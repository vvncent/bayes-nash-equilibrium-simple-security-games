"""Exact checks for the one-query half-quota reduction using real linear arithmetic."""
from fractions import Fraction as F
from random import Random
from itertools import combinations

import z3


def exact(value):
    f = F(value)
    return z3.Q(f.numerator, f.denominator)


def frac(model, expression):
    return model.eval(expression, model_completion=True).as_fraction()


def impose_source(solver, f, u, price, masses, caps, a, rate):
    for i, p in enumerate(masses):
        row = sum(f[i])
        solver.add(u[i] >= 0, row <= exact(p), z3.Or(u[i] == 0, row == exact(p)))
        for j in range(len(caps)):
            slack = u[i] + rate[i][j] * price[j] - exact(a[i][j])
            solver.add(slack >= 0, f[i][j] >= 0, z3.Or(f[i][j] == 0, slack == 0))
    for j, c in enumerate(caps):
        load = sum(row[j] for row in f)
        solver.add(price[j] >= 0, load <= exact(c), z3.Or(price[j] == 0, load == exact(c)))


def check_case(a, B, E, raw, caps, canonical):
    m, n = len(raw), len(caps)
    from math import lcm
    D = lcm(*(F(v).denominator for v in list(raw) + list(caps)))
    if canonical:
        masses = [4*m*D*F(v) + 2 for v in raw]
        caps = [4*m*D*F(v) for v in caps]
        extra = 1
    else:
        masses = list(map(F, raw))
        extra = 0
    p, c = sum(masses), sum(caps)
    source_b = sum((masses[i] for i in B), F(0))
    K = 1 + p + c
    T = K
    target = K + (source_b + extra)/2
    margins = masses + [c+T, 8*K, 2*K+extra]
    capacity = list(caps) + [p+T+5*K+extra, 5*K]
    if canonical:
        assert target.denominator == 2
        cuts = lambda seq: {sum(sub) for k in range(1,len(seq)) for sub in combinations(seq,k)}
        assert cuts(margins).isdisjoint(cuts(capacity))
    row_count, col_count = len(margins), len(capacity)
    A = [[F(-1)]*col_count for _ in margins]
    for i in range(m):
        A[i][:n] = a[i][:]
        A[i][n] = 0
    A[m][:n+1] = [0]*(n+1)
    for i in (m+1, m+2):
        A[i][n:] = [0, 0]
    slope = [[1+int(i in (B|{m+2}) and j in (E|{n+1})) for j in range(col_count)] for i in range(row_count)]
    u = z3.Reals(' '.join(f'u{i}' for i in range(row_count)))
    price = z3.Reals(' '.join(f'p{j}' for j in range(col_count)))
    f = [z3.Reals(' '.join(f'f{i}x{j}' for j in range(col_count))) for i in range(row_count)]
    s = z3.Solver()
    for i in range(row_count):
        s.add(sum(f[i]) == exact(margins[i]))
        for j in range(col_count):
            sl = u[i] + slope[i][j]*price[j] - exact(A[i][j])
            s.add(f[i][j] >= 0, sl >= 0, z3.Or(f[i][j] == 0, sl == 0))
    for j in range(col_count):
        s.add(sum(row[j] for row in f) == exact(capacity[j]))
    w = sum(f[i][j] for i in B|{m+2} for j in E|{n+1})
    s.add(w == exact(target))
    assert s.check() == z3.sat
    witness = s.model()
    normalized_prices = [frac(witness, v) for v in price]
    assert normalized_prices[n:] == [0,0]
    # Check the strict quota bracket at the connected reference and the full vector.
    for q in (target-K/2, target+K/2):
        solver = z3.Solver()
        solver.add(*list(s.assertions())[:-1], w == exact(q), *(v == exact(val) for v,val in zip(price,normalized_prices)))
        assert solver.check() == z3.sat
    trial = [row[:n] for row in f[:m]]
    real_rate = [row[:n] for row in slope[:m]]
    decoded = z3.Solver()
    impose_source(decoded, trial, u[:m], price[:n], masses, caps, a, real_rate)
    forbidden = [price[n] != 0, price[n+1] != 0, z3.Not(z3.And(*decoded.assertions()))]
    forbidden += [f[i][n+1] > 0 for i in range(m+1)]
    forbidden += [f[i][j] > 0 for i in (m+1,m+2) for j in range(n)]
    s.add(z3.Or(*forbidden))
    assert s.check() == z3.unsat
    if canonical:
        caps = [v/(4*m*D) for v in caps]
    old = z3.Solver()
    impose_source(old, trial, u[:m], price[:n], raw, caps, a, real_rate)
    old.add(*(v == exact(val) for v,val in zip(price[:n],normalized_prices[:n])))
    assert old.check() == z3.sat


def main():
    rng = Random(61503)
    cases = [([[1]], {0},{0},[1],[1]), ([[-1,-3],[0,0]],set(),{0},[1,3],[2,4]),
             ([[4,4],[4,8]],{1},{1},[1,1],[1,1]), ([[F(2**151+1,2**127+5),1],[-1,0]],{0},{0},[F(1,2**193+9),2**80],[1,F(2**75+1,3)])]
    for z in range(25):
        m,n = 1+z%3, 1+(z//3)%3
        a = [[F(rng.randrange(-4,9),rng.choice((1,1,2,7))) for _ in range(n)] for _ in range(m)]
        row = [F(rng.randrange(1,7),rng.choice((1,3))) for _ in range(m)]
        col = [F(rng.randrange(1,7),rng.choice((1,4))) for _ in range(n)]
        cases.append((a,{i for i in range(m) if rng.randrange(2)},{j for j in range(n) if rng.randrange(2)},row,col))
    for case in cases:
        check_case(*case, canonical=True)
    # Connected witness unnecessary in these particular degenerate tests; anchor and all-output decoding still hold.
    for case in cases[:3]:
        check_case(*case, canonical=False)
    print(f'{len(cases)} perturbed and 3 unperturbed dense tables: every half-quota output decodes, strict brackets and original margins feasible; integer no-balance and half-integral quota checked on all 29 compiled inputs.')

if __name__ == '__main__':
    main()
