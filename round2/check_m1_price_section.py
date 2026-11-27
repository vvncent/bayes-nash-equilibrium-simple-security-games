"""Check exact price sections and price-only finite-precision recovery.

Run python3 -B round2/check_m1_price_section.py with z3-solver installed.
"""

from fractions import Fraction as Q
from itertools import combinations
from math import gcd
from random import Random

import z3

from check_m1_support_reconstruction import Market, cases, rational, read, verify


def add_form(left, right, sign=1):
    return tuple(a + sign*b for a, b in zip(left, right))


def shifted(form, threshold):
    return (form[0] - threshold,) + form[1:]


def solve_square(forms):
    """Rows are affine functions required to vanish."""
    n = len(forms)
    rows = [list(map(Q, f[1:] + (-f[0],))) for f in forms]
    for j in range(n):
        pivot = next((k for k in range(j, n) if rows[k][j]), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = rows[j][j]
        rows[j] = [a/scale for a in rows[j]]
        for k in range(n):
            if k != j and rows[k][j]:
                scale = rows[k][j]
                rows[k] = [a - scale*b for a, b in zip(rows[k], rows[j])]
    return tuple(row[-1] for row in rows)


def bounds(market):
    offers = [(Q(a), Q(b)) for a, b in market.offers.values()]
    B = max([Q(1)] + [b for _, b in offers])
    P = 1 + max([Q(0)] + [a/b for a, b in offers])
    U = 1 + max([Q(0)] + [a for a, _ in offers])
    K = 1
    for row in ([(Q(1), P), (Q(1), U)] +
                [(Q(1), b, Q(-1), a) for a, b in offers]):
        denominator = 1
        for x in row:
            denominator = denominator*x.denominator // gcd(denominator, x.denominator)
        K = max(K, *(abs(x*denominator).numerator for x in row))
    dimension = 1 + len(market.masses) + len(market.capacities)
    return B, P, U, (dimension*K)**dimension


def symbolic_section(market, chart, box):
    """Independent literal complementarity test directly in the section."""
    n, m = len(market.masses), len(market.capacities)
    y = z3.Reals(" ".join(f"sec_y_{h}" for h in range(len(box)))) if box else []
    p = [z3.Real(f"sec_p_{j}") for j in range(m)]
    u = [z3.Real(f"sec_u_{i}") for i in range(n)]
    f = {e: z3.Real(f"sec_f_{e[0]}_{e[1]}") for e in market.offers}
    s = z3.SolverFor("QF_LRA")
    s.add(*(var >= 0 for var in u+p+list(f.values())))
    for (low, high), var in zip(box, y):
        s.add(var >= low, var <= high)
    for form, var in zip(chart, p):
        s.add(var == form[0] + sum(a*b for a, b in zip(form[1:], y)))
    for (i,j), (a,b) in market.offers.items():
        gap = u[i] + b*p[j] - a
        s.add(gap >= 0, z3.Or(f[i,j] == 0, gap == 0))
    for i, mu in enumerate(market.masses):
        load = sum((x for (ii,_), x in f.items() if ii == i), z3.RealVal(0))
        s.add(load <= mu, z3.Or(u[i] == 0, load == mu))
    for j, cap in enumerate(market.capacities):
        load = sum((x for (_,jj), x in f.items() if jj == j), z3.RealVal(0))
        s.add(load <= cap, z3.Or(p[j] == 0, load == cap))
    status = s.check()
    assert status in (z3.sat, z3.unsat)
    return status == z3.sat


def repair(market, trial, eta):
    B, P, U, den = bounds(market)
    assert 2*B*eta < Q(1, den)
    n, m = len(market.masses), len(market.capacities)
    offer = {(i,j): a - b*trial[j] for (i,j), (a,b) in market.offers.items()}
    best = [max([Q(0)] + [v for (k,_), v in offer.items() if k == i]) for i in range(n)]
    S = {e for e, value in offer.items() if best[e[0]] - value <= 2*B*eta}
    f = {e: z3.Real(f"rel_flow_{e[0]}_{e[1]}") for e in S}
    s = z3.SolverFor("QF_LRA")
    s.add(*(x >= 0 for x in f.values()))
    for i, mu in enumerate(market.masses):
        load = sum((x for (ii,_), x in f.items() if ii == i), z3.RealVal(0))
        s.add(load <= mu)
        if best[i] > B*eta:
            s.add(load == mu)
    for j, cap in enumerate(market.capacities):
        load = sum((x for (_,jj), x in f.items() if jj == j), z3.RealVal(0))
        s.add(load <= cap)
        if trial[j] > eta:
            s.add(load == cap)
    res = s.check()
    if res == z3.unsat:
        return None
    assert res == z3.sat
    flow = {e: rational(s.model().eval(x, model_completion=True)) for e, x in f.items()}
    if not eta:
        sol = tuple(best), tuple(trial), flow
        verify(market, S, sol)
        return sol
    p = [z3.Real(f"fix_p_{j}") for j in range(m)]
    u = [z3.Real(f"fix_u_{i}") for i in range(n)]
    pay = z3.SolverFor("QF_LRA")
    pay.add(*(x >= 0 for x in p+u), *(x <= P for x in p), *(x <= U for x in u))
    for (i,j), (a,b) in market.offers.items():
        gap = u[i] + b*p[j] - a
        pay.add(gap >= 0)
        if (i,j) in S:
            pay.add(gap == 0)
    pay.add(*(p[j] == 0 for j in range(m) if trial[j] <= eta))
    pay.add(*(u[i] == 0 for i in range(n) if best[i] <= B*eta))
    assert pay.check() == z3.sat
    model = pay.model()
    sol = read(model,u), read(model,p), flow
    verify(market, S, sol)
    return sol


def search(market, chart, box, eta=Q(0)):
    B, P, _, _ = bounds(market)
    k = len(box)
    zero = (Q(0),)*(k+1)
    chart = [tuple(map(Q, form)) for form in chart]
    faces = set()
    for d, pair in enumerate(box):
        coord = (Q(0),) + tuple(Q(int(i == d)) for i in range(k))
        faces.update(shifted(coord, x) for x in pair)
    for form in chart:
        faces.add(form)
        faces.add(shifted(form,P))
        faces.add(shifted(form,eta))
    for i in range(len(market.masses)):
        options = [zero]
        for (buyer,j), (a,b) in market.offers.items():
            if i == buyer:
                form = tuple(-b*z for z in chart[j])
                options.append((a + form[0],) + form[1:])
        for f in options:
            faces.add(shifted(f, B*eta))
            for g in options:
                faces.add(shifted(add_form(f,g,-1), 2*B*eta))
    faces = sorted(form for form in faces if any(form[1:]))
    seen = set()
    for subset in combinations(faces,k):
        y = solve_square(subset)
        if y is None or y in seen:
            continue
        seen.add(y)
        if any(not lo <= v <= hi for (lo,hi),v in zip(box,y)):
            continue
        prices = tuple(f[0] + sum(a*b for a,b in zip(f[1:],y)) for f in chart)
        if any(v < 0 or v > P for v in prices):
            continue
        sol = repair(market, prices, eta)
        if sol is not None:
            return sol
    return None


def exact_tests():
    rng = Random(40877)
    total = yes = no = 0
    for market in cases():
        m = len(market.capacities)
        _, high, _, _ = bounds(market)
        for step in range(24):
            k = step % (m+1)
            if k == m:
                chart = [(Q(0),) + tuple(Q(int(j == i)) for i in range(k)) for j in range(m)]
                box = [(Q(0), high) for _ in range(k)]
            else:
                chart = [tuple([Q(rng.randrange(-1,5),3)] +
                               [Q(rng.randrange(-3,4),2) for _ in range(k)]) for j in range(m)]
                if k == 1 and not any(form[1] for form in chart):
                    chart[0] = (chart[0][0], Q(1))
                box = [(Q(-1), Q(2)) for _ in range(k)]
            results = search(market, chart, box)
            expect = symbolic_section(market, chart, box)
            assert (results is not None) == expect
            total += 1
            yes += expect
            no += not expect
    return total, yes, no


def approximate_tests():
    count = shifted = 0
    for market in cases() + [Market((2,2), (1,1), {(0,0):(1,3), (1,1):(1,5)})]:
        B, high, _, den = bounds(market)
        m = len(market.capacities)
        identity = [(Q(0),) + tuple(Q(j == h) for h in range(m)) for j in range(m)]
        eq = search(market, identity, [(0, high)]*m)
        assert eq is not None
        pstar = eq[1]
        eta = 1/(8*B*den)
        for choices in range(1 << m):
            q = tuple(max(Q(0), min(high, p + (eta if choices >> i & 1 else -eta)))
                      for i,p in enumerate(pstar))
            point_chart = [(p,) for p in q]
            sol = search(market, point_chart, [], eta)
            assert sol is not None
            shifted += not symbolic_section(market, point_chart, [])
            count += 1
        if m == 2:
            q = [min(high, p + eta/2) for p in pstar]
            line = [(q[0], Q(1)), (q[1], Q(-1))]
            assert search(market, line, [(-eta/8, eta/8)], eta) is not None
            shifted += not symbolic_section(market, line, [(-eta/8, eta/8)])
            count += 1
    return count, shifted


def security_snapshots():
    """Recover from near coverage with ties, flat offers, zero gains and both extreme budgets."""
    from check_security_support_reconstruction import Game, symbols

    instances = (
        ((1,), (1,1), ((1,1),), ((2,1),), 1),
        ((Q(1,3),Q(2,3)), (1,1), ((1,1),(1,1)), ((0,0),(1,1)), 1),
        ((1,), (0,0), ((1,1),), ((0,1),), 1),
        ((Q(1,2),Q(1,2)), (0,2,1), ((2,1,1),(1,1,1)), ((0,1,1),(0,0,0)), 1),
        ((1,), (1,3,0), ((1,1,1),), ((1,2,0),), 0),
        ((1,), (1,3,0), ((1,1,1),), ((1,2,0),), 3),
    )
    count = misses = 0
    for masses, gains, a, b, r in instances:
        n, m = len(masses), len(gains)
        game = Game(tuple(map(Q,masses)), tuple(map(Q,gains)),
                    {(i,j):(Q(a[i][j]),Q(b[i][j])) for i in range(n) for j in range(m)}, r)
        x,u,f,lam = symbols(game)
        all_variables = list(x)+list(u)+list(f.values())+[lam]
        direct = z3.SolverFor("QF_LRA")
        direct.add(*(v >= 0 for v in f.values()), z3.Sum(x)==r)
        direct.add(*(z3.And(v>=0, v<=1) for v in x))
        for i in range(n):
            direct.add(z3.Sum([f[i,j] for j in range(m)]) == masses[i])
        for (i,j), (intercept,slope) in game.offers.items():
            gap = u[i]+slope*x[j]-intercept
            direct.add(gap>=0, z3.Or(f[i,j]==0,gap==0))
        score = [gains[j]*z3.Sum([f[i,j] for i in range(n)]) for j in range(m)]
        for j in range(m):
            direct.add(z3.Or(x[j]==0, score[j]>=lam), z3.Or(x[j]==1, score[j]<=lam))
        assert direct.check()==z3.sat
        center = read(direct.model(), x)
        D = n+m+1
        K = max(2, r, max(abs(a)+b for a,b in game.offers.values())+1)
        B = max([Q(1)]+[bb for _,bb in game.offers.values()])
        eta = Q(1,8)/(B*(D*K)**D)
        trials = {center}
        for j in range(m):
            for k in range(m):
                if j!=k and center[j]>=eta and center[k]<=1-eta:
                    trial=list(center)
                    trial[j]-=eta
                    trial[k]+=eta
                    trials.add(tuple(trial))
        for trial in trials:
            payoffs = {(i,j): aa-bb*trial[j] for (i,j),(aa,bb) in game.offers.items()}
            v = [max(payoffs[i,j] for j in range(m)) for i in range(n)]
            S = {(i,j) for (i,j),pay in payoffs.items() if v[i]-pay<=2*B*eta}
            flow_solver = z3.SolverFor("QF_LRA")
            flow_solver.add(*(amount>=0 for amount in f.values()))
            flow_solver.add(*(f[e]==0 for e in f if e not in S))
            for i in range(n):
                flow_solver.add(z3.Sum([f[i,j] for j in range(m)])==masses[i])
            for j in range(m):
                if trial[j]>eta:
                    flow_solver.add(score[j]>=lam)
                if trial[j]<1-eta:
                    flow_solver.add(score[j]<=lam)
            assert flow_solver.check()==z3.sat
            price_solver = z3.SolverFor("QF_LRA")
            price_solver.add(z3.Sum(x)==r, *(z3.And(t>=0,t<=1) for t in x))
            for j in range(m):
                if trial[j]<=eta:
                    price_solver.add(x[j]==0)
                if trial[j]>=1-eta:
                    price_solver.add(x[j]==1)
            for (i,j),(aa,bb) in game.offers.items():
                price_solver.add(u[i]+bb*x[j]>=aa)
                if (i,j) in S:
                    price_solver.add(u[i]+bb*x[j]==aa)
            assert price_solver.check()==z3.sat
            merged = (read(price_solver.model(),list(x)+list(u)) +
                      read(flow_solver.model(),list(f.values())+[lam]))
            direct.push()
            direct.add(*(var==value for var,value in zip(all_variables,merged)))
            assert direct.check()==z3.sat
            direct.pop()
            direct.push()
            direct.add(*(x[j]==trial[j] for j in range(m)))
            misses+=direct.check()==z3.unsat
            direct.pop()
            count+=1
    return count, misses


if __name__ == "__main__":
    total, yes, no = exact_tests()
    count, misses = approximate_tests()
    print(f"{total} exact scoped tests matched literal M1 feasibility ({yes} feasible, {no} infeasible).")
    print(f"{count} nearby snapshots/lines recovered exact equilibria; "
          f"{misses} supplied sections contained no equilibrium price.")
    tested, nonsolutions = security_snapshots()
    print(f"{tested} security coverage snapshots recovered exact equilibria, "
          f"including {nonsolutions} coverages that were not exact equilibria.")
