"""matching.typ §§4-5: cutoff bisection with pattern intervals, pinned narrowing with canonicalization,
exact budget repair. Every intermediate claim is asserted exactly."""
from fractions import Fraction as Fr
from math import ceil, log2
import z3
from core import (R, val, Game, loads, check_box, check_bne, box_query, row_int_bound, bits, meet,
                  join, br_flow, best_response_ok)


def labels01(x):
    return ["zero" if v == 0 else ("one" if v == 1 else "free") for v in x]


# ------------------------------------------------------------------ §4 precision Q1
def Q1_of(G):
    m, n = G.m, G.n
    N1 = n + m * n + 1
    D = 1 + max(G.d)
    rows = []
    unit = lambda k: [Fr(1) if t == k else Fr(0) for t in range(N1)]
    xi = lambda j: j
    fi = lambda i, j: n + i * n + j
    li = N1 - 1
    for k in range(N1):
        rows.append((unit(k), Fr(0)))
        rows.append((unit(k), Fr(1)))
    rows.append((unit(li), D))
    for i in range(m):
        co = [Fr(0)] * N1
        for j in range(n):
            co[fi(i, j)] = Fr(1)
        rows.append((co, G.p[i]))
        for j in range(n):
            for k in range(n):
                if j != k:
                    co = [Fr(0)] * N1
                    co[xi(j)] = -G.b[i][j]
                    co[xi(k)] = G.b[i][k]
                    rows.append((co, G.a[i][k] - G.a[i][j]))
    for j in range(n):
        co = [Fr(0)] * N1
        for i in range(m):
            co[fi(i, j)] = G.d[j]
        co[li] = Fr(-1)
        rows.append((co, Fr(0)))
    rows.append(([Fr(1)] * n + [Fr(0)] * (N1 - n), Fr(G.r)))
    H1 = row_int_bound(rows)
    return (N1 * H1) ** N1, N1, H1


def pattern_poly(G, x, f, side):
    """Constraint builder for the §4 pattern polytope in (x, f, lambda)."""
    m, n = G.m, G.n
    A = [[f[i][j] > 0 for j in range(n)] for i in range(m)]
    lab = labels01(x)

    def build(s, V):
        X, F, lam = V
        s.add(lam >= 0, lam <= R(1 + max(G.d)))
        for j in range(n):
            s.add(X[j] >= 0, X[j] <= 1)
        for i in range(m):
            s.add(z3.Sum(F[i]) == R(G.p[i]))
            for j in range(n):
                s.add(F[i][j] >= 0, F[i][j] <= 1)
                if not A[i][j]:
                    s.add(F[i][j] == 0)
                else:
                    for k in range(n):
                        s.add(R(G.a[i][j]) - R(G.b[i][j]) * X[j] >= R(G.a[i][k]) - R(G.b[i][k]) * X[k])
        for j in range(n):
            sc = R(G.d[j]) * z3.Sum([F[i][j] for i in range(m)])
            if lab[j] == "zero":
                s.add(X[j] == 0, sc <= lam)
            elif lab[j] == "one":
                s.add(X[j] == 1, sc >= lam)
            else:
                s.add(sc == lam)
        tot = z3.Sum(X)
        s.add(tot >= G.r if side == "L" else tot <= G.r)

    def mk():
        X = [z3.Real(f"x{j}") for j in range(n)]
        F = [[z3.Real(f"f{i}_{j}") for j in range(n)] for i in range(m)]
        return X, F, z3.Real("lam")

    return build, mk


def lam_interval(G, x, f, side):
    build, mk = pattern_poly(G, x, f, side)
    out = []
    for sense in ("min", "max"):
        s = z3.Optimize()
        V = mk()
        build(s, V)
        (s.minimize if sense == "min" else s.maximize)(V[2])
        assert s.check() == z3.sat
        out.append(val(s.model(), V[2]))
    return out


def witness_at(G, x, f, side, lam0):
    build, mk = pattern_poly(G, x, f, side)
    s = z3.Optimize()
    s.set(priority="lex")
    V = mk()
    build(s, V)
    s.add(V[2] == R(lam0))
    for e in V[0] + [q for row in V[1] for q in row]:
        s.minimize(e)
    assert s.check() == z3.sat
    mod = s.model()
    return [val(mod, e) for e in V[0]], [[val(mod, e) for e in row] for row in V[1]]


def locate_cutoff(G, oracle, stats):
    n = G.n
    D = 1 + max(G.d)
    Q1, N1, H1 = Q1_of(G)
    stats["Q1_bits"] = Q1.bit_length()
    lamL, eqL = Fr(0), ([Fr(1)] * n, br_flow(G, [Fr(1)] * n))
    lamH, eqH = D, ([Fr(0)] * n, br_flow(G, [Fr(0)] * n))
    assert check_box(G, [lamL / dj for dj in G.d], [0] * n, [1] * n, *eqL)[0]
    assert check_box(G, [lamH / dj for dj in G.d], [0] * n, [1] * n, *eqH)[0]
    steps = 0
    gap = Fr(1, Q1 * Q1)
    while lamH - lamL >= gap:
        mid = (lamL + lamH) / 2
        c = [mid / dj for dj in G.d]
        x, f = box_query(G, c, [Fr(0)] * n, [Fr(1)] * n, oracle)
        steps += 1
        tot = sum(x)
        if tot == G.r:
            stats["bisect_steps"] = steps
            return ("done", (x, f, mid))
        if tot > G.r:
            lamL, eqL = mid, (x, f)
        else:
            lamH, eqH = mid, (x, f)
    stats["bisect_steps"] = steps
    X = D * Q1 * Q1
    k = max(0, (X.numerator // X.denominator).bit_length() - 1)
    while Fr(2) ** k < X:
        k += 1
    stats["bisect_bound"] = 1 + k  # 1 + ceil(log2(D Q1^2)), exact
    assert steps <= stats["bisect_bound"]
    IL = lam_interval(G, *eqL, "L")
    IH = lam_interval(G, *eqH, "H")
    assert IL[0] <= lamL <= IL[1] and IH[0] <= lamH <= IH[1]
    assert max(IL[0], IH[0]) <= min(IL[1], IH[1]), "pattern intervals disjoint"
    for e1 in IL + IH:
        assert e1.denominator <= Q1
    lam0 = max(IL[0], IH[0])
    X, FX = witness_at(G, *eqL, "L", lam0)
    Y, FY = witness_at(G, *eqH, "H", lam0)
    c0 = [lam0 / dj for dj in G.d]
    one, zero = [Fr(1)] * n, [Fr(0)] * n
    assert check_box(G, c0, zero, one, X, FX)[0] and sum(X) >= G.r
    assert check_box(G, c0, zero, one, Y, FY)[0] and sum(Y) <= G.r
    L, fL = meet(G, X, FX, Y, FY)
    H, fH = join(G, X, FX, Y, FY)
    assert check_box(G, c0, zero, one, L, fL)[0], "meet not an equilibrium"
    assert check_box(G, c0, zero, one, H, fH)[0], "join not an equilibrium"
    assert sum(L) <= G.r <= sum(H) and all(L[j] <= H[j] for j in range(n))
    stats["lam0"] = lam0
    return ("bracket", (lam0, L, fL, H, fH))


# ------------------------------------------------------------------ §5 precision Q2
def Q2_of(G):
    m, n = G.m, G.n
    N2 = n + 1
    rows = []
    unit = lambda k: [Fr(1) if t == k else Fr(0) for t in range(N2)]
    for k in range(N2):
        rows.append((unit(k), Fr(0)))
        rows.append((unit(k), Fr(1)))
    rows.append((unit(n), Fr(n)))
    for i in range(m):
        for j in range(n):
            for k in range(n):
                if j != k:
                    co = [Fr(0)] * N2
                    co[j] = -G.b[i][j]
                    co[k] = G.b[i][k]
                    rows.append((co, G.a[i][k] - G.a[i][j]))
    rows.append(([Fr(1)] * n + [Fr(-1)], Fr(G.r)))
    rows.append(([Fr(1)] * n + [Fr(1)], Fr(G.r)))
    H2 = row_int_bound(rows)
    return (N2 * H2) ** N2


def canonicalize(G, c, l, h, x, f):
    """§5 'Controlling adaptive endpoint lengths'."""
    m, n = G.m, G.n
    A = [[f[i][j] > 0 for j in range(n)] for i in range(m)]
    st = []
    for j in range(n):
        if l[j] == h[j]:
            st.append("pin")
        elif x[j] == l[j]:
            st.append("lo")
        elif x[j] == h[j]:
            st.append("hi")
        else:
            st.append("free")
    s = z3.Optimize()
    s.set(priority="lex")
    X = [z3.Real(f"x{j}") for j in range(n)]
    for j in range(n):
        if st[j] in ("pin", "lo"):
            s.add(X[j] == R(l[j]))
        elif st[j] == "hi":
            s.add(X[j] == R(h[j]))
        else:
            s.add(X[j] >= R(l[j]), X[j] <= R(h[j]))
    for i in range(m):
        for j in range(n):
            if A[i][j]:
                for k in range(n):
                    s.add(R(G.a[i][j]) - R(G.b[i][j]) * X[j] >= R(G.a[i][k]) - R(G.b[i][k]) * X[k])
    for e in X:
        s.minimize(e)
    assert s.check() == z3.sat
    mod = s.model()
    xv = [val(mod, e) for e in X]
    s = z3.Optimize()
    s.set(priority="lex")
    F = [[z3.Real(f"f{i}_{j}") for j in range(n)] for i in range(m)]
    for i in range(m):
        s.add(z3.Sum(F[i]) == R(G.p[i]))
        for j in range(n):
            s.add(F[i][j] >= 0)
            if not A[i][j]:
                s.add(F[i][j] == 0)
    for j in range(n):
        cs = z3.Sum([F[i][j] for i in range(m)])
        if st[j] == "lo":
            s.add(cs <= R(c[j]))
        elif st[j] == "hi":
            s.add(cs >= R(c[j]))
        elif st[j] == "free":
            s.add(cs == R(c[j]))
    for row in F:
        for e in row:
            s.minimize(e)
    assert s.check() == z3.sat
    mod = s.model()
    fv = [[val(mod, e) for e in row] for row in F]
    ok, why = check_box(G, c, l, h, xv, fv)
    assert ok, "canonical point fails the pinned subbox: " + why
    return xv, fv


def pin_recover(G, c, L, fL, H, fH, k, x, f):
    """§3 pinning lemma: patch the box flow with an endpoint flow."""
    n = G.n
    w = loads(G, f)
    if w[k] >= c[k]:
        S = [x[j] > L[j] for j in range(n)]
        base = fL
    else:
        S = [x[j] < H[j] for j in range(n)]
        base = fH
    F = [[f[i][j] if S[j] else base[i][j] for j in range(n)] for i in range(G.m)]
    return F


def narrow_and_repair(G, oracle, lam0, L, fL, H, fH, stats, canon=True):
    n = G.n
    c = [lam0 / dj for dj in G.d]
    one, zero = [Fr(1)] * n, [Fr(0)] * n
    Q2 = Q2_of(G)
    eta = Fr(1, 4 * n * Q2)
    sp = Fr(1)
    while sp > eta / 4:
        sp /= 2
    stats["eta_bits"] = (1 / eta).numerator.bit_length()
    calls = 0
    maxbits = []
    while any(H[j] - L[j] > eta for j in range(n)):
        for k in range(n):
            wdt = H[k] - L[k]
            if wdt <= eta:
                continue
            lo3, hi3 = L[k] + wdt / 3, H[k] - wdt / 3
            t = Fr(ceil(lo3 / sp)) * sp
            assert lo3 <= t <= hi3
            l = L[:]
            h = H[:]
            l[k] = h[k] = t
            if lam0 == 0:
                x = h[:]
                f = br_flow(G, x)
            else:
                x, f = box_query(G, c, l, h, oracle)
            calls += 1
            ok, why = check_box(G, c, l, h, x, f)
            assert ok, why
            if canon:
                x, f = canonicalize(G, c, l, h, x, f)
            F = pin_recover(G, c, L, fL, H, fH, k, x, f)
            ok, why = check_box(G, c, zero, one, x, F)
            assert ok, "pinning lemma failed: " + why
            assert all(L[j] <= x[j] <= H[j] for j in range(n)) and x[k] == t
            tot = sum(x)
            if tot == G.r:
                stats["narrow_calls"] = calls
                stats["maxbits"] = maxbits
                stats["exit"] = "hit"
                return x, F
            if tot < G.r:
                L, fL = x, F
            else:
                H, fH = x, F
            assert sum(L) <= G.r <= sum(H)
            assert H[k] - L[k] <= Fr(2, 3) * wdt
            maxbits.append(max(bits(q) for q in L + H))
    stats["narrow_calls"] = calls
    stats["maxbits"] = maxbits
    # budget repair at endpoint L
    xe, fe = L, fL
    assert abs(sum(xe) - G.r) < Fr(1, Q2)
    A = [[fe[i][j] > 0 for j in range(n)] for i in range(G.m)]
    lab = labels01(xe)
    s = z3.Optimize()
    X = [z3.Real(f"x{j}") for j in range(n)]
    sv = z3.Real("s")
    s.add(sv >= 0, sv <= n)
    for j in range(n):
        if lab[j] == "zero":
            s.add(X[j] == 0)
        elif lab[j] == "one":
            s.add(X[j] == 1)
        else:
            s.add(X[j] >= 0, X[j] <= 1)
    for i in range(G.m):
        for j in range(n):
            if A[i][j]:
                for k in range(n):
                    s.add(R(G.a[i][j]) - R(G.b[i][j]) * X[j] >= R(G.a[i][k]) - R(G.b[i][k]) * X[k])
    s.add(z3.Sum(X) - G.r <= sv, G.r - z3.Sum(X) <= sv)
    s.minimize(sv)
    assert s.check() == z3.sat
    mod = s.model()
    sstar = val(mod, sv)
    assert sstar == 0, f"price LP optimum positive: {sstar}"
    xr = [val(mod, e) for e in X]
    stats["exit"] = "repair"
    return xr, fe


def solve_game(G, oracle, canon=True):
    stats = {}
    kind, data = locate_cutoff(G, oracle, stats)
    if kind == "done":
        x, f, lam = data
        stats["exit"] = "bisection-hit"
        return x, f, stats
    lam0, L, fL, H, fH = data
    x, f = narrow_and_repair(G, oracle, lam0, L, fL, H, fH, stats, canon)
    return x, f, stats
