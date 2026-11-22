"""Verification for Theorem 1 (exponentially long equilibrium path) in findings.md.

(a) exact check of every numeric inequality used in the proof, for n = 1..NMAX_PARAMS;
(b) strong connectivity of the circulation network (used in the cut argument);
(c) exact rational verification of the 2^n partial-budget equilibria for n = 1..NMAX_EXACT,
    including that the forced return flows j+1 are pairwise distinct and budgets monotone;
(d) floating-point MILP sanity check (scipy/HiGHS) for n = 1..NMAX_MILP: at each forced
    budget, maximise and minimise the return-arc attack mass over ALL partial-budget
    equilibria.  Theorem 1 predicts max = min = (j+1)/Kappa.
"""
import sys, time
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from fractions import Fraction as Fr
from game import Gn


def strongly_connected(G):
    circ = G.circ
    adj = {u: [] for u in range(circ.n)}
    radj = {u: [] for u in range(circ.n)}
    for k in range(circ.m):
        adj[circ.tail[k]].append(circ.head[k])
        radj[circ.head[k]].append(circ.tail[k])

    def reach(src, g):
        seen = {src}
        st = [src]
        while st:
            u = st.pop()
            for w in g[u]:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
        return seen
    return len(reach(0, adj)) == circ.n and len(reach(0, radj)) == circ.n


def check_params(G):
    """Every inequality used in the proof of Theorem 1, checked exactly."""
    n, L, eps, K, C, A = G.n, G.L, G.eps, G.K, G.C, G.A
    ok = True
    ok &= (C < Fr(2 ** (n - 1)))                         # non-special value gaps <= C
    ok &= (eps * L <= Fr(1, 2))                          # step (2)
    ok &= (eps * L * 2 ** (n + 1) <= Fr(1, 8))           # |mu - mu_c| <= 1/8 in the window
    bound_P = Fr(2 ** n) / eps + L * (2 ** n + Fr(1, 8))  # |P_u| bound, step (4)
    ok &= (bound_P < K / 2)                              # interiority
    # disallowed pairs never best responses: allowed utilities >= -C - |A| - (1+eps)K/2 > -M
    ok &= (-G.M < -C - abs(A) - (1 + eps) * K)
    return ok


def milp_extremes(G, budget, special_target):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    mT, nT = len(G.p), len(G.d)
    allowed = sorted(G.val.keys())
    E = len(allowed)
    # variable layout: x[0:nT], F[E], v[mT], lam, z[E] (bin), al[nT] (bin), be[nT] (bin)
    ix = lambda u: u
    iF = lambda e: nT + e
    iv = lambda k: nT + E + k
    ilam = nT + E + mT
    iz = lambda e: nT + E + mT + 1 + e
    ial = lambda u: nT + 2 * E + mT + 1 + u
    ibe = lambda u: nT + 2 * E + mT + 1 + nT + u
    N = nT + 2 * E + mT + 1 + 2 * nT
    a = [[float(v) for v in row] for row in G.a]
    b = [[float(v) for v in row] for row in G.b]
    p = [float(v) for v in G.p]
    d = [float(v) for v in G.d]
    Kf = float(G.K)
    BM = 4 * Kf + 10.0
    QM = max(d) + 1.0
    rows, lo, hi = [], [], []

    def add(coeffs, l, h):
        r = np.zeros(N)
        for i, c in coeffs:
            r[i] += c
        rows.append(r); lo.append(l); hi.append(h)
    # sum x = budget
    add([(ix(u), 1.0) for u in range(nT)], float(budget), float(budget))
    # row sums
    for k in range(mT):
        add([(iF(e), 1.0) for e, (kk, u) in enumerate(allowed) if kk == k], p[k], p[k])
    for e, (k, u) in enumerate(allowed):
        # F <= p z
        add([(iF(e), 1.0), (iz(e), -p[k])], -np.inf, 0.0)
        # v_k >= a - b x_u   ->  v_k + b x_u >= a
        add([(iv(k), 1.0), (ix(u), b[k][u])], a[k][u], np.inf)
        # v_k <= a - b x_u + BM(1-z) -> v_k + b x_u + BM z <= a + BM
        add([(iv(k), 1.0), (ix(u), b[k][u]), (iz(e), BM)], -np.inf, a[k][u] + BM)
    for u in range(nT):
        qcoef = [(iF(e), d[u]) for e, (k, uu) in enumerate(allowed) if uu == u]
        # x_u <= al_u ; q_u >= lam - QM(1-al)  ->  q - lam - QM al >= -QM
        add([(ix(u), 1.0), (ial(u), -1.0)], -np.inf, 0.0)
        add(qcoef + [(ilam, -1.0), (ial(u), -QM)], -QM, np.inf)
        # x_u >= 1 - be_u ; q_u <= lam + QM(1-be) -> q - lam + QM be <= QM
        add([(ix(u), 1.0), (ibe(u), 1.0)], 1.0, np.inf)
        add(qcoef + [(ilam, -1.0), (ibe(u), QM)], -np.inf, QM)
    A_ = np.array(rows)
    cons = LinearConstraint(A_, np.array(lo), np.array(hi))
    lb = np.zeros(N); ub = np.ones(N)
    for e in range(E):
        lb[iF(e)] = 0.0; ub[iF(e)] = 1.0
    for k in range(mT):
        lb[iv(k)] = -1e9; ub[iv(k)] = 1e9
    lb[ilam] = 0.0; ub[ilam] = QM
    integrality = np.zeros(N)
    for e in range(E):
        integrality[iz(e)] = 1
    for u in range(nT):
        integrality[ial(u)] = 1; integrality[ibe(u)] = 1
    e_star = allowed.index((G.rho, special_target))
    out = []
    for sign in (+1.0, -1.0):
        c = np.zeros(N); c[iF(e_star)] = -sign  # maximise sign * F
        res = milp(c, constraints=cons, bounds=Bounds(lb, ub), integrality=integrality,
                   options={"mip_rel_gap": 0, "primal_feasibility_tolerance": 1e-9,
                            "time_limit": 600})
        out.append(None if res.x is None else res.x[iF(e_star)])
    return out[0], out[1]


if __name__ == "__main__":
    NMAX_PARAMS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    NMAX_EXACT = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    NMAX_MILP = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    print("(a,b) proof inequalities and strong connectivity:")
    allp = True
    for n in range(1, NMAX_PARAMS + 1):
        G = Gn(n)
        okp = check_params(G) and strongly_connected(G)
        allp &= okp
    print(f"   n=1..{NMAX_PARAMS}: all inequalities hold exactly and network strongly connected: {allp}")
    allok = allp  # artifact: exit status
    print("(c) exact equilibria at the forced budgets:")
    for n in range(1, NMAX_EXACT + 1):
        t0 = time.time()
        G = Gn(n)
        budgets, flows, ok_all = [], [], True
        for j in range(2 ** n):
            x, F, lam, budget, f = G.game_equilibrium_from_tu(Fr(2 * j + 1, 2))
            ok, msg = G.check(x, F, lam, budget)
            ok_all &= ok and f[G.rho] == j + 1 and all(0 < xu < 1 for xu in x)
            # the proof's window quantity |mu - mu_c(budget)| must be < 1/8
            T = G.K * (budget - Fr(G.V, 2))
            mu_c = G.A - G.eps * T / G.V
            ok_all &= abs(Fr(2 * j + 1, 2) - mu_c) < Fr(1, 8)
            budgets.append(budget)
        mono = all(budgets[i] > budgets[i + 1] for i in range(len(budgets) - 1))
        allok &= ok_all and mono  # artifact: exit status
        print(f"   n={n}: {2**n} equilibria exact-verified={ok_all}, budgets strictly monotone={mono}, "
              f"budget range [{float(budgets[-1]):.6f}, {float(budgets[0]):.6f}] (r={G.r}), {time.time()-t0:.2f}s")
    print("(d) MILP sanity check (floating point) over ALL equilibria at the forced budgets:")
    for n in range(1, NMAX_MILP + 1):
        G = Gn(n)
        worst = 0.0
        t0 = time.time()
        for j in range(2 ** n):
            x, F, lam, budget, f = G.game_equilibrium_from_tu(Fr(2 * j + 1, 2))
            mx, mn = milp_extremes(G, budget, G.s_n)
            target = (j + 1) / G.Kap
            if mx is None or mn is None:
                print(f"   n={n} j={j}: MILP failed"); worst = float('inf'); continue
            worst = max(worst, abs(mx - target), abs(mn - target))
        print(f"   n={n}: max |extreme return mass - (j+1)/Kappa| over j = {worst:.2e}  ({time.time()-t0:.1f}s)")
        allok &= worst <= 1e-6  # artifact: exit status (floating-point MILP; tolerance 1e-6, MILP failure = inf)
    sys.exit(0 if allok else 1)  # artifact: exit status
