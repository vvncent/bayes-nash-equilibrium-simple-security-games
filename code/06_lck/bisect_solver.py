"""Polynomial-time exact solver for G_n at a budget s in its window (Proposition 2).

The continuation path of G_n has >= 2^n pieces (Theorem 1), but the instance has a single
non-unit slope.  Its equilibria at budget s are exactly TU optima at a scalar parameter mu
with  T = K(s - |V|/2) in  g(mu) = |V|(A - mu)/eps + [sum_u lo_u(mu), sum_u hi_u(mu)],
where lo/hi are the extreme relative dual prices P'_u - P'_{s_n} over the TU-optimal dual
face.  g is decreasing in mu, so bisection plus rational reconstruction finds a solution
with O(input bits) oracle calls.  Each oracle call is one exact capacity-scaling
min-cost circulation and two Bellman-Ford runs.
"""
import sys, time
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from fractions import Fraction as Fr
from game import Gn
from capscale import min_cost_circulation


def best_rational_in(lo, hi):
    """Fraction with the smallest denominator in the closed interval [lo, hi] (lo <= hi)."""
    lo, hi = Fr(lo), Fr(hi)
    if lo > hi:
        raise ValueError
    fl = lo.numerator // lo.denominator
    if Fr(fl) == lo:
        return lo
    if fl + 1 <= hi:
        return Fr(fl + 1)
    # lo and hi in (fl, fl+1): recurse on reciprocals of fractional parts
    inner = best_rational_in(1 / (hi - fl), 1 / (lo - fl))
    return fl + 1 / inner


class Oracle:
    def __init__(self, G):
        self.G = G
        self.calls = 0

    def g(self, mu):
        """Exact interval g(mu) and the TU data needed to build an equilibrium."""
        G = self.G
        self.calls += 1
        circ = G.circ
        circ.cost[G.rho] = -Fr(mu)
        f, pi, naug = min_cost_circulation(circ.n, circ.tail, circ.head, circ.cap, circ.cost)
        lo, hi = G.relative_price_range(mu, f)
        base = G.V * (G.A - Fr(mu)) / G.eps
        return base + sum(lo), base + sum(hi), f, lo, hi


def solve_budget(G, s, verbose=False):
    """Exact equilibrium of G_n at budget s (s inside the window of Theorem 1)."""
    T = G.K * (Fr(s) - Fr(G.V, 2))
    orc = Oracle(G)
    mu_lo, mu_hi = Fr(0), Fr(2 ** G.n)
    # denominator bound for a crossing point (see findings.md, Prop. 2)
    Q = 2 * (T.denominator) * (G.V * G.eps.denominator + 2 * G.V) * 4
    found = None
    steps = 0
    while found is None:
        steps += 1
        if (mu_hi - mu_lo) < Fr(1, 2 * Q * Q):
            cand = best_rational_in(mu_lo, mu_hi)
            glo, ghi, f, lo, hi = orc.g(cand)
            if glo <= T <= ghi:
                found = (cand, f, lo, hi, glo, ghi)
                break
            raise RuntimeError("rational reconstruction failed")
        mid = (mu_lo + mu_hi) / 2
        glo, ghi, f, lo, hi = orc.g(mid)
        if glo <= T <= ghi:
            found = (mid, f, lo, hi, glo, ghi)
        elif glo > T:
            mu_lo = mid
        else:
            mu_hi = mid
    mu, f, lo, hi, glo, ghi = found
    # pick the convex combination of the extreme duals whose sum hits T exactly
    theta = Fr(0) if ghi == glo else (T - glo) / (ghi - glo)
    rel = [lo[u] + theta * (hi[u] - lo[u]) for u in range(G.V)]   # P'_u - P'_{s_n}
    Psn = (G.A - mu) / G.eps
    P = [Psn + rel[u] for u in range(G.V)]
    x = [Fr(1, 2) + P[u] / G.K for u in range(G.V)]
    circ = G.circ
    F = [[Fr(0)] * G.V for _ in range(circ.m)]
    for k in range(circ.m):
        F[k][circ.head[k]] += Fr(f[k], G.Kap)
        F[k][circ.tail[k]] += Fr(G.kappa[k] - f[k], G.Kap)
    return x, F, Fr(1), mu, orc.calls, steps, f


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [2, 5, 10, 20, 30, 40, 60]
    allok = True  # artifact: exit status
    for n in ns:
        G = Gn(n)
        t0 = time.time()
        x, F, lam, mu, calls, steps, f = solve_budget(G, G.r)
        ok, msg = G.check(x, F, lam, G.r)
        bits = max(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) for v in x)
        print(f"n={n:3d}: path has >= 2^{n} pieces; bisection found exact equilibrium at budget r={G.r}: "
              f"{ok} ({msg}); oracle calls={calls}; mu*={mu}; return flow={f[G.rho]}; "
              f"coverage bits<={bits}; {time.time()-t0:.2f}s")
        # also a budget deep inside the window (forced return flow about 2^(n-1))
        s_mid = Fr(G.V, 2) - Fr(G.V * (2 ** (n - 1)), 1) / (G.eps * G.K)
        x, F, lam, mu, calls, steps, f = solve_budget(G, s_mid)
        ok2, msg2 = G.check(x, F, lam, s_mid)
        print(f"        mid-window budget: exact equilibrium {ok2}; oracle calls={calls}; "
              f"return flow={f[G.rho]} (expected near 2^(n-1)+1 = {2**(n-1)+1})")
        allok &= bool(ok) and bool(ok2)  # artifact: exit status (both outputs exact equilibria)
    sys.exit(0 if allok else 1)  # artifact: exit status
