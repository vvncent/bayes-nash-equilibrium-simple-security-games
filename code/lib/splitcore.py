"""Exact split-space tools for two-profile markets (root session; independent of the branches).

Market: goods j with capacity c_j>0; group-1 buyers (payoff a_ij - P_j), group-2 buyers
(payoff a_ij - s_j P_j); masses p_i>0; outside option 0; reserve price 0.
All arithmetic is exact (fractions.Fraction) via the stdlib simplex in exactlp.py.
Intended for n<=4 goods and a handful of buyers.
"""
from fractions import Fraction as Fr
from itertools import combinations
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactlp import solve_lp  # noqa: E402

# No artificial price cap: unbounded maxima (zero-capacity coordinates) are detected by the LP.


class LPB:
    """Tiny exact LP builder: named variables with bounds, <= and == rows."""

    def __init__(self):
        self.names, self.lo, self.hi, self.ub, self.eq = [], [], [], [], []

    def var(self, name, lo=Fr(0), hi=None):
        self.names.append(name)
        self.lo.append(lo)
        self.hi.append(hi)
        return name

    def le(self, coefs, rhs):
        self.ub.append((dict(coefs), Fr(rhs)))

    def ge(self, coefs, rhs):
        self.ub.append(({k: -Fr(v) for k, v in coefs.items()}, -Fr(rhs)))

    def eqc(self, coefs, rhs):
        self.eq.append((dict(coefs), Fr(rhs)))

    def solve(self, obj, sense="min"):
        idx = {nm: k for k, nm in enumerate(self.names)}

        def row(d):
            r = [Fr(0)] * len(self.names)
            for k, v in d.items():
                r[idx[k]] += Fr(v)
            return r

        c = row(obj)
        if sense == "max":
            c = [-x for x in c]
        st, x, val = solve_lp(c, [row(d) for d, _ in self.ub], [b for _, b in self.ub],
                              [row(d) for d, _ in self.eq], [b for _, b in self.eq], self.lo, self.hi)
        if st != "optimal":
            return st, None, None
        return st, dict(zip(self.names, x)), (-val if sense == "max" else val)

    def copy(self):
        o = LPB()
        o.names, o.lo, o.hi = list(self.names), list(self.lo), list(self.hi)
        o.ub, o.eq = list(self.ub), list(self.eq)
        return o


class Market:
    def __init__(self, c, s, g1, g2):
        """g1, g2: lists of (mass, [intercepts per good])."""
        self.c = [Fr(x) for x in c]
        self.s = [Fr(x) for x in s]
        self.g1 = [(Fr(p), [Fr(a) for a in row]) for p, row in g1]
        self.g2 = [(Fr(p), [Fr(a) for a in row]) for p, row in g2]
        self.n = len(self.c)

    def _add_face(self, L, group, cap, pv, tag):
        """Add the optimal dual face of one group's transport LP (own price units pv)."""
        n = self.n
        sub = LPB()
        for nm in pv:
            sub.var(nm, Fr(0))
        vs = [sub.var(f"{tag}v{i}") for i in range(len(group))]
        for i, (p, row) in enumerate(group):
            for j in range(n):
                sub.ge({vs[i]: 1, pv[j]: 1}, row[j])
        obj = {vs[i]: p for i, (p, _) in enumerate(group)}
        for j in range(n):
            obj[pv[j]] = obj.get(pv[j], 0) + Fr(cap[j])
        st, _, val = sub.solve(obj)
        assert st == "optimal", st
        for nm in vs:
            L.var(nm)
        for i, (p, row) in enumerate(group):
            for j in range(n):
                L.ge({vs[i]: 1, pv[j]: 1}, row[j])
        L.le(obj, val)
        return val

    def faces(self, t):
        n = self.n
        L = LPB()
        P = [L.var(f"P{j}", Fr(0)) for j in range(n)]
        Q = [L.var(f"Q{j}", Fr(0)) for j in range(n)]
        V1 = self._add_face(L, self.g1, [Fr(x) for x in t], P, "a")
        V2 = self._add_face(L, self.g2, [self.c[j] - Fr(t[j]) for j in range(n)], Q, "b")
        return L, P, Q, V1, V2

    def extremes(self, t):
        """Coordinatewise min/max of D_1(t) and of S^{-1}D_2(c-t) (None = unbounded above)."""
        L, P, Q, V1, V2 = self.faces(t)
        out = {}
        for name, var, scale in (("D1", P, [Fr(1)] * self.n), ("D2s", Q, self.s)):
            lo, hi = [], []
            for j in range(self.n):
                lo.append(L.solve({var[j]: 1}, "min")[2] / scale[j])
                st, _, b = L.solve({var[j]: 1}, "max")
                hi.append(None if st == "unbounded" else b / scale[j])
            out[name] = (lo, hi)
        return out, V1, V2

    def common_prices(self, t):
        """Coordinatewise range of P over D_1(t) ∩ S^{-1}D_2(c-t); None if empty."""
        L, P, Q, _, _ = self.faces(t)
        for j in range(self.n):
            L.eqc({Q[j]: 1, P[j]: -self.s[j]}, 0)
        if L.solve({}, "min")[0] != "optimal":
            return None
        out = []
        for j in range(self.n):
            st, _, hi = L.solve({P[j]: 1}, "max")
            out.append((L.solve({P[j]: 1}, "min")[2], None if st == "unbounded" else hi))
        return out

    def is_solution(self, t):
        return self.common_prices(t) is not None

    def gap(self, t):
        """F(t) at a point where both faces are singletons; raises otherwise."""
        ex, _, _ = self.extremes(t)
        lo1, hi1 = ex["D1"]
        lo2, hi2 = ex["D2s"]
        if lo1 != hi1 or lo2 != hi2:
            raise ValueError("non-generic query: faces are not singletons")
        return [lo2[j] - lo1[j] for j in range(self.n)]

    def solution_box(self, mu):
        """Coordinatewise range of t over all SC solutions with common price mu
        (None if mu is not an equilibrium price)."""
        r = self.solution_lp(mu)
        if r is None:
            return None
        L, t = r
        return [(L.solve({t[j]: 1}, "min")[2], L.solve({t[j]: 1}, "max")[2]) for j in range(self.n)]

    def solution_lp(self, mu):
        """(LP builder, split variables) describing all SC solutions with common price mu."""
        n = self.n
        L = LPB()
        t = [L.var(f"t{j}", Fr(0), self.c[j]) for j in range(n)]
        cols = [[{} for _ in range(n)] for _ in range(2)]
        for gi, (group, scale) in enumerate(((self.g1, [Fr(1)] * n), (self.g2, self.s))):
            for i, (p, row) in enumerate(group):
                vals = [row[j] - scale[j] * Fr(mu[j]) for j in range(n)]
                vi = max([Fr(0)] + vals)
                tight = [j for j in range(n) if vals[j] == vi]
                fs = {j: L.var(f"f{gi}_{i}_{j}") for j in tight}
                L.le({fs[j]: 1 for j in tight}, p) if tight else None
                if vi > 0:
                    L.ge({fs[j]: 1 for j in tight}, p)  # infeasible if no tight edge
                for j in tight:
                    cols[gi][j][fs[j]] = 1
        for j in range(n):
            c1 = dict(cols[0][j]); c1[t[j]] = c1.get(t[j], 0) - 1
            L.le(c1, 0)                                   # group-1 load <= t_j
            c2 = dict(cols[1][j]); c2[t[j]] = c2.get(t[j], 0) + 1
            L.le(c2, self.c[j])                           # group-2 load <= c_j - t_j
            if Fr(mu[j]) > 0:
                L.ge(c1, 0)
                L.ge(c2, self.c[j])
        if L.solve({}, "min")[0] != "optimal":
            return None
        return L, t

    def promise1(self):
        masses = [p for p, _ in self.g1] + [p for p, _ in self.g2]
        bs = {sum(S) for r in range(1, len(masses) + 1) for S in combinations(masses, r)}
        cs = {sum(S) for r in range(1, self.n + 1) for S in combinations(self.c, r)}
        return not (bs & cs)
