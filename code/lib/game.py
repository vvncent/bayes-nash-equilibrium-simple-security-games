"""Bayesian simple security game in marginal form, exact equilibrium checker, and the
lower-bound family G_n built from the Disser-Skutella counting gadget.

Game data (all Fractions):
  p[i]      prior of attacker type i (sum 1)
  a[i][j]   attacker payoff at target j when uncovered
  b[i][j]   attacker payoff loss from coverage (>= 0); utility a - b*x_j
  d[j]      defender payoff gain from coverage (>= 0)
  budget    total coverage sum_j x_j (r for the real game, any real s for partial budgets)
Equilibrium (x, f, lam):
  f >= 0, sum_j f[i][j] = p[i];  f[i][j] > 0  =>  j maximizes a[i][j] - b[i][j] x_j
  0 <= x <= 1, sum x = budget;   q_j = d_j * sum_i f[i][j]
  x_j > 0 => q_j >= lam;  x_j < 1 => q_j <= lam.
"""
from fractions import Fraction as Fr
from mcf import ds_gadget, ds_recursive_flow, residual_arcs, bellman_ford, Net


def check_equilibrium(p, a, b, d, budget, x, f, lam, verbose=False):
    """Exact verification of a (partial-budget) equilibrium. Returns (ok, message)."""
    m, n = len(p), len(d)
    if any(xj < 0 or xj > 1 for xj in x):
        return False, "coverage outside [0,1]"
    if sum(x) != budget:
        return False, f"sum x = {sum(x)} != budget {budget}"
    for i in range(m):
        if any(f[i][j] < 0 for j in range(n)):
            return False, f"negative flow in row {i}"
        if sum(f[i]) != p[i]:
            return False, f"row {i} sums to {sum(f[i])} != {p[i]}"
        util = [a[i][j] - b[i][j] * x[j] for j in range(n)]
        best = max(util)
        for j in range(n):
            if f[i][j] > 0 and util[j] != best:
                return False, f"type {i} attacks non-best target {j}"
    w = [sum(f[i][j] for i in range(m)) for j in range(n)]
    q = [d[j] * w[j] for j in range(n)]
    for j in range(n):
        if x[j] > 0 and q[j] < lam:
            return False, f"target {j}: covered but score {q[j]} < lam {lam}"
        if x[j] < 1 and q[j] > lam:
            return False, f"target {j}: unfilled but score {q[j]} > lam {lam}"
    return True, "ok"


class Gn:
    """Lower-bound instance G_n (see findings.md, Theorem 1).

    Types  = arcs of the DS gadget N_n plus the return arc rho = (t_n, s_n), capacity 2^n.
    Targets = nodes of N_n.
    """

    def __init__(self, n, A=Fr(1, 2), slope_eps=None):
        self.n = n
        net, s, t, idx = ds_gadget(n)
        self.gadget = net
        self.s_n, self.t_n = s, t
        # circulation network = gadget + return arc
        circ = Net(net.n)
        circ.names = list(net.names)
        for k in range(net.m):
            circ.add_arc(net.tail[k], net.head[k], net.cap[k], net.cost[k])
        self.rho = circ.add_arc(t, s, 2 ** n, 0)  # cost set per mu
        self.circ = circ
        self.V = circ.n
        self.L = self.V - 1
        self.kappa = list(circ.cap)
        self.Kap = sum(self.kappa)
        self.D = [sum(circ.cap[k] for k in range(circ.m) if circ.tail[k] == u) for u in range(self.V)]
        assert sum(self.D) == self.Kap
        self.A = Fr(A)
        self.C = max(circ.cost[k] for k in range(net.m))  # = 2^{n-1} - 1/2
        self.eps = Fr(1, self.L * 2 ** (n + 4))
        self.K = 4 * (Fr(2 ** n) / self.eps + self.L * 2 ** (n + 1))
        self.M = 2 * self.K + self.C + 2
        self.r = Fr(self.V, 2)  # = n + 1, an integer
        if slope_eps is not None:
            # homotopy/rounding experiments: special slope (1+tau)K with 0 < tau <= eps,
            # all size parameters (K, M) unchanged
            assert 0 < slope_eps <= self.eps
            self.eps = Fr(slope_eps)
        self._build_game()

    def _build_game(self):
        circ, K, eps = self.circ, self.K, self.eps
        mT, nT = circ.m, self.V
        self.p = [Fr(self.kappa[k], self.Kap) for k in range(mT)]
        self.d = [Fr(self.Kap, self.D[u]) for u in range(nT)]
        # disallowed pairs: payoff -M - K x (never a best response); every slope is K
        # except the single special entry (rho, s_n), whose slope is (1+eps)K.
        a = [[-self.M] * nT for _ in range(mT)]
        b = [[K] * nT for _ in range(mT)]
        self.val = {}  # TU values on allowed pairs (k,u), excluding the parametric special value
        self.beta = {}
        for k in range(mT):
            u, w = circ.tail[k], circ.head[k]
            self.val[(k, u)] = Fr(0)
            self.beta[(k, u)] = Fr(1)
            if k == self.rho:
                self.val[(k, w)] = self.A
                self.beta[(k, w)] = 1 + eps
            else:
                self.val[(k, w)] = -circ.cost[k]
                self.beta[(k, w)] = Fr(1)
        for (k, u), v in self.val.items():
            be = self.beta[(k, u)]
            a[k][u] = v + be * K / 2
            b[k][u] = be * K
        self.a, self.b = a, b

    # ---------- TU parametric problem (circulation with return-arc cost -mu) ----------
    def tu_flow(self, mu):
        """Optimal circulation for return-arc cost -mu (mu not an integer, 0 < mu < 2^n).

        Uses the closed-form DS flow of value ceil(mu) and certifies optimality exactly.
        Returns (flow, potentials pi) with reduced costs c + pi_u - pi_w >= 0 on residual arcs.
        """
        mu = Fr(mu)
        v = -(-mu.numerator // mu.denominator)  # ceil
        assert 0 < mu < 2 ** self.n and mu.denominator != 1
        fg = ds_recursive_flow(self.n, v)
        f = fg + [v]
        circ = self.circ
        circ.cost[self.rho] = -mu
        res = residual_arcs(circ, f)
        arcs = list(res) + [(circ.n, u, 1, Fr(0), -1, 0) for u in range(circ.n)]
        dist, _ = bellman_ford(circ.n + 1, arcs, [circ.n])  # raises if not optimal
        pi = dist[:circ.n]
        return f, pi

    def relative_price_range(self, mu, f):
        """Exact min/max of P'_u - P'_{s_n} over all TU-optimal duals at mu (P' = -pi)."""
        circ = self.circ
        circ.cost[self.rho] = -Fr(mu)
        res = residual_arcs(circ, f)
        # difference constraints pi_w - pi_u <= cost(u,w) on residual arcs
        d_from, _ = bellman_ford(circ.n, res, [self.s_n])     # max (pi_w - pi_sn)
        rev = [(a[1], a[0], a[2], a[3], a[4], a[5]) for a in res]
        d_to, _ = bellman_ford(circ.n, rev, [self.s_n])        # dist(w -> s_n)
        # P'_u - P'_sn = pi_sn - pi_u ; max = dist(u -> s_n), min = -dist(s_n -> u)
        lo = [-d_from[u] for u in range(circ.n)]
        hi = [d_to[u] for u in range(circ.n)]
        return lo, hi

    def game_equilibrium_from_tu(self, mu):
        """Map the TU optimum at mu to a partial-budget equilibrium of the game (exact)."""
        mu = Fr(mu)
        f, pi = self.tu_flow(mu)
        circ = self.circ
        Pp = [-pi[u] for u in range(self.V)]
        c = (self.A - mu) / self.eps - Pp[self.s_n]
        P = [Pp[u] + c for u in range(self.V)]
        x = [Fr(1, 2) + P[u] / self.K for u in range(self.V)]
        # transportation flow: type k sends f_k to head, kappa_k - f_k to tail
        F = [[Fr(0)] * self.V for _ in range(circ.m)]
        for k in range(circ.m):
            F[k][circ.head[k]] += Fr(f[k], self.Kap)
            F[k][circ.tail[k]] += Fr(self.kappa[k] - f[k], self.Kap)
        return x, F, Fr(1), sum(x), f

    def check(self, x, F, lam, budget):
        return check_equilibrium(self.p, self.a, self.b, self.d, budget, x, F, lam)


def describe(G):
    bits = max(max(abs(v.numerator).bit_length(), v.denominator.bit_length())
               for row in G.a + G.b for v in row)
    return (f"n={G.n}: types={len(G.p)}, targets={len(G.d)}, eps=1/{G.eps.denominator}, "
            f"K={G.K} (~2^{G.K.numerator.bit_length()}), max entry bits={bits}")


if __name__ == "__main__":
    import sys, time
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(1, nmax + 1):
        t0 = time.time()
        G = Gn(n)
        prev_budget = None
        all_ok = True
        mono = True
        for j in range(2 ** n):
            mu = Fr(2 * j + 1, 2)
            x, F, lam, budget, f = G.game_equilibrium_from_tu(mu)
            ok, msg = G.check(x, F, lam, budget)
            if not ok:
                all_ok = False
                print("  FAIL", j, msg)
                break
            # return-arc flow (in kappa units) must be j+1
            if f[G.rho] != j + 1:
                all_ok = False
            if prev_budget is not None and not (budget < prev_budget):
                mono = False
            prev_budget = budget
        print(describe(G))
        print(f"   {2**n} exact partial-budget equilibria verified: {all_ok}; "
              f"budgets strictly decrease as forced return flow j+1 increases: {mono}; "
              f"final budget r={G.r}; time {time.time()-t0:.2f}s")
