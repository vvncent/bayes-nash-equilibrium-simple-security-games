# Exact (Fraction-only) falsification test of the l1-contraction premise used by exact-search.typ
# for "BNE in UEOPL via FGMS Theorem 34".  Not a proof: random finite instances only.
#
# Part A: F(x,q) = (1-delta)(T,R) + delta(a0, kappa/2) exactly as in exact-search.typ section 2,
#         with g = 1 (tau = kappa = 1/8); eta, delta from the note's formulas (the contraction
#         argument uses only eta*B <= tau, eta*D*sum(1/d') <= kappa(1-2delta), delta <= 1/8).
#         Checks: simplex-projection KKT, F maps cube to cube, ||F(z)-F(z')||_1 <= (1-delta)||z-z'||_1.
# Part B (control, must FAIL): same map with eta = 1 (diagonal no longer nonnegative); the test
#         must detect an l1 expansion, showing it has power.
# Part C: exact re-computation of exact-search.typ's four-target example (J v and the l2 growth).
#
# Run (artifact root): python -I -B 04_ueopl/check_l1_contraction.py
import os, random, sys
from fractions import Fraction as Q

LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "check_l1_contraction.log")  # artifact: was logs/
out = []
def say(s=""):
    print(s); out.append(s)

def proj_simplex(u):
    s = sorted(u, reverse=True); acc = Q(0); th = None
    for k in range(1, len(s) + 1):
        acc += s[k - 1]; t = (acc - 1) / k
        th = t if th is None or t > th else th
    y = [max(Q(0), uj - th) for uj in u]
    # exact KKT check of the Euclidean projection onto the simplex
    ok = sum(y) == 1 and all(yj >= 0 for yj in y)
    ok = ok and all((uj - yj == th) if yj > 0 else (uj <= th) for uj, yj in zip(u, y))
    return y, ok

def clip(v, lo, hi):
    return min(hi, max(lo, v))

def make_F(G, eta_override=None):
    p, a, b, d, r = G["p"], G["a"], G["b"], G["d"], G["r"]
    m, n = len(p), len(d)
    g = Q(1); tau = kappa = g / 8
    B = max(max(row) for row in b)
    dp = [dj + g / 16 for dj in d]; D = max(dp); sinv = sum(1 / x for x in dp)
    eta = min(Q(1), tau / (1 + B), kappa / (4 * (1 + D) * (1 + sinv)))
    delta = min(Q(1, 8), eta * g / (8 * (1 + D)), g / (8 * (1 + B)))
    if eta_override is not None:
        eta = eta_override
    a0 = [Q(r, n)] * n
    def lam(s):
        lo, hi = delta * kappa, (1 - delta) * kappa
        if s <= lo: return D
        if s >= hi: return Q(0)
        return D * (hi - s) / (hi - lo)
    kkt_ok = [True]
    def F(z):
        x, q = z[:n], z[n]
        w = [Q(0)] * n
        for i in range(m):
            u = [(a[i][j] - b[i][j] * x[j]) / tau for j in range(n)]
            y, ok = proj_simplex(u)
            kkt_ok[0] &= ok
            for j in range(n):
                w[j] += p[i] * y[j]
        s = clip(q, Q(0), kappa); L = lam(s)
        T = [clip(x[j] + eta * (w[j] - L / dp[j]), Q(0), Q(1)) for j in range(n)]
        R = clip(s + sum(x) - sum(T), Q(0), kappa)
        return [(1 - delta) * t + delta * a0j for t, a0j in zip(T, a0)] + [(1 - delta) * R + delta * kappa / 2]
    return F, delta, kkt_ok

def rand_game(rng):
    m, n = rng.randint(2, 4), rng.randint(2, 4)
    raw = [rng.randint(1, 6) for _ in range(m)]; tot = sum(raw)
    p = [Q(x, tot) for x in raw]
    a = [[Q(rng.randint(-8, 8), rng.choice([1, 2, 4])) for _ in range(n)] for _ in range(m)]
    b = [[rng.choice([Q(0), Q(1, 2), Q(1), Q(2), Q(3)]) for _ in range(n)] for _ in range(m)]
    d = [rng.choice([Q(0), Q(1, 2), Q(1), Q(2)]) for _ in range(n)]
    return dict(p=p, a=a, b=b, d=d, r=rng.randint(1, n - 1))

def rpt(rng, k, den=64):
    return [Q(rng.randint(0, den), den) for _ in range(k)]

def l1(u, v):
    return sum(abs(x - y) for x, y in zip(u, v))

def pair_test(F, delta, n, rng, npairs):
    worst = Q(0); bad = 0; cube_bad = 0
    for t in range(npairs):
        z = rpt(rng, n + 1)
        if t % 2 == 0:   # far pair
            zp = rpt(rng, n + 1)
        else:            # near pair (same or adjacent affine piece)
            zp = [clip(c + Q(rng.randint(-3, 3), 4096), Q(0), Q(1)) for c in z]
        if zp == z: continue
        Fz, Fzp = F(z), F(zp)
        cube_bad += sum(1 for c in Fz + Fzp if c < 0 or c > 1)
        ratio = l1(Fz, Fzp) / l1(z, zp)
        worst = max(worst, ratio)
        if ratio > 1 - delta: bad += 1
    return worst, bad, cube_bad

rng = random.Random(20261121)
NG, NP = 200, 200
say("Part A: exact-search map, %d random games x %d pairs (g=1, tau=kappa=1/8)" % (NG, NP))
allA = True
for gi in range(NG):
    G = rand_game(rng); n = len(G["d"])
    F, delta, kkt = make_F(G)
    worst, bad, cube_bad = pair_test(F, delta, n, rng, NP)
    okg = bad == 0 and cube_bad == 0 and kkt[0]
    allA &= okg
    if gi < 5 or not okg:
        say("  game %2d m=%d n=%d delta=%s worst ratio=%s (<= 1-delta: %s) cube_ok=%s kkt_ok=%s"
            % (gi, len(G["p"]), n, delta, worst, bad == 0, cube_bad == 0, kkt[0]))
say("Part A %s: l1 ratio <= 1-delta, F(cube) in cube, projection KKT on all sampled pairs" % ("PASS" if allA else "FAIL"))

say("")
say("Part B (control): same games with eta = 1; the test must find an l1 expansion somewhere")
found = False
rngB = random.Random(7)
for gi in range(NG):
    G = rand_game(rngB); n = len(G["d"])
    F, delta, kkt = make_F(G, eta_override=Q(1))
    worst, bad, _ = pair_test(F, delta, n, rngB, NP)
    if bad > 0:
        found = True
        say("  control game %d: worst ratio %s > 1-delta=%s (expansion detected)" % (gi, worst, 1 - delta))
        break
say("Part B %s: control violation %s" % ("PASS" if found else "FAIL", "detected" if found else "NOT detected"))

say("")
say("Part C: exact-search.typ four-target example (fixed cutoff 1/4, tau=eta=1/100, d=1)")
c, alpha, tau, eta, lamc = Q(1, 2), Q(1, 4), Q(1, 100), Q(1, 100), Q(1, 4)
types = [(i, j) for i in range(4) for j in range(4) if i != j]
def T4(x):
    w = [Q(0)] * 4; supp = []
    for (i, j) in types:
        U = []
        for k in range(4):
            if k == i: U.append(alpha * (c - x[i]))
            elif k == j: U.append(c - x[j])
            else: U.append(-3 - x[k])
        y, ok = proj_simplex([uk / tau for uk in U])
        assert ok
        supp.append(sum(1 for t in y if t > 0))
        for k in range(4): w[k] += Q(1, 12) * y[k]
    T = [x[k] + eta * (w[k] - lamc) for k in range(4)]
    return T, supp, all(0 < t < 1 for t in T)
x = [c + Q(1, 10) * t for t in (Q(1), Q(1, 4), Q(2), Q(-13, 4))]
v = [Q(4), Q(2), Q(-3), Q(-3)]
T0, supp, noclip = T4(x)
two = [types[k] for k, s in enumerate(supp) if s >= 2]
Jv = []
for h in (Q(1, 10**6), Q(1, 10**7)):
    Th, supph, _ = T4([xi + h * vi for xi, vi in zip(x, v)])
    Jv.append([(a1 - a0) / h for a1, a0 in zip(Th, T0)])
expected = [4 + Q(1, 24), 2 - Q(1, 24), Q(-3), Q(-3)]
lhs = (1 - Q(1, 1000)) ** 2 * sum(t * t for t in expected)
okC = (two == [(0, 1)] and noclip and Jv[0] == Jv[1] == expected and lhs > sum(t * t for t in v))
say("  types with 2-point support: %s ; no clipping: %s" % (two, noclip))
say("  J v (two step sizes) = %s" % [str(t) for t in Jv[0]])
say("  (1-delta)^2 |Jv|^2 = %s  vs |v|^2 = %s" % (lhs, sum(t * t for t in v)))
say("Part C %s: reproduces J v = (4+1/24, 2-1/24, -3, -3) and l2 growth" % ("PASS" if okC else "FAIL"))

say("")
say("OVERALL %s" % ("PASS" if (allA and found and okC) else "FAIL"))
os.makedirs(os.path.dirname(LOG), exist_ok=True)
with open(LOG, "w") as fh:
    fh.write("\n".join(out) + "\n")
sys.exit(0 if (allA and found and okC) else 1)
