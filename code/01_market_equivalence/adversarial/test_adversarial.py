"""Adversarial-oracle stress test of the game -> market reduction (Ch. 3, Prop. prop:mk-g2m,
Thm. thm:mk-main(b)), in exact rational arithmetic (fractions.Fraction; z3 over linear real arithmetic).

The procedure under test is lib/procedure.py (solve_game: cutoff bisection with pattern intervals,
pinned narrowing with canonicalization, exact budget repair), with the perturbation lemma
(Lemma mk-degenerate, decode from 01_market_equivalence/check_degenerate.py) for zero slopes / gains.
Both are imported read-only. Only the oracle is replaced, by the adversarial oracles below; every oracle
answer is verified to be an exact (M1) equilibrium of the query by an independent checker before it is
handed to the procedure, and every output is checked to be an exact BNE of the ORIGINAL game by two
independent checkers (core.check_bne and bne_ok below).

Oracles (all answer the dense zero-reserve (M1) instance (p, c, a, b) of a box query):
  default  z3 Solver, default settings and model
  lexmin   z3 Optimize, lexicographically smallest price vector (then smallest v, then smallest f)
  lexmax   z3 Optimize, lexicographically largest price vector (then smallest v, then smallest f)
  random   3 extreme points by random linear objectives over the equilibrium set (a union of polyhedra);
           pick one at random; with prob. 1/2 return a random relative-interior point of its
           complementary piece (positive convex combination of the vertex and 2 more piece vertices)
  degen    z3 Optimize maximizing the number of degenerate features (zero prices, unfilled capacity,
           buyers with unspent mass, tight buyer-good pairs i.e. ties), so a degenerate equilibrium is
           returned whenever one exists; ties broken by lexicographically largest prices

Usage ($PY -I -B, from the artifact root):
  test_adversarial.py quick                 <= 60 s subset (small games, all oracles, audit, controls)
  test_adversarial.py main [N_scale] [workers] [seed] [limit_s]   the full random + structured run
                                            (per-run wall-clock limit, default 1800 s)
While a run is going: logs/progress_<tag>.log (START/DONE/TIMEOUT per run, HEARTBEAT every 60 s with
each running task's live phase), logs/live_<tag>/w<k>.json (live status per worker), and
logs/runs_<tag>.jsonl (one record per finished run, written as it finishes).
  test_adversarial.py controls [workers]    the negative controls only
  test_adversarial.py games seed id1 id2 .. rerun named games of the main list, all oracles (2 workers)
Exit status: 0 iff every (game, oracle) run gives an exact BNE with every oracle answer verified, and
every negative control is caught; 1 on any failure or uncaught control; 2 if there is no failure but some
runs hit the per-run time limit (those runs are unverified and listed as TIMEOUT). Per-run records: adversarial/logs/runs_<mode>.jsonl.
"""
import sys, os, time, json, random, traceback
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, ".."), _os.path.join(_HERE, "..", "..", "lib")]  # artifact: path bootstrap
from fractions import Fraction as Fr
from math import ceil
import z3
import core
from core import R, val, Game, check_bne, check_box, box_query, bits, loads, br_flow
import procedure
from procedure import solve_game, narrow_and_repair, Q2_of, labels01, canonicalize, pin_recover
from check_degenerate import Game0, Q3_of, decode
from run_tests import three_target, two_target

LOGDIR = _os.path.join(_HERE, "logs")

# Live status (inspectable runs): a worker of run_pool sets _STATUS["path"]; status() then rewrites the
# worker's file logs/live_<tag>/w<k>.json (atomically) with the current task, phase, oracle-call number,
# when the current oracle call started, and the slowest call so far. No-op outside run_pool.
_STATUS = {"path": None, "info": {}}


def status(**kw):
    if _STATUS["path"] is None:
        return
    _STATUS["info"].update(kw)
    _STATUS["info"]["updated"] = time.time()
    tmp = _STATUS["path"] + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(_STATUS["info"], fh)
    os.replace(tmp, _STATUS["path"])
ORACLES = ["default", "lexmin", "lexmax", "random", "degen"]


# ============================================================================== independent checkers
def m1_ok(p, c, a, b, P, v, F):
    """Definition def:m1 (a)-(d), dense, zero reserves. Exact."""
    m, n = len(p), len(c)
    if len(P) != n or len(v) != m or len(F) != m:
        return False, "shape"
    for j in range(n):
        if P[j] < 0:
            return False, f"P{j}<0"
    for i in range(m):
        if v[i] < 0:
            return False, f"v{i}<0"
        for j in range(n):
            u = a[i][j] - b[i][j] * P[j]
            if F[i][j] < 0:
                return False, f"F{i}{j}<0"
            if v[i] < u:
                return False, f"(a) v{i} < u{i}{j}"
            if F[i][j] > 0 and v[i] != u:
                return False, f"(b) F{i}{j}>0 not tight"
        rs = sum(F[i])
        if rs > p[i] or (v[i] > 0 and rs != p[i]):
            return False, f"(c) row {i}"
    for j in range(n):
        cs = sum(F[i][j] for i in range(m))
        if cs > c[j] or (P[j] > 0 and cs != c[j]):
            return False, f"(d) column {j}"
    return True, "ok"


def bne_ok(G, x, f):
    """BNE from the game definition: x in [0,1]^n with sum r (realizable by Lemma realize), every type
    best-responds (all positive f_ij maximize a_ij - b_ij x_j over ALL targets, rows sum to p_i),
    and the defender cutoff condition: some lambda with d_j w_j >= lambda where x_j > 0 and
    d_j w_j <= lambda where x_j < 1 (i.e. max over x_j<1 <= min over x_j>0)."""
    m, n = G.m, G.n
    if len(x) != n or any(not isinstance(q, Fr) for q in x):
        return False, "x not exact"
    if sum(x) != G.r or any(q < 0 or q > 1 for q in x):
        return False, "coverage"
    for i in range(m):
        if sum(f[i]) != G.p[i] or any(q < 0 for q in f[i]):
            return False, f"row {i}"
        V = max(G.a[i][k] - G.b[i][k] * x[k] for k in range(n))
        for j in range(n):
            if f[i][j] > 0 and G.a[i][j] - G.b[i][j] * x[j] != V:
                return False, f"type {i} not best responding at {j}"
    w = [sum(f[i][j] for i in range(m)) for j in range(n)]
    sc = [G.d[j] * w[j] for j in range(n)]
    lo = [sc[j] for j in range(n) if x[j] < 1]
    hi = [sc[j] for j in range(n) if x[j] > 0]
    if lo and hi and max(lo) > min(hi):
        return False, f"defender cutoff violated {max(lo)} > {min(hi)}"
    # direct defender optimality against the expected-utility objective (equivalent; second check)
    if sum(sc[j] * x[j] for j in range(n)) != sum(sorted(sc, reverse=True)[:G.r]):
        return False, "defender not optimal"
    return True, "ok"


def maxbits(*objs):
    mb = 0
    for o in objs:
        if isinstance(o, (list, tuple)):
            mb = max(mb, maxbits(*o))
        else:
            mb = max(mb, bits(o))
    return mb


# ============================================================================== oracles
class OracleError(Exception):
    pass


def encode(p, c, a, b, s):
    m, n = len(p), len(c)
    P = [z3.Real(f"P{j}") for j in range(n)]
    v = [z3.Real(f"v{i}") for i in range(m)]
    F = [[z3.Real(f"F{i}_{j}") for j in range(n)] for i in range(m)]
    U = [[R(a[i][j]) - R(b[i][j]) * P[j] for j in range(n)] for i in range(m)]
    cs = [z3.Sum([F[i][j] for i in range(m)]) for j in range(n)]
    rs = [z3.Sum(F[i]) for i in range(m)]
    for j in range(n):
        s.add(P[j] >= 0, cs[j] <= R(c[j]), z3.Or(P[j] == 0, cs[j] == R(c[j])))
        # implied bound: P_j > 0 forces a full column, so some buyer has 0 <= v_i = a_ij - b_ij P_j
        s.add(P[j] <= R(max([Fr(0)] + [a[i][j] / b[i][j] for i in range(m)])))
    for i in range(m):
        s.add(v[i] >= 0, rs[i] <= R(p[i]), z3.Or(v[i] == 0, rs[i] == R(p[i])))
        # implied bound: v_i > 0 forces a full row, so v_i = a_ij - b_ij P_j <= a_ij for a used j
        s.add(v[i] <= R(max([Fr(0)] + list(a[i]))))
        for j in range(n):
            s.add(F[i][j] <= R(p[i]))
        for j in range(n):
            s.add(F[i][j] >= 0, v[i] >= U[i][j], z3.Or(F[i][j] == 0, v[i] == U[i][j]))
    return P, v, F, U, cs, rs


def read(mod, P, v, F):
    return ([val(mod, e) for e in P], [val(mod, e) for e in v], [[val(mod, e) for e in row] for row in F])


class Oracle:
    """Counts calls and bit lengths; verifies every answer exactly (raises OracleError otherwise)."""

    def __init__(self, name, seed=0, verify=True):
        assert name in ORACLES
        self.name = name
        self.rng = random.Random(seed)
        self.calls = 0
        self.qbits = 0
        self.abits = 0
        self.verify = verify
        self.ndegen = 0  # total number of degenerate features over all answers
        self.maxcall, self.maxcall_at = 0.0, 0  # slowest oracle call (seconds, call number)
        self.fallbacks = 0  # optimizations that hit OPT_MS (see _check_opt)

    def solve(self, p, c, a, b):
        self.calls += 1
        qb = maxbits(p, c, a, b)
        self.qbits = max(self.qbits, qb)
        t1 = time.time()
        status(phase=f"in oracle call {self.calls} ({self.name})", call=self.calls, call_started=t1, query_bits=qb)
        P, v, F = getattr(self, "_" + self.name)(p, c, a, b)
        dt = time.time() - t1
        if dt > self.maxcall:
            self.maxcall, self.maxcall_at = dt, self.calls
        status(phase=f"procedure step (LP / decoding) after oracle call {self.calls}", call=self.calls,
               call_started=None, last_call_s=round(dt, 3), max_call_s=round(self.maxcall, 3),
               max_call_at=self.maxcall_at)
        if self.verify:
            ok, why = m1_ok(p, c, a, b, P, v, F)
            if not ok:
                raise OracleError(f"oracle {self.name} answer is not an (M1) equilibrium: {why}")
        self.abits = max(self.abits, maxbits(P, v, F))
        m, n = len(p), len(c)
        # degenerate features of the answer (what the degen oracle maximizes): zero prices, unfilled
        # capacity, unspent buyer mass, tight buyer-good pairs beyond one per buyer (ties)
        self.ndegen += (sum(q == 0 for q in P) + sum(sum(F[i][j] for i in range(m)) < c[j] for j in range(n))
                        + sum(sum(F[i]) < p[i] for i in range(m))
                        + sum(max(0, sum(1 for j in range(n) if v[i] == a[i][j] - b[i][j] * P[j]) - 1)
                              for i in range(m)))
        return P, v, F

    # Every z3 Optimize call of the oracles (b)-(d) gets OPT_MS milliseconds. On "unknown" (time
    # limit) the randomized oracle retries with a new random objective; after RETRIES failures, or for
    # lexmin/lexmax/degen at once, the oracle falls back to a plain z3 Solver equilibrium (default
    # oracle, a fresh random seed). Fallbacks are counted per run (record field "fallbacks"); every
    # answer, fallback or not, is verified exactly by m1_ok before the procedure sees it.
    OPT_MS = 20000
    RETRIES = 3

    def _check_opt(self, s):
        s.set("timeout", self.OPT_MS)
        r = s.check()
        if r == z3.sat:
            return True
        if r == z3.unknown:
            self.fallbacks += 1
            return False
        raise OracleError(f"{self.name}: z3 returned {r}")

    def _fallback(self, p, c, a, b):
        s = z3.Solver()
        s.set("random_seed", self.rng.randint(0, 10 ** 6))
        P, v, F, *_ = encode(p, c, a, b, s)
        if s.check() != z3.sat:
            raise OracleError("fallback: no equilibrium found")
        return read(s.model(), P, v, F)

    # (a)
    def _default(self, p, c, a, b):
        s = z3.Solver()
        P, v, F, *_ = encode(p, c, a, b, s)
        if s.check() != z3.sat:
            raise OracleError("no equilibrium found (z3 unsat?)")
        return read(s.model(), P, v, F)

    # (b)
    def _lex(self, p, c, a, b, sense):
        s = z3.Optimize()
        s.set(priority="lex")
        P, v, F, *_ = encode(p, c, a, b, s)
        for e in P:
            (s.minimize if sense == "min" else s.maximize)(e)
        for e in v + [q for row in F for q in row]:
            s.minimize(e)
        if not self._check_opt(s):
            return self._fallback(p, c, a, b)
        return read(s.model(), P, v, F)

    def _lexmin(self, p, c, a, b):
        return self._lex(p, c, a, b, "min")

    def _lexmax(self, p, c, a, b):
        return self._lex(p, c, a, b, "max")

    # (c)
    def _robj(self, es):
        return z3.Sum([R(Fr(self.rng.randint(-5, 5), self.rng.randint(1, 3))) * e for e in es])

    def _random(self, p, c, a, b):
        pts = []
        tries = 0
        while len(pts) < 3:
            s = z3.Optimize()
            P, v, F, *_ = encode(p, c, a, b, s)
            (s.maximize if self.rng.random() < 0.5 else s.minimize)(self._robj(P + v + [q for r_ in F for q in r_]))
            if self._check_opt(s):
                pts.append(read(s.model(), P, v, F))
            else:
                tries += 1
                if tries >= self.RETRIES:
                    pts.append(self._fallback(p, c, a, b))
        P0, v0, F0 = pts[self.rng.randrange(3)]
        if self.rng.random() < 0.5:
            return P0, v0, F0
        # relative interior of the complementary piece of (P0, v0, F0)
        m, n = len(p), len(c)
        piece = [(P0, v0, F0)]
        for _ in range(2):
            s = z3.Optimize()
            P = [z3.Real(f"P{j}") for j in range(n)]
            v = [z3.Real(f"v{i}") for i in range(m)]
            F = [[z3.Real(f"F{i}_{j}") for j in range(n)] for i in range(m)]
            for j in range(n):
                cs = z3.Sum([F[i][j] for i in range(m)])
                s.add(P[j] >= 0, cs <= R(c[j]), P[j] <= R(max([Fr(0)] + [a[i][j] / b[i][j] for i in range(m)])))
                s.add(cs == R(c[j]) if P0[j] > 0 else P[j] == 0)
            for i in range(m):
                rs = z3.Sum(F[i])
                s.add(v[i] >= 0, rs <= R(p[i]), v[i] <= R(max([Fr(0)] + list(a[i]))))
                s.add(rs == R(p[i]) if v0[i] > 0 else v[i] == 0)
                for j in range(n):
                    u = R(a[i][j]) - R(b[i][j]) * P[j]
                    s.add(F[i][j] >= 0)
                    if v0[i] == a[i][j] - b[i][j] * P0[j]:
                        s.add(v[i] == u)
                    else:
                        s.add(v[i] >= u, F[i][j] == 0)
            (s.maximize if self.rng.random() < 0.5 else s.minimize)(self._robj(P + v + [q for r_ in F for q in r_]))
            if not self._check_opt(s):
                continue  # a piece vertex timed out: combine the points found so far
            piece.append(read(s.model(), P, v, F))
        wt = [Fr(self.rng.randint(1, 9)) for _ in piece]
        W = sum(wt)
        wt = [q / W for q in wt]
        P = [sum(w_ * pt[0][j] for w_, pt in zip(wt, piece)) for j in range(n)]
        v = [sum(w_ * pt[1][i] for w_, pt in zip(wt, piece)) for i in range(m)]
        F = [[sum(w_ * pt[2][i][j] for w_, pt in zip(wt, piece)) for j in range(n)] for i in range(m)]
        return P, v, F

    # (d)
    def _degen(self, p, c, a, b):
        m, n = len(p), len(c)
        s = z3.Optimize()
        s.set(priority="lex")
        P, v, F, U, cs, rs = encode(p, c, a, b, s)
        one, zero = z3.IntVal(1), z3.IntVal(0)
        feats = ([z3.If(P[j] == 0, one, zero) for j in range(n)]
                 + [z3.If(cs[j] < R(c[j]), one, zero) for j in range(n)]
                 + [z3.If(rs[i] < R(p[i]), one, zero) for i in range(m)]
                 + [z3.If(v[i] == U[i][j], one, zero) for i in range(m) for j in range(n)])
        s.maximize(z3.Sum(feats))
        for e in P:
            s.maximize(e)
        if not self._check_opt(s):
            return self._fallback(p, c, a, b)
        return read(s.model(), P, v, F)


# ============================================================================== games
def mk(p, a, b, d, r):
    return {"p": [str(q) for q in p], "a": [[str(q) for q in row] for row in a],
            "b": [[str(q) for q in row] for row in b], "d": [str(q) for q in d], "r": r}


def unmk(g):
    return ([Fr(q) for q in g["p"]], [[Fr(q) for q in row] for row in g["a"]],
            [[Fr(q) for q in row] for row in g["b"]], [Fr(q) for q in g["d"]], g["r"])


def norm(w):
    return [Fr(q) / sum(w) for q in w]


def pick_size(rng, mmax=5, nmax=6):
    # weighted toward small sizes, but every (m, n) up to (mmax, nmax) occurs
    m = rng.choice([1, 1, 2, 2, 2, 3, 3, 4, 5][: [1, 2, 5, 7, 8, 9][mmax]])
    n = rng.choice([2, 2, 3, 3, 3, 4, 4, 5, 6][: [0, 0, 2, 5, 7, 8, 9][nmax]])
    return m, n


def gen(rng, kind):
    rq = lambda lo, hi, dmax: Fr(rng.randint(lo, hi), rng.randint(1, dmax))
    if kind == "zero":
        m, n = rng.choice([(1, 2), (1, 2), (1, 3), (2, 2), (2, 2), (2, 3), (1, 4), (3, 2)])
    elif kind == "big":
        m, n = rng.choice([(4, 5), (5, 5), (4, 6), (5, 6), (5, 6)])
    else:
        m, n = pick_size(rng)
    r = rng.randint(1, n - 1)
    p = norm([rng.randint(1, 4) for _ in range(m)])
    a = [[rq(-6, 6, 3) for _ in range(n)] for _ in range(m)]
    b = [[rq(1, 6, 3) for _ in range(n)] for _ in range(m)]
    d = [rq(1, 5, 3) for _ in range(n)]
    if kind in ("pos", "big"):
        pass
    elif kind == "ties":  # few distinct values: many exact ties in payoffs, slopes, gains, priors
        p = norm([1] * m) if rng.random() < 0.7 else p
        a = [[Fr(rng.choice([-1, 0, 1, 2])) for _ in range(n)] for _ in range(m)]
        b = [[Fr(rng.choice([1, 2])) for _ in range(n)] for _ in range(m)]
        d = [Fr(rng.choice([1, 2])) for _ in range(n)]
    elif kind == "neardeg":  # equal intercepts within each type, equal priors, near-equal gains/slopes
        p = norm([1] * m)
        base = [rq(-3, 3, 2) for _ in range(m)]
        eps = Fr(1, rng.choice([997, 1000, 1024]))
        a = [[base[i] + (eps * rng.randint(-1, 1) if rng.random() < 0.3 else 0) for _ in range(n)]
             for i in range(m)]
        b = [[Fr(1) + eps * rng.randint(0, 2) for _ in range(n)] for _ in range(m)]
        d = [Fr(1) + eps * rng.randint(0, 2) for _ in range(n)]
    elif kind == "zero":  # zero slopes and/or zero gains (perturbation lemma)
        b = [[Fr(0) if rng.random() < 0.4 else rq(1, 4, 2) for _ in range(n)] for _ in range(m)]
        d = [Fr(0) if rng.random() < 0.35 else rq(1, 4, 2) for _ in range(n)]
        a = [[rq(-4, 4, 2) for _ in range(n)] for _ in range(m)]
        if all(q > 0 for row in b for q in row) and all(q > 0 for q in d):
            if rng.random() < 0.5:
                b[rng.randrange(m)][rng.randrange(n)] = Fr(0)
            else:
                d[rng.randrange(n)] = Fr(0)
    elif kind == "identical":  # identical types
        a = [a[0][:] for _ in range(m)]
        b = [b[0][:] for _ in range(m)]
        p = norm([1] * m) if rng.random() < 0.5 else p
    elif kind == "dominant":  # one target dominant for every type
        js = rng.randrange(n)
        for i in range(m):
            a[i][js] = Fr(rng.randint(8, 12))
    elif kind == "tiny":  # zero-prior-like tiny priors
        m = max(m, 2)
        a = [[rq(-6, 6, 3) for _ in range(n)] for _ in range(m)]
        b = [[rq(1, 6, 3) for _ in range(n)] for _ in range(m)]
        delta = Fr(1, rng.choice([1000, 997, 4096, 10 ** 6]))
        k = rng.randint(1, m - 1)  # k tiny types
        p = [delta] * k + [(1 - k * delta) / (m - k)] * (m - k)
        rng.shuffle(p)
    else:
        raise ValueError(kind)
    return mk(p, a, b, d, r)


def audit_games():
    out = []
    for name, G in (("audit_three_target", three_target()), ("audit_two_target", two_target())):
        out.append((name, mk(G.p, G.a, G.b, G.d, G.r)))
    return out


# Games on which removing the Lemma mk-pin patch yields a non-BNE output (found by a search over 300
# small random games with the ctl_nopatch variant; on most games the raw sub-box flow is already a
# full-box flow, see the README). Kept fixed so the control is reproducible; also solved in every mode.
PIN_WITNESS = [
    {"p": ["2/5", "2/5", "1/5"], "a": [["2", "-1/2", "-1"], ["5/3", "-1/3", "4/3"], ["2", "-1", "0"]],
     "b": [["3", "1", "3"], ["3/2", "1", "1"], ["5", "5", "2"]], "d": ["2", "1", "1"], "r": 1},
    {"p": ["1/5", "2/5", "2/5"], "a": [["-4", "5", "-1"], ["2", "-5", "-4"], ["-5/2", "0", "1"]],
     "b": [["3/2", "3", "1/2"], ["5/2", "1/3", "2"], ["2/3", "2", "3"]], "d": ["1", "2/3", "4/3"], "r": 1},
    {"p": ["1/2", "1/2"], "a": [["2", "2", "0", "1"], ["-1", "-1", "0", "0"]],
     "b": [["1", "1", "2", "2"], ["2", "2", "2", "2"]], "d": ["2", "2", "1", "1"], "r": 3},
    {"p": ["1/3", "2/3"], "a": [["0", "1", "-1", "0"], ["2", "-1", "2", "0"]],
     "b": [["2", "2", "1", "2"], ["1", "2", "2", "2"]], "d": ["2", "2", "1", "2"], "r": 1},
]


def witness_games():
    return [(f"pin_witness#{i}", g) for i, g in enumerate(PIN_WITNESS)]


def game_list(scale, seed):
    """scale=1: 1,020 random/structured games + audit cases."""
    plan = [("pos", 420), ("big", 30), ("ties", 150), ("neardeg", 120), ("zero", 120),
            ("identical", 60), ("dominant", 60), ("tiny", 60)]
    rng = random.Random(seed)
    out = audit_games() + witness_games()
    for kind, cnt in plan:
        for t in range(max(1, int(cnt * scale))):
            out.append((f"{kind}#{t}", gen(rng, kind)))
    return out


# ============================================================================== one run
def input_bits(g):
    p, a, b, d, r = unmk(g)
    tot = 0
    for q in p + [x for row in a for x in row] + [x for row in b for x in row] + d:
        tot += abs(q.numerator).bit_length() + q.denominator.bit_length()
    return tot


def narrow_bound(n, eta):
    """Per coordinate the width starts <= 1 and shrinks by 2/3 per query until <= eta."""
    k, wdt = 0, Fr(1)
    while wdt > eta:
        wdt *= Fr(2, 3)
        k += 1
    return n * k


def run_one(task):
    gid, g, oname, seed = task
    t0 = time.time()
    rec = {"game": gid, "oracle": oname, "seed": seed}
    p, a, b, d, r = unmk(g)
    rec.update(m=len(p), n=len(d), r=r, input_bits=input_bits(g))
    try:
        status(phase="setup (game, perturbation epsilon)")
        G0 = Game0(p, a, b, d, r)
        degenerate = any(q == 0 for row in b for q in row) or any(q == 0 for q in d)
        orc = Oracle(oname, seed)
        if degenerate:
            eps = Fr(1, 8 * Q3_of(G0))
            G = Game(p, a, [[q + eps for q in row] for row in b], [q + eps for q in d], r)
            rec["eps_bits"] = (1 / eps).numerator.bit_length()
        else:
            G = Game(p, a, b, d, r)
        x, f, st = solve_game(G, orc, True)
        status(phase="decode / final BNE checks", call_started=None)
        okp, whyp = check_bne(G, x, f)
        assert okp, "procedure output not a BNE of the game it solved: " + whyp
        if degenerate:
            x, f = decode(G0, x, f)
        ok1, why1 = check_bne(G0, x, f)
        ok2, why2 = bne_ok(G0, x, f)
        rec.update(ok=bool(ok1 and ok2), why=f"{why1}/{why2}", exit=st["exit"], calls=orc.calls,
                   bisect=st.get("bisect_steps"), narrow=st.get("narrow_calls"),
                   Q1_bits=st.get("Q1_bits"), eta_bits=st.get("eta_bits"),
                   endpoint_bits=max(st.get("maxbits") or [0]), qbits=orc.qbits, abits=orc.abits,
                   degen_answers=orc.ndegen, degenerate=degenerate, x=[str(q) for q in x],
                   max_call_s=round(orc.maxcall, 3), max_call_at=orc.maxcall_at, fallbacks=orc.fallbacks)
        # call-count bound of Lemmas mk-bisect + mk-narrow (exact)
        D = 1 + max(G.d)
        X = D * procedure.Q1_of(G)[0] ** 2
        k = 0
        while Fr(2) ** k < X:
            k += 1
        bound = 1 + k + narrow_bound(G.n, Fr(1, 4 * G.n * Q2_of(G)))
        rec["call_bound"] = bound
        if orc.calls > bound:
            rec.update(ok=False, why=f"calls {orc.calls} > bound {bound}")
    except Exception as e:  # any assertion inside the procedure or oracle is a failure
        rec.update(ok=False, why=f"{type(e).__name__}: {e}", trace=traceback.format_exc()[-1500:])
        if "orc" in locals():
            rec.update(calls=orc.calls, qbits=orc.qbits, abits=orc.abits)
    rec["t"] = round(time.time() - t0, 2)
    if not rec["ok"]:
        rec["data"] = g
    return rec


def run_audit_bracket(oname, seed):
    """Ex. mk-interp: start narrowing from the audit's bracket at lambda=2/7 (the off-chord case)."""
    t0 = time.time()
    rec = {"game": "audit_bracket_2/7", "oracle": oname, "seed": seed}
    try:
        G = three_target()
        F = Fr
        L = [F(0), F(0), F(1, 6)]
        H = [F(1, 3), F(2, 3), F(2, 3)]
        fL = [[F(2, 7), F(2, 7), F(0)], [F(0), F(1, 7), F(1, 7)], [F(0), F(0), F(1, 7)]]
        fH = [[F(1, 7), F(3, 7), F(0)], [F(1, 7), F(0), F(1, 7)], [F(0), F(0), F(1, 7)]]
        orc = Oracle(oname, seed)
        st = {}
        x, f = narrow_and_repair(G, orc, F(2, 7), L, fL, H, fH, st)
        ok1, w1 = check_bne(G, x, f)
        ok2, w2 = bne_ok(G, x, f)
        rec.update(ok=bool(ok1 and ok2), why=f"{w1}/{w2}", exit=st["exit"], calls=orc.calls,
                   qbits=orc.qbits, abits=orc.abits, x=[str(q) for q in x], m=3, n=3, r=1)
    except Exception as e:
        rec.update(ok=False, why=f"{type(e).__name__}: {e}", trace=traceback.format_exc()[-1500:])
    rec["t"] = round(time.time() - t0, 2)
    return rec


# ============================================================================== negative controls
class CorruptOracle(Oracle):
    """Returns a NON-equilibrium (checked) on every call; the harness verifier is switched off so the
    procedure sees the corrupted answer. kinds: price (raise the price of a used good by 1/3),
    capacity (a genuine equilibrium of the instance with doubled capacities), drop (halve all flows)."""

    def __init__(self, kind, seed=0):
        super().__init__("lexmin", seed, verify=False)
        self.kind = kind
        self.flagged = 0  # corrupted answers the independent verifier rejects

    def solve(self, p, c, a, b):
        if self.kind == "capacity":
            P, v, F = Oracle.solve(self, p, [2 * q for q in c], a, b)
        else:
            P, v, F = Oracle.solve(self, p, c, a, b)
            if self.kind == "price":
                m, n = len(p), len(c)
                j = max(range(n), key=lambda j: sum(F[i][j] for i in range(m)))
                P = P[:]
                P[j] += Fr(1, 3)
            else:
                F = [[q / 2 for q in row] for row in F]
        if not m1_ok(p, c, a, b, P, v, F)[0]:
            self.flagged += 1
        return P, v, F


def narrow_variant(G, oracle, lam0, L, fL, H, fH, variant, max_iter=4000):
    """Copy of procedure.narrow_and_repair with one step removed (and the internal assertions that
    would only re-detect the removed step switched off, so the final BNE check is what catches it).
    variant: nopatch   - pinned query kept, Lemma mk-pin patch removed (raw sub-box flow used)
             nopin     - query the whole box [L,H] unpinned (no pin), raw flow used
             norepair  - narrowing kept, exact budget repair removed: return the endpoint (L, f^L)
             interp    - narrowing kept, budget repair replaced by chord interpolation with f^L"""
    n = G.n
    c = [lam0 / dj for dj in G.d]
    Q2 = Q2_of(G)
    eta = Fr(1, 4 * n * Q2)
    sp = Fr(1)
    while sp > eta / 4:
        sp /= 2
    it = 0
    while any(H[j] - L[j] > eta for j in range(n)):
        progress = False
        for k in range(n):
            wdt = H[k] - L[k]
            if wdt <= eta:
                continue
            it += 1
            if it > max_iter:
                raise RuntimeError("no progress (iteration cap)")
            lo3, hi3 = L[k] + wdt / 3, H[k] - wdt / 3
            t = Fr(ceil(lo3 / sp)) * sp
            l, h = L[:], H[:]
            if variant != "nopin":
                l[k] = h[k] = t
            if lam0 == 0:
                x = h[:]
                f = br_flow(G, x)
            else:
                x, f = box_query(G, c, l, h, oracle)
            x, f = canonicalize(G, c, l, h, x, f)
            if variant in ("nopatch", "nopin"):
                F = f
            else:
                F = pin_recover(G, c, L, fL, H, fH, k, x, f)
            tot = sum(x)
            if tot == G.r:
                return x, F, "hit"
            if tot < G.r:
                L, fL = x, F
            else:
                H, fH = x, F
            if H[k] - L[k] < wdt:
                progress = True
        if not progress:
            raise RuntimeError("no progress (widths did not shrink in a full round)")
    if variant == "norepair":
        return L, fL, "endpoint"
    if variant == "interp":
        sL, sH = sum(L), sum(H)
        th = (G.r - sL) / (sH - sL)
        return [L[j] + th * (H[j] - L[j]) for j in range(n)], fL, "interp"
    # nopatch / nopin keep the exact repair LP of the original (copied)
    xe, fe = L, fL
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
    return [val(mod, e) for e in X], fe, ("repair" if val(mod, sv) == 0 else "repair-positive")


def control_run(task):
    """Returns a record with caught=True iff the variant failed (exception or non-BNE output)."""
    gid, g, ctl, oname, seed = task
    t0 = time.time()
    p, a, b, d, r = unmk(g)
    G = Game(p, a, b, d, r)
    rec = {"game": gid, "control": ctl, "oracle": oname}
    corc = CorruptOracle(ctl.split("_", 1)[1], seed) if ctl.startswith("corrupt_") else None
    try:
        if corc is not None:
            orc = corc
            x, f, st = solve_game(G, orc, True)
            ok = check_bne(G, x, f)[0] and bne_ok(G, x, f)[0]
            rec.update(caught=not ok, how="non-BNE output" if not ok else "NOT CAUGHT")
        else:
            orc = Oracle(oname, seed)
            st = {}
            if gid == "audit_bracket_2/7":
                F = Fr
                lam0, L, H = F(2, 7), [F(0), F(0), F(1, 6)], [F(1, 3), F(2, 3), F(2, 3)]
                fL = [[F(2, 7), F(2, 7), F(0)], [F(0), F(1, 7), F(1, 7)], [F(0), F(0), F(1, 7)]]
                fH = [[F(1, 7), F(3, 7), F(0)], [F(1, 7), F(0), F(1, 7)], [F(0), F(0), F(1, 7)]]
            else:
                kind, data = procedure.locate_cutoff(G, orc, st)
                if kind == "done":
                    rec.update(caught=None, how="bisection hit: narrowing not reached (skipped)")
                    rec["t"] = round(time.time() - t0, 2)
                    return rec
                lam0, L, fL, H, fH = data
            x, f, ex = narrow_variant(G, orc, lam0, L, fL, H, fH, ctl.split("_", 1)[1])
            ok = check_bne(G, x, f)[0] and bne_ok(G, x, f)[0]
            rec.update(exit=ex, caught=not ok, how=("non-BNE output (" + bne_ok(G, x, f)[1] + ")") if not ok
                       else "NOT CAUGHT (valid BNE)", x=[str(q) for q in x])
    except OracleError as e:
        rec.update(caught=True, how=f"oracle verifier: {e}")
    except Exception as e:
        rec.update(caught=True, how=f"procedure stopped: {type(e).__name__}: {str(e)[:120]}")
    if corc is not None:
        rec.update(flagged=corc.flagged, calls=corc.calls)
    rec["t"] = round(time.time() - t0, 2)
    return rec


def controls(workers, nper, seed, out, ctl_oracles=("lexmin", "lexmax", "degen"), tag="controls", limit=900):
    """Each control runs on the audit cases and nper random games that reach narrowing."""
    rng = random.Random(seed)
    games = audit_games() + witness_games()
    for t in range(nper):
        games.append((f"ctl_pos#{t}", gen(rng, "pos")))
    tasks = []
    for gid, g in games:
        for kind in ("price", "capacity", "drop"):
            tasks.append((gid, g, "corrupt_" + kind, "lexmin", 0))
    games_n = games + [("audit_bracket_2/7", mk(*(lambda G: (G.p, G.a, G.b, G.d, G.r))(three_target())))]
    for gid, g in games_n:
        for ctl in ("nopatch", "nopin", "norepair", "interp"):
            for o in ctl_oracles:
                tasks.append((gid, g, "ctl_" + ctl, o, 1))
    recs = run_pool("control_run", tasks, workers, limit, tag, out)
    summ = {}
    for rc in recs:
        s = summ.setdefault(rc["control"], {"runs": 0, "caught": 0, "nonBNE": 0, "stopped": 0, "skipped": 0,
                                            "oracle_flagged_all": True})
        if rc["caught"] is None:
            s["skipped"] += 1
            continue
        s["runs"] += 1
        s["caught"] += bool(rc["caught"])
        s["nonBNE"] += rc["how"].startswith("non-BNE")
        s["stopped"] += rc["how"].startswith("procedure stopped")
        if rc["control"].startswith("corrupt_"):
            s["oracle_flagged_all"] &= rc.get("flagged", 0) >= 1
    allok = True
    for ctl, s in sorted(summ.items()):
        # corrupted oracle: must be caught on EVERY run (and flagged by the independent verifier);
        # removed steps: must be caught on at least one run (they are not wrong on every game)
        if ctl.startswith("corrupt_"):
            caught = s["runs"] > 0 and s["caught"] == s["runs"] and s["oracle_flagged_all"]
        else:
            caught = s["caught"] >= 1
        allok &= caught
        print(f"control {ctl:16s} runs={s['runs']:3d} caught={s['caught']:3d} (non-BNE output {s['nonBNE']}, "
              f"procedure stopped {s['stopped']}) skipped={s['skipped']} -> {'CAUGHT' if caught else 'NOT CAUGHT'}",
              flush=True)
    return allok


# ============================================================================== driver
def task_label(task):
    return " ".join(str(x) for x in task if not isinstance(x, dict))


def _worker_main(conn, wid, live_dir, fn_name):
    fn = globals()[fn_name]
    _STATUS["path"] = _os.path.join(live_dir, f"w{wid}.json")
    while True:
        task = conn.recv()
        if task is None:
            break
        _STATUS["info"] = {"worker": wid, "pid": os.getpid(), "task": task_label(task), "started": time.time()}
        status(phase="start")
        conn.send(fn(task))
        status(phase="idle (finished " + task_label(task) + ")")


def lost_record(fn_name, task, why, last):
    if fn_name == "run_one":
        gid, g, oname, seed = task
        return {"game": gid, "oracle": oname, "seed": seed, "m": len(g["p"]), "n": len(g["d"]), "r": g["r"],
                "ok": False, "timeout": why.startswith("timeout"), "why": why, "last_status": last, "data": g}
    gid, g, ctl, oname, seed = task
    return {"game": gid, "control": ctl, "oracle": oname, "caught": None, "how": why, "last_status": last}


def run_pool(fn_name, tasks, workers, limit, tag, out):
    """Inspectable process pool. While it runs:
      logs/progress_<tag>.log   START / DONE / TIMEOUT line per task, and every 60 s a HEARTBEAT block
                                listing every running task with its elapsed time and live status;
      logs/live_<tag>/w<k>.json the live status of worker k (task, phase, oracle call number, start of
                                the current oracle call, slowest call so far);
      out (jsonl)               one record per finished task, appended and flushed as soon as it ends.
    A task running longer than `limit` wall-clock seconds is killed (its worker restarted) and recorded
    with timeout=True and its last live status; it is reported separately from failures."""
    import multiprocessing as mp
    from multiprocessing.connection import wait
    ctx = mp.get_context("spawn")
    live = _os.path.join(LOGDIR, f"live_{tag}")
    os.makedirs(live, exist_ok=True)
    for fn_ in os.listdir(live):
        os.remove(_os.path.join(live, fn_))
    prog = open(_os.path.join(LOGDIR, f"progress_{tag}.log"), "w", buffering=1)
    t0 = time.time()
    pending = list(tasks)
    total = len(pending)
    recs = []
    slots = {}

    def stamp():
        return f"{time.strftime('%H:%M:%S')} +{time.time() - t0:7.0f}s"

    def spawn(wid):
        pc, cc = ctx.Pipe()
        pr = ctx.Process(target=_worker_main, args=(cc, wid, live, fn_name), daemon=True)
        pr.start()
        cc.close()
        slots[wid] = {"proc": pr, "conn": pc, "task": None, "start": None}

    def assign(wid):
        sl = slots[wid]
        if pending:
            sl["task"] = pending.pop(0)
            sl["start"] = time.time()
            sl["conn"].send(sl["task"])
            prog.write(f"{stamp()} START   w{wid} {task_label(sl['task'])}\n")
        else:
            sl["task"] = None

    def read_live(wid):
        try:
            with open(_os.path.join(live, f"w{wid}.json")) as fh:
                return json.load(fh)
        except Exception:
            return {}

    def finish(wid, rec, word):
        recs.append(rec)
        out.write(json.dumps(rec) + "\n")
        out.flush()
        sl = slots[wid]
        res = rec.get("ok", rec.get("caught"))
        prog.write(f"{stamp()} {word:7s} w{wid} {task_label(sl['task'])} result={res} calls={rec.get('calls')} "
                   f"t={time.time() - sl['start']:.1f}s [{len(recs)}/{total} done]\n")

    for wid in range(max(1, workers)):
        spawn(wid)
        assign(wid)
    last_hb = time.time()
    while any(sl["task"] is not None for sl in slots.values()):
        busy = {sl["conn"]: wid for wid, sl in slots.items() if sl["task"] is not None}
        for conn in wait(list(busy), timeout=2):
            wid = busy[conn]
            try:
                rec = conn.recv()
                finish(wid, rec, "DONE")
            except (EOFError, OSError):
                finish(wid, lost_record(fn_name, slots[wid]["task"], "worker died", read_live(wid)), "CRASH")
                spawn(wid)
            assign(wid)
        now = time.time()
        for wid, sl in list(slots.items()):
            if sl["task"] is not None and now - sl["start"] > limit:
                last = read_live(wid)
                sl["proc"].terminate()
                sl["proc"].join(10)
                finish(wid, lost_record(fn_name, sl["task"], f"timeout after {limit}s (killed)", last), "TIMEOUT")
                spawn(wid)
                assign(wid)
        if now - last_hb >= 60:
            last_hb = now
            prog.write(f"{stamp()} HEARTBEAT {len(recs)}/{total} done, {len(pending)} queued, running:\n")
            for wid, sl in sorted(slots.items()):
                if sl["task"] is not None:
                    st = read_live(wid)
                    cs = st.get("call_started")
                    incall = f", current oracle call running {now - cs:.0f}s" if cs else ""
                    prog.write(f"    w{wid} {now - sl['start']:6.0f}s {task_label(sl['task'])} | {st.get('phase')}"
                               f"{incall} | slowest call {st.get('max_call_s')}s (#{st.get('max_call_at')})\n")
    for sl in slots.values():
        try:
            sl["conn"].send(None)
        except Exception:
            pass
        sl["proc"].join(10)
    prog.write(f"{stamp()} ALL DONE {len(recs)}/{total}\n")
    prog.close()
    return recs


def summarize(recs):
    fails = [r for r in recs if not r["ok"] and not r.get("timeout")]
    by = {}
    for r in recs:
        if "calls" not in r:
            continue
        key = (r["m"], r["n"], bool(r.get("degenerate")))
        s = by.setdefault(key, {"runs": 0, "calls": 0, "qbits": 0, "abits": 0, "Q1": 0, "inb": 0, "t": 0.0})
        s["runs"] += 1
        s["calls"] = max(s["calls"], r["calls"])
        s["qbits"] = max(s["qbits"], r["qbits"])
        s["abits"] = max(s["abits"], r["abits"])
        s["Q1"] = max(s["Q1"], r.get("Q1_bits") or 0)
        s["inb"] = max(s["inb"], r.get("input_bits", 0))
        s["t"] = max(s["t"], r["t"])
    print("size table (max over runs): m n degenerate | runs | max oracle calls | max query bits | "
          "max answer bits | max log2 Q1 | max input bits | max run s")
    for key in sorted(by):
        s = by[key]
        print(f"  {key[0]} {key[1]} {'Z' if key[2] else '-'} | {s['runs']:4d} | {s['calls']:5d} | {s['qbits']:5d} | "
              f"{s['abits']:5d} | {s['Q1']:6d} | {s['inb']:4d} | {s['t']:.1f}")
    ex = {}
    for r in recs:
        ex[r.get("exit")] = ex.get(r.get("exit"), 0) + 1
    print("exits:", ex)
    per_o = {}
    for r in recs:
        po = per_o.setdefault(r["oracle"], [0, 0, 0, 0])
        po[0] += 1
        po[1] += r["ok"]
        po[2] += r.get("calls", 0) or 0
        po[3] += r.get("degen_answers", 0) or 0
    print("per oracle [runs, BNE ok, oracle calls, degenerate features in answers]:", per_o)
    return fails


def report(tag, recs, ngames, t0, cok):
    fails = summarize(recs)
    touts = [r for r in recs if r.get("timeout")]
    for rc in fails:
        print("FAILURE:", json.dumps(rc), flush=True)
    for rc in touts:
        print("TIMEOUT (unverified, not a failure):", json.dumps({k: rc[k] for k in rc if k != "data"}), flush=True)
    ab = [r for r in recs if r["game"] == "audit_bracket_2/7"]
    print("audit bracket (Ex. mk-interp) outputs:", sorted(set(tuple(r.get("x", [])) for r in ab)))
    print(f"{tag}: {len(recs)} runs ({ngames} games x {len(ORACLES)} oracles + {len(ab)} audit-bracket), "
          f"failures={len(fails)}, timeouts={len(touts)}, controls {'all caught' if cok else 'NOT ALL CAUGHT'}, "
          f"{time.time()-t0:.0f}s", flush=True)
    # exit 1: a failure or an uncaught control; exit 2: no failure, but some runs timed out (unverified)
    return 1 if (fails or not cok) else (2 if touts else 0)


def main_mode(scale, workers, seed, tag, ctl_n, limit):
    os.makedirs(LOGDIR, exist_ok=True)
    t0 = time.time()
    games = game_list(scale, seed)
    tasks = []
    for gi, (gid, g) in enumerate(games):
        for oi, o in enumerate(ORACLES):
            tasks.append((gid, g, o, seed * 100003 + gi * 7 + oi))
    print(f"{len(games)} games x {len(ORACLES)} oracles = {len(tasks)} runs (+ audit bracket x {len(ORACLES)}), "
          f"workers={workers}, per-run limit {limit}s; progress: logs/progress_{tag}.log, "
          f"live status: logs/live_{tag}/, records: logs/runs_{tag}.jsonl", flush=True)
    # big tasks first for load balance
    tasks.sort(key=lambda t: -(len(t[1]["p"]) * len(t[1]["d"]) * (8 if any(q == "0" for q in t[1]["d"])
                                                                   or any(q == "0" for row in t[1]["b"] for q in row) else 1)))
    with open(_os.path.join(LOGDIR, f"runs_{tag}.jsonl"), "w") as out:
        recs = run_pool("run_one", tasks, workers, limit, tag, out)
        for i, o in enumerate(ORACLES):
            rc = run_audit_bracket(o, 3 + i)
            out.write(json.dumps(rc) + "\n")
            recs.append(rc)
    print(f"main runs finished, {time.time()-t0:.0f}s", flush=True)
    with open(_os.path.join(LOGDIR, f"controls_{tag}.jsonl"), "w") as cout:
        cok = controls(workers, ctl_n, seed + 1, cout, tag=f"controls_{tag}")
    return report(tag, recs, len(games), t0, cok)


def quick_mode(workers):
    """<= 60 s: audit games, one pin witness, 10 small random/structured games, all oracles; audit
    bracket; controls on the audit cases and pin witnesses (oracles lexmin, degen)."""
    os.makedirs(LOGDIR, exist_ok=True)
    t0 = time.time()
    rng = random.Random(2026)
    games = audit_games() + witness_games()[:1]
    for kind in ("pos", "pos", "ties", "neardeg", "identical", "dominant", "tiny", "ties", "pos", "zero"):
        while True:
            g = gen(rng, kind)
            if len(g["p"]) * len(g["d"]) <= (2 if kind == "zero" else 6):
                break
        games.append((kind + "#q", g))
    tasks = [(gid, g, o, 11 * gi + oi) for gi, (gid, g) in enumerate(games) for oi, o in enumerate(ORACLES)]
    with open(_os.path.join(LOGDIR, "runs_quick.jsonl"), "w") as out:
        recs = run_pool("run_one", tasks, workers, 300, "quick", out)
        for o in ORACLES:
            rc = run_audit_bracket(o, 3)
            out.write(json.dumps(rc) + "\n")
            recs.append(rc)
    with open(_os.path.join(LOGDIR, "controls_quick.jsonl"), "w") as cout:
        cok = controls(workers, 0, 5, cout, ("lexmin", "degen"), tag="controls_quick", limit=300)
    return report("quick", recs, len(games), t0, cok)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "quick"
    if mode == "quick":
        w = int(sys.argv[2]) if len(sys.argv) > 2 else 4
        sys.exit(quick_mode(w))
    if mode == "main":
        scale = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
        w = int(sys.argv[3]) if len(sys.argv) > 3 else 8
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        limit = int(sys.argv[5]) if len(sys.argv) > 5 else 1800
        sys.exit(main_mode(scale, w, seed, f"main_s{seed}", 16, limit))
    if mode == "games":  # rerun named games of the main list with all oracles: games seed id1 id2 ...
        seed = int(sys.argv[2])
        want = sys.argv[3:]
        os.makedirs(LOGDIR, exist_ok=True)
        t0 = time.time()
        games = game_list(1.0, seed)
        tasks = [(gid, g, o, seed * 100003 + gi * 7 + oi) for gi, (gid, g) in enumerate(games) if gid in want
                 for oi, o in enumerate(ORACLES)]
        with open(_os.path.join(LOGDIR, f"runs_games_s{seed}.jsonl"), "w") as out:
            recs = run_pool("run_one", tasks, 2, 1800, f"games_s{seed}", out)
        for rc in recs:
            print(rc["game"], rc["oracle"], "BNE" if rc["ok"] else "FAIL", rc.get("why"), "calls", rc.get("calls"),
                  "fallbacks", rc.get("fallbacks"), f"{rc.get('t')}s", flush=True)
        sys.exit(report(f"games_s{seed}", recs, len(want), t0, True))
    if mode == "controls":
        w = int(sys.argv[2]) if len(sys.argv) > 2 else 8
        os.makedirs(LOGDIR, exist_ok=True)
        with open(_os.path.join(LOGDIR, "controls_only.jsonl"), "w") as cout:
            sys.exit(0 if controls(w, 16, 2, cout) else 1)
    raise SystemExit(__doc__)
