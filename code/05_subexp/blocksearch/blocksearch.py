"""Exact block search for the fixed point of a PL l1-contraction (book Ch. 5, Sec. sec:subexp).

Everything that the algorithm computes is exact (fractions.Fraction and Python integers).  z3 is
used only for ground truth (fixed point, uniqueness, contraction premise, pattern LP feasibility).

Implemented as in the book (Thm sx-pl and its subsections):
  * blocks of k coordinates (the last block may be smaller), tail recursion on the remaining
    coordinates with the stated tolerance  theta = delta^2 tau / 16;
  * per call: grid exponent beta = ceil(log2(16 k_b / (delta tau))), N = 2^beta, candidates are a
    disjoint union of integer boxes in [0,N]^k_b (scaled by N);
  * each round: a 1/(2(k_b+1))-deep integer point w of the candidates in their bounding box,
    test c = w/N, recursive tail solve, h = G_X(c, y) evaluated exactly, stop if ||h-c||_1 <= tau/2,
    otherwise remove the l1 halfspace H(c, c-h) (sign formula, Lemma sx-sign) from the candidates;
  * exact reconstruction (Sec. sx-recon): root tolerance tau = 2^-B with tau <= delta/(8 D^2),
    continued-fraction recovery of every coordinate, final exact evaluation.

Deep point (Lemma sx-deep, cited from GLM): NOT GLM's centerpoint algorithm.  A brute-force exact
search: candidate integer points of the bounding box are tried (coordinatewise median first, then a
product grid of marginal quantiles and box endpoints, then -- when the bounding box is small --
every integer point), and the exact l1-halfspace depth of each is computed; the first point of
depth >= 1/(2(k+1)) is used.  If none is found the run fails (DeepPointMissing).

Exact depth.  For z with sign vector sigma = sgn(z-w), z in H(w,v) iff
sum_{sigma_i!=0} sigma_i v_i + sum_{sigma_i=0} |v_i| >= 0.  The set of v with z in H(w,v) is closed,
so the count |C cap H(w,v)| is upper semicontinuous in v and its minimum over v != 0 is attained at
a generic v (all v_i != 0, no signed partial sum zero).  Write v_i = s_i a_i with s in {+-1}^k,
a > 0; then z in H(w,v) iff a . mu > 0 with mu_i = +1 if z_i = w_i, else s_i sgn(z_i - w_i).  The
condition depends on a only through the threshold family {mu : a.mu > 0}; WEIGHTS[k] holds one
generic a per family (k=1: 1 family, k=2: 2, k=3: 4).  depth(w) = min over s and these a.  This
formula is cross-checked against direct minimisation over all integer v in [-4,4]^k by
selftest_depth().
"""
from fractions import Fraction as Fr
from itertools import product
from math import floor
import z3

# ----------------------------------------------------------------------------------------------
# small helpers


def l1(u):
    return sum(abs(t) for t in u)


def sub(u, w):
    return [a - b for a, b in zip(u, w)]


def sgn(t):
    return (t > 0) - (t < 0)


def in_H(z, c, v):
    """Lemma sx-sign: z in H(c, v)."""
    s = 0
    for zi, ci, vi in zip(z, c, v):
        si = sgn(zi - ci)
        s += si * vi if si != 0 else abs(vi)
    return s >= 0


def in_H_definition(z, c, v):
    """Definition of H(c,v): ||z-c|| <= ||z-(c-eps v)|| for every eps>0 (checked just right of 0,
    below the first breakpoint of the convex PL function eps -> ||z-c+eps v||, and at a spread of
    larger eps)."""
    bps = [(ci - zi) / vi for zi, ci, vi in zip(z, c, v) if vi != 0 and (ci - zi) / vi > 0]
    eps = (min(bps) / 2) if bps else Fr(1)
    phi0 = l1(sub(z, c))
    ok = l1([zi - ci + eps * vi for zi, ci, vi in zip(z, c, v)]) >= phi0
    for e2 in [Fr(1, 7), Fr(1, 2), Fr(1), Fr(3), Fr(10)]:
        if ok and l1([zi - ci + e2 * vi for zi, ci, vi in zip(z, c, v)]) < phi0:
            raise AssertionError("convexity violated")
    return ok


def ceil_log2_ratio(num, den):
    """smallest integer beta >= 0 with 2^beta >= num/den (num, den > 0 rationals)."""
    q = Fr(num) / Fr(den)
    b = 0
    while Fr(2) ** b < q:
        b += 1
    return b


class CheckFailure(Exception):
    """An assertion of the book's argument failed (protected point cut, residual bound, ...)."""


class DeepPointMissing(CheckFailure):
    pass


def require(cond, msg):
    if not cond:
        raise CheckFailure(msg)


# ----------------------------------------------------------------------------------------------
# backends: the same circuit code is evaluated over Fractions, over affine forms (to solve one
# affine piece exactly) and over z3 terms (ground truth)


class Aff:
    """value at a base point + affine form in nvar variables. max/min pick the branch by value."""
    __slots__ = ("v", "a", "c")

    def __init__(self, v, a, c):
        self.v, self.a, self.c = v, a, c

    def _lift(self, o):
        if isinstance(o, Aff):
            return o
        o = Fr(o)
        return Aff(o, [0] * len(self.a), o)

    def __add__(self, o):
        o = self._lift(o)
        return Aff(self.v + o.v, [x + y for x, y in zip(self.a, o.a)], self.c + o.c)
    __radd__ = __add__

    def __neg__(self):
        return Aff(-self.v, [-x for x in self.a], -self.c)

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return self._lift(o) - self

    def __mul__(self, o):
        assert not isinstance(o, Aff), "nonlinear"
        o = Fr(o)
        return Aff(self.v * o, [x * o for x in self.a], self.c * o)
    __rmul__ = __mul__

    def __truediv__(self, o):
        assert not isinstance(o, Aff)
        return self * (1 / Fr(o))


def _val(t):
    return t.v if isinstance(t, Aff) else t


class FrB:
    name = "fr"
    K = staticmethod(lambda t: t)
    max = staticmethod(max)
    min = staticmethod(min)


class AffB:
    name = "aff"
    K = staticmethod(lambda t: t)

    @staticmethod
    def max(a, b):
        return a if _val(a) >= _val(b) else b

    @staticmethod
    def min(a, b):
        return a if _val(a) <= _val(b) else b


class Z3B:
    name = "z3"

    @staticmethod
    def K(t):
        return z3.RealVal(str(Fr(t))) if isinstance(t, (Fr, int)) else t

    @staticmethod
    def max(a, b):
        a, b = Z3B.K(a), Z3B.K(b)
        return z3.If(a >= b, a, b)

    @staticmethod
    def min(a, b):
        a, b = Z3B.K(a), Z3B.K(b)
        return z3.If(a <= b, a, b)


def zfr(v):
    return Fr(v.numerator_as_long(), v.denominator_as_long())


def zabs(t):
    return z3.If(t >= 0, t, -t)


# ----------------------------------------------------------------------------------------------
# PL maps.  A map object has .d, .delta and .circuit(u, B) -> list of d outputs.


class PLMap:
    def __init__(self, d, delta, circuit, name=""):
        self.d, self.delta, self.circuit, self.name = d, Fr(delta), circuit, name
        self.evals = 0

    def F(self, u):
        self.evals += 1
        return self.circuit(u, FrB)


def solve_piece(G, prefix, u0):
    """Exact fixed point of the restricted map u -> G(prefix, u)[free] on the affine piece active
    at u0, verified by exact evaluation.  Returns None if the piece is wrong/singular."""
    f = len(u0)
    xs = [Aff(u0[i], [Fr(int(i == j)) for j in range(f)], Fr(0)) for i in range(f)]
    out = G.circuit(list(prefix) + xs, AffB)[len(prefix):]
    # u = A u + b  ->  (I - A) u = b
    M = []
    for i in range(f):
        o = out[i] if isinstance(out[i], Aff) else Aff(Fr(out[i]), [Fr(0)] * f, Fr(out[i]))
        M.append([Fr(int(i == j)) - o.a[j] for j in range(f)] + [o.c])
    for col in range(f):
        piv = next((r for r in range(col, f) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [t / pv for t in M[col]]
        for r in range(f):
            if r != col and M[r][col] != 0:
                fac = M[r][col]
                M[r] = [a - fac * b for a, b in zip(M[r], M[col])]
    u = [M[i][f] for i in range(f)]
    if any(t < 0 or t > 1 for t in u):
        return None
    if G.circuit(list(prefix) + u, FrB)[len(prefix):] != u:
        return None
    return u


def z3_fixed_point(G, prefix=(), unique=True, timeout_ms=600000):
    """Exact fixed point of the restricted map with z3; optional uniqueness proof (unsat of a
    second, different fixed point)."""
    f = G.d - len(prefix)
    xv = [z3.Real(f"x{i}") for i in range(f)]
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    for t in xv:
        s.add(t >= 0, t <= 1)
    out = G.circuit([z3.RealVal(str(t)) for t in prefix] + xv, Z3B)[len(prefix):]
    for i in range(f):
        s.add(xv[i] == Z3B.K(out[i]))
    r = s.check()
    if r != z3.sat:
        return None, str(r)
    mdl = s.model()
    sol = [zfr(mdl.eval(t, model_completion=True)) for t in xv]
    uniq = None
    if unique:
        s.add(z3.Or([xv[i] != z3.RealVal(str(sol[i])) for i in range(f)]))
        uniq = str(s.check())
    return sol, uniq


def z3_contraction(G, delta=None, timeout_ms=300000):
    """z3 search for u,u' with ||G(u)-G(u')||_1 > (1-delta)||u-u'||_1.  'unsat' = premise holds."""
    delta = G.delta if delta is None else Fr(delta)
    d = G.d
    u = [z3.Real(f"u{j}") for j in range(d)]
    v = [z3.Real(f"v{j}") for j in range(d)]
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    for t in u + v:
        s.add(t >= 0, t <= 1)
    Fu = [Z3B.K(t) for t in G.circuit(u, Z3B)]
    Fv = [Z3B.K(t) for t in G.circuit(v, Z3B)]
    lhs = z3.Sum([zabs(Fu[j] - Fv[j]) for j in range(d)])
    rhs = Z3B.K(1 - delta) * z3.Sum([zabs(u[j] - v[j]) for j in range(d)])
    s.add(lhs > rhs)
    r = s.check()
    wit = None
    if r == z3.sat:
        m = s.model()
        wit = ([zfr(m.eval(t, model_completion=True)) for t in u],
               [zfr(m.eval(t, model_completion=True)) for t in v])
    return str(r), wit


# ----------------------------------------------------------------------------------------------
# boxes (inclusive integer intervals per coordinate), cuts, deep points


def box_size(b):
    n = 1
    for lo, hi in b:
        n *= hi - lo + 1
    return n


def union_size(boxes):
    return sum(box_size(b) for b in boxes)


def int_dir(v):
    """positive integer multiple of a rational vector (positive scaling keeps H(c,v))."""
    from math import lcm
    L = 1
    for t in v:
        L = lcm(L, Fr(t).denominator)
    return [int(Fr(t) * L) for t in v]


def cut_boxes(boxes, w, v):
    """Remove H(w, v) from a disjoint union of boxes (exact: every piece has a constant sign
    vector w.r.t. w, so one sign-formula test per piece decides it).  Returns (kept, removed_count)."""
    vi = int_dir(v)
    k = len(w)
    contrib = [{-1: -vi[i], 0: abs(vi[i]), 1: vi[i]} for i in range(k)]
    kept, removed = [], 0
    for b in boxes:
        parts = []
        for i, (lo, hi) in enumerate(b):
            p = []
            wi = w[i]
            if lo < wi:
                p.append((lo, min(hi, wi - 1), -1))
            if lo <= wi <= hi:
                p.append((wi, wi, 0))
            if hi > wi:
                p.append((max(lo, wi + 1), hi, 1))
            parts.append(p)
        for combo in product(*parts):
            s = sum(contrib[i][combo[i][2]] for i in range(k))
            piece = tuple((lo, hi) for lo, hi, _ in combo)
            if s >= 0:
                removed += box_size(piece)
            else:
                kept.append(piece)
    return merge_boxes(kept), removed


def merge_boxes(boxes):
    """merge boxes that agree on all other coordinates and are adjacent in one coordinate."""
    if not boxes:
        return boxes
    k = len(boxes[0])
    changed = True
    while changed:
        changed = False
        for i in range(k):
            groups = {}
            for b in boxes:
                key = b[:i] + b[i + 1:]
                groups.setdefault(key, []).append(b[i])
            nb = []
            for key, ivs in groups.items():
                ivs.sort()
                cur = list(ivs[0])
                for lo, hi in ivs[1:]:
                    if lo == cur[1] + 1:
                        cur[1] = hi
                        changed = True
                    else:
                        nb.append(key[:i] + (tuple(cur),) + key[i:])
                        cur = [lo, hi]
                nb.append(key[:i] + (tuple(cur),) + key[i:])
            boxes = nb
    return boxes


def in_boxes(z, boxes):
    return any(all(lo <= zi <= hi for zi, (lo, hi) in zip(z, b)) for b in boxes)


def _families(k):
    """one generic positive weight vector per threshold family {mu in {+-1}^k : a.mu > 0}."""
    fams = {}
    mus = list(product((-1, 1), repeat=k))
    for a in product(range(1, 6), repeat=k):
        if any(sum(x * y for x, y in zip(a, mu)) == 0 for mu in mus):
            continue
        fam = frozenset(mu for mu in mus if sum(x * y for x, y in zip(a, mu)) > 0)
        fams.setdefault(fam, a)
    return list(fams.values())


WEIGHTS = {k: _families(k) for k in range(1, 5)}
assert [len(WEIGHTS[k]) for k in (1, 2, 3)] == [1, 2, 4]


def sign_counts(boxes, w):
    """n_sigma = #{z in C : sgn(z - w) = sigma}, sigma in {-1,0,1}^k."""
    k = len(w)
    cnt = {}
    for b in boxes:
        per = []
        for i, (lo, hi) in enumerate(b):
            wi = w[i]
            below = max(0, min(hi, wi - 1) - lo + 1)
            eq = 1 if lo <= wi <= hi else 0
            above = max(0, hi - max(lo, wi + 1) + 1)
            per.append(((-1, below), (0, eq), (1, above)))
        for combo in product(*per):
            m = 1
            for _, c in combo:
                m *= c
                if not m:
                    break
            if m:
                key = tuple(s for s, _ in combo)
                cnt[key] = cnt.get(key, 0) + m
    return cnt


def depth_count(boxes, w):
    """exact min over v != 0 of |C cap H(w,v)| (see module docstring)."""
    k = len(w)
    cnt = sign_counts(boxes, w)
    best = None
    for s in product((-1, 1), repeat=k):
        mus = {sig: tuple(1 if sig[i] == 0 else s[i] * sig[i] for i in range(k)) for sig in cnt}
        for a in WEIGHTS[k]:
            tot = 0
            for sig, n in cnt.items():
                if sum(a[i] * mus[sig][i] for i in range(k)) > 0:
                    tot += n
            if best is None or tot < best:
                best = tot
    return best


def depth_count_bruteforce_v(boxes, w, R=4):
    """min over all integer v in [-R,R]^k \\ {0} of |C cap H(w,v)| by enumerating C (small C only)."""
    k = len(w)
    pts = [z for b in boxes for z in product(*[range(lo, hi + 1) for lo, hi in b])]
    best = None
    for v in product(range(-R, R + 1), repeat=k):
        if not any(v):
            continue
        tot = sum(1 for z in pts if in_H(z, w, v))
        best = tot if best is None or tot < best else best
    return best


def marginal_quantile(boxes, i, frac):
    """smallest integer t with #{z in C : z_i <= t} >= frac*|C|."""
    tot = union_size(boxes)
    target = frac * tot
    info = []
    for b in boxes:
        wgt = box_size(b) // (b[i][1] - b[i][0] + 1)
        info.append((b[i][0], b[i][1], wgt))
    lo = min(x[0] for x in info)
    hi = max(x[1] for x in info)

    def cnt(t):
        return sum(wg * max(0, min(t, h) - l + 1) for l, h, wg in info)
    while lo < hi:
        mid = (lo + hi) // 2
        if cnt(mid) >= target:
            hi = mid
        else:
            lo = mid + 1
    return lo


def deep_point(boxes, k, stats, exhaustive_limit=4096, audit=False):
    """brute-force exact search for an integer point of the bounding box of depth >= 1/(2(k+1))."""
    tot = union_size(boxes)
    need = Fr(1, 2 * (k + 1))
    bbox = [(min(b[i][0] for b in boxes), max(b[i][1] for b in boxes)) for i in range(k)]
    bbsize = box_size(bbox)
    stats["deep_calls"] += 1
    if audit and bbsize <= exhaustive_limit:
        # direct test of the lemma's conclusion: the deepest integer point of the bounding box
        mx = max(depth_count(boxes, list(w)) for w in product(*[range(lo, hi + 1) for lo, hi in bbox]))
        stats["deep_audits"] += 1
        stats["deep_audit_min_maxdepth"] = min(stats["deep_audit_min_maxdepth"], Fr(mx, tot))
        if Fr(mx, tot) < need:
            raise DeepPointMissing(f"no integer point of the bbox has depth >= {need}: max {mx}/{tot}")
    # stage 1: coordinatewise (lower) median
    w = [marginal_quantile(boxes, i, Fr(1, 2)) for i in range(k)]
    dc = depth_count(boxes, w)
    if Fr(dc, tot) >= need:
        stats["deep_median"] += 1
        stats["deep_min_depth_used"] = min(stats["deep_min_depth_used"], Fr(dc, tot))
        return w, Fr(dc, tot)
    # stage 2: product grid of marginal quantiles, the median +-1 and box endpoints
    cand = []
    for i in range(k):
        vals = {marginal_quantile(boxes, i, Fr(j, 8 * (k + 1))) for j in range(1, 8 * (k + 1))}
        vals |= {w[i] - 1, w[i] + 1}
        ends = {t for b in boxes for t in (b[i][0], b[i][1], b[i][0] - 1, b[i][1] + 1)}
        if len(ends) <= 40:
            vals |= ends
        cand.append(sorted(t for t in vals if bbox[i][0] <= t <= bbox[i][1]))
    best = None
    for wc in product(*cand):
        dcc = depth_count(boxes, list(wc))
        if best is None or dcc > best[0]:
            best = (dcc, list(wc))
    if Fr(best[0], tot) >= need:
        stats["deep_grid"] += 1
        stats["deep_min_depth_used"] = min(stats["deep_min_depth_used"], Fr(best[0], tot))
        return best[1], Fr(best[0], tot)
    # stage 3: every integer point of the bounding box (small boxes only)
    if bbsize <= 200000:
        for wc in product(*[range(lo, hi + 1) for lo, hi in bbox]):
            dcc = depth_count(boxes, list(wc))
            if dcc > best[0]:
                best = (dcc, list(wc))
        if Fr(best[0], tot) >= need:
            stats["deep_exhaustive"] += 1
            stats["deep_min_depth_used"] = min(stats["deep_min_depth_used"], Fr(best[0], tot))
            return best[1], Fr(best[0], tot)
        raise DeepPointMissing(f"exhaustive: max depth {best[0]}/{tot} < {need}")
    raise DeepPointMissing(f"searched grid: max depth {best[0]}/{tot} < {need}; bbox too large for exhaustive")


# ----------------------------------------------------------------------------------------------
# the recursive block search


def new_stats():
    return dict(calls=0, tests=0, max_tests=0, cuts=0, protected_checks=0, protected_cut=0,
                deep_calls=0, deep_median=0, deep_grid=0, deep_exhaustive=0, deep_audits=0,
                deep_min_depth_used=Fr(1), deep_audit_min_maxdepth=Fr(1), piece_fallback_z3=0,
                max_beta=0, max_boxes=0, max_level=0, tail_err_max_ratio=Fr(0), h_err_max_ratio=Fr(0),
                cut_frac_min=Fr(1), residual_max_ratio=Fr(0))


class Config:
    def __init__(self, k, check=True, flip=False, theta_factor=None, audit_deep=True, max_tests=None,
                 xstar_top=None, strict_hyp=True):
        self.k = k
        self.strict_hyp = strict_hyp  # False: record (not raise) violations of the tail-precision hypotheses
        self.xstar_top = xstar_top    # NEGATIVE CONTROL (non-contraction): protect this point at the root
        self.check = check            # per-call ground truth checks (protected point, residuals)
        self.flip = flip              # NEGATIVE CONTROL: cut H(c, h-c) instead of H(c, c-h)
        self.theta_factor = theta_factor  # NEGATIVE CONTROL: tail tolerance theta_factor*tau
        self.audit_deep = audit_deep  # exhaustive max-depth audit when the bounding box is small
        self.max_tests = max_tests


def exact_restricted_fp(G, prefix, u, stats):
    us = solve_piece(G, prefix, u)
    if us is None:
        stats["piece_fallback_z3"] += 1
        us, _ = z3_fixed_point(G, prefix, unique=False)
    return us


def block_call(G, prefix, tau, cfg, stats, level=0):
    """returns (u, ustar): u dyadic (free coordinates) with ||u - G(prefix,u)_free||_1 <= tau;
    ustar the exact restricted fixed point (only if cfg.check, else None)."""
    delta = G.delta
    require(delta > 0, "delta <= 0: no contraction gap, the algorithm is not applicable")
    stats["calls"] += 1
    stats["max_level"] = max(stats["max_level"], level)
    p = len(prefix)
    free = G.d - p
    kb = min(cfg.k, free)
    tail = free - kb
    theta = delta * delta * tau / 16 if cfg.theta_factor is None else cfg.theta_factor * tau
    e = delta * tau / 16
    beta = ceil_log2_ratio(16 * kb, delta * tau)
    N = 2 ** beta
    stats["max_beta"] = max(stats["max_beta"], beta)
    bprime = Fr(1, 2 * (kb + 1))
    boxes = [tuple((0, N) for _ in range(kb))]
    total0 = (N + 1) ** kb
    log = []   # per test: (w, c, y, ystar, h, v or None)
    z_known = None
    if level == 0 and cfg.xstar_top is not None:   # known root fixed point: check every cut at once
        z_known = [floor(t * N + Fr(1, 2)) for t in cfg.xstar_top[:kb]]
    ntests = 0
    while True:
        size = union_size(boxes)
        require(size >= 1, "candidate set emptied")
        stats["max_boxes"] = max(stats["max_boxes"], len(boxes))
        w, dep = deep_point(boxes, kb, stats, audit=cfg.audit_deep)
        c = [Fr(t, N) for t in w]
        if tail:
            y, ystar = block_call(G, list(prefix) + c, theta, cfg, stats, level + 1)
        else:
            y, ystar = [], []
        out = G.F(list(prefix) + c + y)
        h = out[p:p + kb]
        ntests += 1
        stats["tests"] += 1
        if cfg.max_tests and ntests > cfg.max_tests:
            raise CheckFailure("test cap exceeded")
        if l1(sub(h, c)) <= tau / 2:
            u = c + y
            res = l1(sub(u, out[p:]))
            stats["residual_max_ratio"] = max(stats["residual_max_ratio"], res / tau)
            require(res <= tau, f"returned residual {res} > tau {tau}")
            log.append((w, c, y, ystar, h, None))
            break
        v = sub(c, h) if not cfg.flip else sub(h, c)
        if z_known is not None and in_H(z_known, w, v):
            stats["protected_cut"] += 1
            raise CheckFailure(f"protected grid point z={z_known} cut at test {ntests} (root level)")
        newboxes, removed = cut_boxes(boxes, w, v)
        # a w of depth >= b' removes at least b'|C| points (here exactly what the cut removed)
        require(Fr(removed) >= bprime * size, "cut removed less than the depth guarantee")
        stats["cut_frac_min"] = min(stats["cut_frac_min"], Fr(removed, size))
        stats["cuts"] += 1
        log.append((w, c, y, ystar, h, v))
        boxes = newboxes
        # test bound: after t failed tests |C| <= (1-b')^t (N+1)^k and |C| >= 1 (z survives)
        require((1 - bprime) ** (ntests) * total0 >= 1 or not cfg.check,
                f"more failed tests ({ntests}) than the bound O(k^2 log N) allows")
    stats["max_tests"] = max(stats["max_tests"], ntests)
    if not cfg.check:
        return u, None
    # ---- per-call verification of the book's argument ----
    ustar = exact_restricted_fp(G, prefix, u, stats)
    if level == 0 and cfg.xstar_top is not None:
        ustar = list(cfg.xstar_top)
    require(ustar is not None, "no exact restricted fixed point found")
    require(l1(sub(u, ustar)) <= tau / delta, "a-posteriori bound ||u-u*|| <= tau/delta fails")
    xstar = ustar[:kb]
    z = [floor(t * N + Fr(1, 2)) for t in xstar]          # coordinatewise rounding
    rho = l1(sub([Fr(t, N) for t in z], xstar))
    require(rho <= Fr(kb, N) <= e, "rounding radius rho <= k/N <= e fails")
    for (w, c, y, ystar, h, v) in log:
        if tail:
            # tail precision: ||y - y(c)|| <= delta tau/16 and ||h - T(c)|| <= e
            Tc = G.F(list(prefix) + c + ystar)[p:p + kb]
            r1 = l1(sub(y, ystar)) / (delta * tau / 16)
            r2 = l1(sub(h, Tc)) / e
            stats["tail_err_max_ratio"] = max(stats["tail_err_max_ratio"], r1)
            stats["h_err_max_ratio"] = max(stats["h_err_max_ratio"], r2)
            if cfg.strict_hyp:
                require(r1 <= 1, "tail error ||y-y(c)|| > delta tau/16")
                require(r2 <= 1, "block error ||h-T(c)|| > e")
            else:
                stats["hyp_viol"] = stats.get("hyp_viol", 0) + (r1 > 1) + (r2 > 1)
        if v is not None:
            stats["protected_checks"] += 1
            if in_H(z, w, v):
                stats["protected_cut"] += 1
                raise CheckFailure(f"protected grid point z={z} cut at level {level} by H(w={w}, v)")
    require(in_boxes(z, boxes), "protected point not in the surviving candidate union")
    return u, ustar


def cf_recover(u, D):
    """the unique fraction with denominator <= D within 1/(8D^2) of u (Legendre: a convergent)."""
    p0, q0, p1, q1 = 0, 1, 1, 0
    x = Fr(u)
    best = None
    while True:
        a = x.numerator // x.denominator
        p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
        cand = Fr(p1, q1)
        if q1 <= D and abs(cand - u) <= Fr(1, 8 * D * D):
            best = cand
        if x == a or q1 > D:
            break
        x = 1 / (x - a)
    return best


def root_tau(delta, D):
    B = 0
    while Fr(1, 2 ** B) > delta / (8 * D * D):
        B += 1
    return Fr(1, 2 ** B), B


def solve_exact(G, k, D, cfg=None, tau=None):
    """the full algorithm: recursion at tau = 2^-B <= delta/(8D^2), then CF reconstruction and a
    final exact evaluation.  Returns (point or None, info)."""
    cfg = cfg or Config(k)
    stats = new_stats()
    require(G.delta > 0, "delta <= 0: no contraction gap, the algorithm is not applicable")
    if tau is None:
        tau, B = root_tau(G.delta, D)
    u, ustar = block_call(G, [], tau, cfg, stats)
    rec = [cf_recover(t, D) for t in u]
    ok = all(t is not None for t in rec) and G.F(rec) == rec
    return (rec if ok else None), dict(stats=stats, tau=tau, u=u, ustar=ustar, rec=rec)


# ----------------------------------------------------------------------------------------------
# abstract PL l1 contractions: F_i(x) = (1-delta) clip01(max(A_i x + b_i, A'_i x + b'_i)) + delta/2
# with sum_i max(|A_ih|, |A'_ih|) <= 1 for every column h  (so every piece has column sums <= 1-delta)


def make_abstract(rng, d, delta, density=1.0, unit=4):
    alpha = 1 - Fr(delta)
    A = [[Fr(0)] * d for _ in range(d)]
    A2 = [[Fr(0)] * d for _ in range(d)]
    for h in range(d):
        units = rng.randint(1, unit)       # column budget units/unit <= 1
        rows = [i for i in range(d) if rng.random() < density] or [rng.randrange(d)]
        for _ in range(units):
            i = rng.choice(rows)
            A[i][h] += Fr(1, unit)
        for i in range(d):
            m = A[i][h]
            A[i][h] = m * rng.choice((-1, 1))
            A2[i][h] = Fr(rng.randint(0, int(m * unit)), unit) * rng.choice((-1, 1))
    for h in range(d):
        assert sum(max(abs(A[i][h]), abs(A2[i][h])) for i in range(d)) <= 1
    b = [Fr(rng.randint(-4, 8), 8) for _ in range(d)]
    b2 = [Fr(rng.randint(-4, 8), 8) for _ in range(d)]
    dl = Fr(delta)

    def circuit(x, B):
        out = []
        for i in range(d):
            p1 = B.K(b[i])
            p2 = B.K(b2[i])
            for h in range(d):
                if A[i][h]:
                    p1 = p1 + B.K(A[i][h]) * x[h]
                if A2[i][h]:
                    p2 = p2 + B.K(A2[i][h]) * x[h]
            m = B.min(B.K(Fr(1)), B.max(B.K(Fr(0)), B.max(p1, p2)))
            out.append(B.K(alpha) * m + B.K(dl / 2))
        return out
    return PLMap(d, dl, circuit, name=f"abstract d={d} delta={dl}")


# ----------------------------------------------------------------------------------------------
# the game's l1 contraction (Sec. sec:contraction): exact constants from the book for a given g


class Game:
    def __init__(self, a, b, d, p, r, g):
        self.a, self.b, self.dg, self.p, self.r, self.g = a, b, d, p, r, Fr(g)
        n, m = len(d), len(p)
        self.n, self.m = n, m
        g = self.g
        bmax = max(max(row) for row in b)
        dp = [dj + g / 16 for dj in d]
        dbar = max(dp)
        sigma = kappa = g / 8
        inv = sum(1 / t for t in dp)
        eta = min(Fr(1), sigma / (1 + bmax), kappa / (4 * (1 + dbar) * (1 + inv)))
        delta = min(Fr(1, 8), eta * g / (8 * (1 + dbar)), g / (8 * (1 + bmax)))
        assert eta * dbar * inv <= kappa / 4 <= kappa * (1 - 2 * delta)   # (eq:ueopl-const)
        self.C = dict(bmax=bmax, dp=dp, dbar=dbar, sigma=sigma, kappa=kappa, eta=eta, delta=delta)
        self.subsets = [S for kk in range(1, n + 1) for S in __import__("itertools").combinations(range(n), kk)]
        self.map = PLMap(n + 1, delta, self.circuit, name=f"game n={n} m={m} r={r} g={g}")

    def _theta(self, uu, B):
        if B.name == "z3":      # max over subsets S of (sum_S u - 1)/|S|  (= the sorted-prefix formula)
            t = None
            for S in self.subsets:
                tt = (sum(uu[j] for j in S) - 1) / len(S)
                t = tt if t is None else B.max(t, tt)
            return t
        order = sorted(range(len(uu)), key=lambda j: _val(uu[j]), reverse=True)
        t, pre = None, 0
        for kk, j in enumerate(order, 1):
            pre = pre + uu[j]
            tt = (pre - 1) / kk
            t = tt if t is None else B.max(t, tt)
        return t

    def circuit(self, u, B, aux=None):
        n, m, C = self.n, self.m, self.C
        a, b, p = self.a, self.b, self.p
        sigma, kappa, eta, delta, dbar, dp = C["sigma"], C["kappa"], C["eta"], C["delta"], C["dbar"], C["dp"]
        x, q = u[:n], u[n]
        K = B.K
        w = [K(Fr(0))] * n
        flows = []
        for i in range(m):
            uu = [(K(a[i][j]) - K(b[i][j]) * x[j]) / sigma if b[i][j] else K(a[i][j] / sigma) for j in range(n)]
            th = self._theta(uu, B)
            y = [B.max(K(Fr(0)), uu[j] - th) for j in range(n)]
            flows.append([y[j] * p[i] for j in range(n)])
            for j in range(n):
                w[j] = w[j] + K(p[i]) * y[j]
        s = B.min(K(kappa), B.max(K(Fr(0)), q))
        hi = (1 - delta) * kappa
        lam = B.min(K(dbar), B.max(K(Fr(0)), (K(hi) - s) * (dbar / ((1 - 2 * delta) * kappa))))
        T = [B.min(K(Fr(1)), B.max(K(Fr(0)), x[j] + (w[j] - lam * (1 / dp[j])) * eta)) for j in range(n)]
        Runc = s + sum(x[1:], x[0]) - sum(T[1:], T[0])
        R = B.min(K(kappa), B.max(K(Fr(0)), Runc))
        out = [T[j] * (1 - delta) + K(delta * Fr(self.r, n)) for j in range(n)] + [R * (1 - delta) + K(delta * kappa / 2)]
        if aux is not None:
            aux.update(T=T, R=R, Runc=Runc, s=s, lam=lam, w=w, flows=flows)
        return out

    # --- decoding (Lemma ueopl-decoding) and exact BNE verification ---
    def decode(self, fp):
        """pattern from the fixed point, residual checks of the decoding lemma, the pattern LP
        solved exactly (z3, LRA), and the exact BNE conditions of Lemma cutoff(b)."""
        n, m, C, g = self.n, self.m, self.C, self.g
        aux = {}
        self.circuit(fp, FrB, aux)
        x, q = fp[:n], fp[n]
        z = aux["T"]
        delta, kappa, eta, dbar, bmax, sigma = C["delta"], C["kappa"], C["eta"], C["dbar"], C["bmax"], C["sigma"]
        chk = {}
        chk["q in [dk/2,(1-d/2)k]"] = delta * kappa / 2 <= q <= (1 - delta / 2) * kappa
        chk["R unclipped"] = 0 <= aux["Runc"] <= kappa and aux["R"] == aux["Runc"]
        chk["sum x + q = r + k/2"] = sum(x) + q == self.r + kappa / 2
        chk["|z-x|<=delta"] = all(abs(zj - xj) <= delta for zj, xj in zip(z, x))
        flows = aux["flows"]
        pay = Fr(0)
        for i in range(m):
            U = [self.a[i][j] - self.b[i][j] * z[j] for j in range(n)]
            for j in range(n):
                if flows[i][j] > 0:
                    pay = max(pay, max(U) - U[j])
        lam = aux["lam"]
        cut = Fr(0)
        for j in range(n):
            sc = self.dg[j] * aux["w"][j]
            if z[j] > 0:
                cut = max(cut, lam - sc)
            if z[j] < 1:
                cut = max(cut, sc - lam)
        chk["pay res <= sigma+2bmax delta"] = pay <= sigma + 2 * bmax * delta
        chk["cutoff res <= dbar delta/eta + g/16"] = cut <= dbar * delta / eta + g / 16
        chk["all residuals < g"] = max(pay, cut, abs(sum(z) - self.r)) < g
        # pattern LP
        allowed = {(i, j) for i in range(m) for j in range(n) if flows[i][j] > 0}
        label = ["zero" if zj == 0 else "one" if zj == 1 else "free" for zj in z]
        X = [z3.Real(f"X{j}") for j in range(n)]
        Fv = [[z3.Real(f"f{i}_{j}") for j in range(n)] for i in range(m)]
        V = [z3.Real(f"v{i}") for i in range(m)]
        L = z3.Real("lam")
        RV = lambda t: z3.RealVal(str(Fr(t)))
        s = z3.Solver()
        s.add(z3.Sum(X) == self.r)
        dmax = max(self.dg)
        s.add(L >= 0, L <= 1 + dmax)
        Wv = [z3.Sum([Fv[i][j] for i in range(m)]) for j in range(n)]
        for j in range(n):
            s.add(X[j] >= 0, X[j] <= 1)
        for i in range(m):
            s.add(z3.Sum(Fv[i]) == RV(self.p[i]))
            for j in range(n):
                s.add(Fv[i][j] >= 0, Fv[i][j] <= 1)
                U = RV(self.a[i][j]) - RV(self.b[i][j]) * X[j]
                s.add(V[i] >= U)
                if (i, j) in allowed:
                    s.add(V[i] == U)
                else:
                    s.add(Fv[i][j] == 0)
        for j in range(n):
            sc = RV(self.dg[j]) * Wv[j]
            if label[j] == "zero":
                s.add(X[j] == 0, sc <= L)
            elif label[j] == "one":
                s.add(X[j] == 1, sc >= L)
            else:
                s.add(sc == L)
        lp = s.check()
        chk["pattern LP feasible"] = lp == z3.sat
        bne = None
        if lp == z3.sat:
            M = s.model()
            xs = [zfr(M.eval(t, model_completion=True)) for t in X]
            fs = [[zfr(M.eval(t, model_completion=True)) for t in row] for row in Fv]
            chk["exact BNE"] = verify_bne(self, xs, fs)
            bne = (xs, fs)
        return chk, bne


def verify_bne(game, x, f):
    """Lemma cutoff(b), exact: budget, bounds, row sums; f_ij>0 => U_ij = V_i; a cutoff lambda with
    x_j>0 => d_j w_j >= lambda and x_j<1 => d_j w_j <= lambda."""
    n, m = game.n, game.m
    if sum(x) != game.r or any(t < 0 or t > 1 for t in x):
        return False
    for i in range(m):
        if sum(f[i]) != game.p[i] or any(t < 0 for t in f[i]):
            return False
        U = [game.a[i][j] - game.b[i][j] * x[j] for j in range(n)]
        if any(f[i][j] > 0 and U[j] != max(U) for j in range(n)):
            return False
    w = [sum(f[i][j] for i in range(m)) for j in range(n)]
    pi = [game.dg[j] * w[j] for j in range(n)]
    lo = max([pi[j] for j in range(n) if x[j] < 1], default=None)   # lambda >= every unsaturated score
    hi = min([pi[j] for j in range(n) if x[j] > 0], default=None)   # lambda <= every covered score
    return lo is None or hi is None or lo <= hi


def random_game(rng, n, m, r=None):
    a = [[Fr(rng.randint(-4, 4), 2) for _ in range(n)] for _ in range(m)]
    b = [[Fr(rng.randint(0, 4), 2) for _ in range(n)] for _ in range(m)]
    b[0][rng.randrange(n)] = Fr(0)                 # a zero slope
    d = [Fr(rng.randint(0, 3), 2) for _ in range(n)]
    d[rng.randrange(n)] = Fr(0)                    # a zero gain
    if all(t == 0 for t in d):
        d[0] = Fr(1)
    ws = [rng.randint(1, 4) for _ in range(m)]
    p = [Fr(t, sum(ws)) for t in ws]
    if r is None:
        r = rng.randint(1, n - 1)
    return a, b, d, p, r


# ----------------------------------------------------------------------------------------------
# self-tests of the geometric primitives


def selftest_depth(rng, trials=300):
    """depth formula (generic-v families) == direct min over all integer v in [-4,4]^k."""
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 3)
        boxes = []
        for _ in range(rng.randint(1, 3)):
            b = []
            for _ in range(k):
                lo = rng.randint(0, 5)
                b.append((lo, lo + rng.randint(0, 2)))
            boxes.append(tuple(b))
        # make disjoint by keeping only boxes not intersecting earlier ones
        dis = []
        for b in boxes:
            if all(any(b[i][1] < c[i][0] or c[i][1] < b[i][0] for i in range(k)) for c in dis):
                dis.append(b)
        w = [rng.randint(0, 8) for _ in range(k)]
        if depth_count(dis, w) != depth_count_bruteforce_v(dis, w):
            bad += 1
    return bad


def selftest_halfspace(rng, trials=5000):
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 4)
        z = [Fr(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(k)]
        c = [Fr(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(k)]
        if rng.random() < 0.3:
            for i in range(k):
                if rng.random() < 0.5:
                    z[i] = c[i]
        v = [Fr(rng.randint(-3, 3), rng.randint(1, 2)) for _ in range(k)]
        if not any(v):
            continue
        bad += in_H(z, c, v) != in_H_definition(z, c, v)
    return bad


def selftest_cut(rng, trials=300):
    """cut_boxes == pointwise removal by the sign formula, on small grids."""
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 3)
        Nn = rng.randint(1, 6)
        boxes = [tuple((0, Nn) for _ in range(k))]
        pts = set(product(range(Nn + 1), repeat=k))
        for _ in range(rng.randint(1, 4)):
            w = [rng.randint(-1, Nn + 1) for _ in range(k)]
            v = [Fr(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(k)]
            if not any(v):
                continue
            boxes, rem = cut_boxes(boxes, w, v)
            before = len(pts)
            pts = {z for z in pts if not in_H(z, w, v)}
            if rem != before - len(pts):
                bad += 1
        got = {z for b in boxes for z in product(*[range(lo, hi + 1) for lo, hi in b])}
        if got != pts or union_size(boxes) != len(pts):
            bad += 1
    return bad
