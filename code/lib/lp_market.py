"""Two-group affine matching market: exact equilibrium machinery.

Model (reservations at zero):
  buyers i, mass p_i>0; goods j, capacity c_j>0; utility a_ij - b_ij P_j, b_ij>0.
  Equilibrium (P>=0, v>=0, f>=0):
   (i)  v_i >= a_ij - b_ij P_j for all pairs,
   (ii) f_ij>0 only on tight pairs,
   (iii) sum_j f_ij <= p_i, equality if v_i>0,
   (iv) sum_i f_ij <= c_j, equality if P_j>0.
Two-group: group 1 shares slope row beta_j; group 2 has slope 1.
All arithmetic Fractions.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from itertools import combinations
import ratlp

F = Fraction
ZERO, ONE = F(0), F(1)


class Inst:
    def __init__(self, c, beta, g1, g2, name=''):
        """c: caps, beta: group-1 slope row, g1/g2: lists of (mass, [intercepts])."""
        self.n = len(c)
        self.c = [F(x) for x in c]
        self.beta = [F(x) for x in beta]
        assert len(self.beta) == self.n
        self.g1 = [(F(p), [F(x) for x in a]) for p, a in g1]
        self.g2 = [(F(p), [F(x) for x in a]) for p, a in g2]
        self.name = name
        # unified buyer list: (p, a_row, b_row, group)
        self.buyers = [(p, a, self.beta, 1) for p, a in self.g1] + \
                      [(p, a, [ONE] * self.n, 2) for p, a in self.g2]
        self.m = len(self.buyers)
        assert all(x > 0 for x in self.c) and all(x > 0 for x in self.beta)
        assert all(p > 0 for p, _, _, _ in self.buyers)

    def util(self, i, j, P):
        p_, a, b, _ = self.buyers[i]
        return a[j] - b[j] * P[j]

    def key(self):
        return (tuple(self.c), tuple(self.beta),
                tuple((p, tuple(a)) for p, a in self.g1),
                tuple((p, tuple(a)) for p, a in self.g2))

    def __repr__(self):
        return (f"Inst({self.name}: n={self.n} c={[str(x) for x in self.c]} "
                f"beta={[str(x) for x in self.beta]} "
                f"g1={[(str(p), [str(x) for x in a]) for p, a in self.g1]} "
                f"g2={[(str(p), [str(x) for x in a]) for p, a in self.g2]})")


def structure_at(inst, P):
    """At price vector P: v_i, tight pair set, flags. Exact."""
    P = [F(x) for x in P]
    v = []
    tight = []  # list over buyers of list of tight goods
    for i in range(inst.m):
        us = [inst.util(i, j, P) for j in range(inst.n)]
        vi = max([ZERO] + us)
        v.append(vi)
        tight.append([j for j in range(inst.n) if us[j] == vi])
    return {'P': P, 'v': v, 'tight': tight,
            'vpos': [vi > 0 for vi in v], 'ppos': [pj > 0 for pj in P]}


def flow_lp(inst, st, split=None, objective_dir=None, want_farkas=False):
    """Feasibility/optimization of equilibrium flows at structure st.
    Variables: f_ij for tight pairs. split: optional list s_j => add
    sum_{i in G1, (i,j) tight} f_ij = s_j for all j.
    objective_dir: optional direction d (len n): maximize sum_j d_j * (G1 load at j).
    Returns ratlp result + 'pairs' + per-good G1 loads if optimal."""
    pairs = [(i, j) for i in range(inst.m) for j in st['tight'][i]]
    idx = {pr: k for k, pr in enumerate(pairs)}
    nv = len(pairs)
    A_eq, b_eq, A_ub, b_ub = [], [], [], []
    for i in range(inst.m):
        row = [ZERO] * nv
        for j in st['tight'][i]:
            row[idx[(i, j)]] = ONE
        if st['vpos'][i]:
            A_eq.append(row); b_eq.append(inst.buyers[i][0])
        else:
            A_ub.append(row); b_ub.append(inst.buyers[i][0])
    for j in range(inst.n):
        row = [ZERO] * nv
        for (i, jj), k in idx.items():
            if jj == j:
                row[k] = ONE
        if st['ppos'][j]:
            A_eq.append(row); b_eq.append(inst.c[j])
        else:
            A_ub.append(row); b_ub.append(inst.c[j])
    if split is not None:
        for j in range(inst.n):
            row = [ZERO] * nv
            for (i, jj), k in idx.items():
                if jj == j and inst.buyers[i][3] == 1:
                    row[k] = ONE
            A_eq.append(row); b_eq.append(F(split[j]))
    obj = None
    if objective_dir is not None:
        obj = [ZERO] * nv
        for (i, jj), k in idx.items():
            if inst.buyers[i][3] == 1:
                obj[k] = F(objective_dir[jj])
    res = ratlp.solve(nv, A_eq, b_eq, A_ub, b_ub, obj=obj,
                      maximize=True, want_farkas=want_farkas)
    res['pairs'] = pairs
    if res['status'] == 'optimal':
        f = {}
        for k, pr in enumerate(pairs):
            if res['x'][k] != 0:
                f[pr] = res['x'][k]
        res['flow'] = f
        res['g1load'] = g1_loads(inst, f)
    return res


def g1_loads(inst, f):
    s = [ZERO] * inst.n
    for (i, j), val in f.items():
        if inst.buyers[i][3] == 1:
            s[j] += val
    return s


def loads(inst, f):
    w = [ZERO] * inst.n
    for (i, j), val in f.items():
        w[j] += val
    return w


def check_equilibrium(inst, P, v, f, require=True):
    """Full exact validation of an equilibrium certificate. f: dict (i,j)->mass."""
    P = [F(x) for x in P]; v = [F(x) for x in v]
    errs = []
    if any(x < 0 for x in P): errs.append('P negative')
    if any(x < 0 for x in v): errs.append('v negative')
    for i in range(inst.m):
        for j in range(inst.n):
            if v[i] < inst.util(i, j, P):
                errs.append(f'stability violated at ({i},{j})')
    for (i, j), val in f.items():
        if val < 0: errs.append(f'flow negative at ({i},{j})')
        if val > 0 and v[i] != inst.util(i, j, P):
            errs.append(f'flow on non-tight pair ({i},{j})')
    for i in range(inst.m):
        rs = sum(val for (ii, j), val in f.items() if ii == i)
        if rs > inst.buyers[i][0]: errs.append(f'row {i} oversupplied')
        if v[i] > 0 and rs != inst.buyers[i][0]:
            errs.append(f'row {i} has v>0 but not filled')
    w = loads(inst, f)
    for j in range(inst.n):
        if w[j] > inst.c[j]: errs.append(f'col {j} over capacity')
        if P[j] > 0 and w[j] != inst.c[j]:
            errs.append(f'col {j} has P>0 but not filled')
    ok = not errs
    if require and not ok:
        raise AssertionError('; '.join(errs))
    return ok, errs


def derive_v(inst, P):
    return structure_at(inst, P)['v']


# ---------------- OPT_g transportation LPs ----------------

def opt_group(inst, group, caps, certify=False):
    """OPT_g(caps) = max sum a_ij f_ij st rows<=p (group g only), cols<=caps, f>=0.
    If certify: also solve the dual and assert equal values; return (val, primal, dual)."""
    bs = [(p, a) for p, a, b, g in inst.buyers if g == group]
    mg = len(bs); n = inst.n
    nv = mg * n
    A_ub, b_ub = [], []
    for i in range(mg):
        row = [ZERO] * nv
        for j in range(n):
            row[i * n + j] = ONE
        A_ub.append(row); b_ub.append(bs[i][0])
    for j in range(n):
        row = [ZERO] * nv
        for i in range(mg):
            row[i * n + j] = ONE
        A_ub.append(row); b_ub.append(F(caps[j]))
    obj = [bs[i][1][j] for i in range(mg) for j in range(n)]
    res = ratlp.solve(nv, [], [], A_ub, b_ub, obj=obj, maximize=True)
    assert res['status'] == 'optimal'
    val = res['value']
    primal = [[res['x'][i * n + j] for j in range(n)] for i in range(mg)]
    dual = None
    if certify:
        # dual: min p.v + caps.Q st v_i + Q_j >= a_ij, v,Q >= 0
        nvd = mg + n
        A2, b2 = [], []
        for i in range(mg):
            for j in range(n):
                row = [ZERO] * nvd
                row[i] = -ONE; row[mg + j] = -ONE
                A2.append(row); b2.append(-bs[i][1][j])
        obj2 = [bs[i][0] for i in range(mg)] + [F(caps[j]) for j in range(n)]
        res2 = ratlp.solve(nvd, [], [], A2, b2, obj=obj2, maximize=False)
        assert res2['status'] == 'optimal'
        assert res2['value'] == val, f'duality gap: {val} vs {res2["value"]}'
        dual = (res2['x'][:mg], res2['x'][mg:])
    return val, primal, dual


# ---------------- C2 fixed-split LP ----------------

def c2_lp(inst, s, want_farkas=False, opt_vals=None):
    """Fixed-split LP (claim C2): variables P (n), v1 (m1), v2 (m2), all >= 0.
      stability both groups (all pairs);
      sum p v1 + sum_j beta_j s_j P_j <= OPT1(s);
      sum p v2 + sum_j (c_j-s_j) P_j <= OPT2(c-s).
    s must satisfy 0 <= s_j <= c_j. Returns dict with feasibility, witness,
    optionally farkas, and the OPT values used."""
    n = inst.n
    s = [F(x) for x in s]
    assert all(0 <= s[j] <= inst.c[j] for j in range(n)), 'split out of box'
    if opt_vals is None:
        o1, _, _ = opt_group(inst, 1, s)
        o2, _, _ = opt_group(inst, 2, [inst.c[j] - s[j] for j in range(n)])
    else:
        o1, o2 = opt_vals
    m1, m2 = len(inst.g1), len(inst.g2)
    nv = n + m1 + m2  # P, v1, v2
    A_ub, b_ub = [], []
    for i1, (p, a) in enumerate(inst.g1):
        for j in range(n):
            row = [ZERO] * nv
            row[j] = -inst.beta[j]
            row[n + i1] = -ONE
            A_ub.append(row); b_ub.append(-a[j])   # a_ij - beta_j P_j - v1_i <= 0
    for i2, (p, a) in enumerate(inst.g2):
        for j in range(n):
            row = [ZERO] * nv
            row[j] = -ONE
            row[n + m1 + i2] = -ONE
            A_ub.append(row); b_ub.append(-a[j])
    row = [ZERO] * nv
    for j in range(n):
        row[j] = inst.beta[j] * s[j]
    for i1, (p, a) in enumerate(inst.g1):
        row[n + i1] = p
    A_ub.append(row); b_ub.append(o1)
    row = [ZERO] * nv
    for j in range(n):
        row[j] = inst.c[j] - s[j]
    for i2, (p, a) in enumerate(inst.g2):
        row[n + m1 + i2] = p
    A_ub.append(row); b_ub.append(o2)
    res = ratlp.solve(nv, [], [], A_ub, b_ub, want_farkas=want_farkas)
    out = {'feasible': res['status'] == 'optimal', 'opt1': o1, 'opt2': o2,
           'A_ub': A_ub, 'b_ub': b_ub, 'nv': nv}
    if out['feasible']:
        out['P'] = res['x'][:n]
        out['v1'] = res['x'][n:n + m1]
        out['v2'] = res['x'][n + m1:]
    elif 'farkas' in res:
        out['farkas'] = res['farkas']
    return out


def equilibrium_from_c2(inst, s, c2):
    """Build a full equilibrium from a feasible C2 witness; check it; return
    (P, v, f, g1loads). Flows: optimal primals of the two capacity-split LPs."""
    n = inst.n
    s = [F(x) for x in s]
    P = c2['P']
    _, f1, _ = opt_group(inst, 1, s)
    _, f2, _ = opt_group(inst, 2, [inst.c[j] - s[j] for j in range(n)])
    f = {}
    for i1 in range(len(inst.g1)):
        for j in range(n):
            if f1[i1][j] != 0:
                f[(i1, j)] = f1[i1][j]
    off = len(inst.g1)
    for i2 in range(len(inst.g2)):
        for j in range(n):
            if f2[i2][j] != 0:
                f[(off + i2, j)] = f2[i2][j]
    v = derive_v(inst, P)
    # the C2 v's need not equal derived v; equilibrium needs the derived ones?
    # Use C2's (v1,v2) directly: they satisfy stability; CS used them. Check both.
    v_c2 = list(c2['v1']) + list(c2['v2'])
    ok, errs = check_equilibrium(inst, P, v_c2, f, require=False)
    if not ok:
        return None, errs
    return (P, v_c2, f, g1_loads(inst, f)), []


# ---------------- arrangement enumeration ----------------

def _norm_hyp(coef, const):
    """Normalize hyperplane coef.P = const for dedup."""
    items = [c for c in coef if c != 0]
    if not items:
        return None
    lead = items[0]
    coef = tuple(c / lead for c in coef)
    const = const / lead
    if lead < 0:
        pass  # already divided; sign fixed by leading 1
    return (coef, const)


def hyperplanes(inst):
    """All structure-changing hyperplanes in price space + box planes.
    Returns list of (coef tuple, const) meaning coef.P = const."""
    n = inst.n
    H = {}
    def add(coef, const):
        nh = _norm_hyp(list(coef), const)
        if nh is not None:
            H[nh] = True
    for i in range(inst.m):
        p, a, b, g = inst.buyers[i]
        for j in range(n):
            # u_ij = 0: a_j - b_j P_j = 0
            coef = [ZERO] * n; coef[j] = b[j]
            add(coef, a[j])
            for k in range(j + 1, n):
                # u_ij = u_ik: -b_j P_j + b_k P_k = a_k - a_j
                coef = [ZERO] * n
                coef[j] = -b[j]; coef[k] = b[k]
                add(coef, a[k] - a[j])
    pmax = price_box(inst)
    for j in range(n):
        coef = [ZERO] * n; coef[j] = ONE
        add(coef, ZERO)
        add(coef, pmax[j])
    return list(H.keys()), pmax


def price_box(inst):
    """Pmax_j = max(0, max_i a_ij / b_ij); every equilibrium P in prod [0,Pmax]."""
    out = []
    for j in range(inst.n):
        best = ZERO
        for p, a, b, g in inst.buyers:
            val = a[j] / b[j]
            if val > best:
                best = val
        out.append(best)
    return out


def _solve_square(rows, rhs):
    """Solve square linear system exactly; None if singular."""
    n = len(rhs)
    M = [list(rows[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] != 0:
                piv = r; break
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                mult = M[r][col]
                M[r] = [M[r][k] - mult * M[col][k] for k in range(n + 1)]
    return [M[i][n] for i in range(n)]


def arrangement_vertices(inst):
    """All intersection points of n hyperplanes inside the price box."""
    hyps, pmax = hyperplanes(inst)
    n = inst.n
    pts = {}
    for sub in combinations(range(len(hyps)), n):
        rows = [hyps[k][0] for k in sub]
        rhs = [hyps[k][1] for k in sub]
        sol = _solve_square(rows, rhs)
        if sol is None:
            continue
        if all(ZERO <= sol[j] <= pmax[j] for j in range(n)):
            pts[tuple(sol)] = True
    return list(pts.keys()), hyps, pmax


def enumerate_equilibrium_vertices(inst):
    """Returns dict: vertices (list of P tuples that are equilibrium prices,
    with structure + a witness flow), all_vertices, hyps."""
    pts, hyps, pmax = arrangement_vertices(inst)
    eqv = []
    for P in pts:
        st = structure_at(inst, list(P))
        res = flow_lp(inst, st)
        if res['status'] == 'optimal':
            eqv.append({'P': list(P), 'st': st, 'flow': res['flow'],
                        'g1load': res['g1load']})
    return {'eqv': eqv, 'all_vertices': pts, 'hyps': hyps, 'pmax': pmax}


def hyp_eval(h, P):
    coef, const = h
    return sum(coef[j] * P[j] for j in range(len(P))) - const


def segment_single_face(hyps, P, Q):
    """True if open segment (P,Q) lies in a single arrangement face
    (no hyperplane strictly separates the endpoints)."""
    for h in hyps:
        a, b = hyp_eval(h, P), hyp_eval(h, Q)
        if (a > 0 and b < 0) or (a < 0 and b > 0):
            return False
    return True


def connectivity(inst, enum):
    """Graph on equilibrium vertices: edge if open segment in one face and
    midpoint structure flow-feasible. Returns list of components (sets of idx)."""
    eqv = enum['eqv']; hyps = enum['hyps']
    k = len(eqv)
    adj = [[] for _ in range(k)]
    for ia in range(k):
        for ib in range(ia + 1, k):
            P, Q = eqv[ia]['P'], eqv[ib]['P']
            if not segment_single_face(hyps, P, Q):
                continue
            mid = [(P[j] + Q[j]) / 2 for j in range(inst.n)]
            st = structure_at(inst, mid)
            if flow_lp(inst, st)['status'] == 'optimal':
                adj[ia].append(ib); adj[ib].append(ia)
    seen = [False] * k
    comps = []
    for s0 in range(k):
        if seen[s0]:
            continue
        stack = [s0]; comp = set()
        seen[s0] = True
        while stack:
            u = stack.pop(); comp.add(u)
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = True; stack.append(w)
        comps.append(comp)
    return comps


# ---------------- split set S* ----------------

def directions(n, rich=False):
    """Direction vectors for support sampling."""
    out = []
    vals = (-1, 0, 1) if not rich else (-2, -1, 0, 1, 2)
    def rec(pref):
        if len(pref) == n:
            if any(x != 0 for x in pref):
                out.append(list(pref))
            return
        for v in vals:
            rec(pref + [v])
    rec([])
    return out


def split_samples(inst, enum, rich=False):
    """Sample extreme/exposed points of each vertex-piece S_V by optimizing
    direction vectors over the flow polytope. Returns list of split tuples."""
    pts = {}
    for vx in enum['eqv']:
        st = vx['st']
        for d in directions(inst.n, rich):
            res = flow_lp(inst, st, objective_dir=d)
            if res['status'] == 'optimal':
                pts[tuple(res['g1load'])] = True
        pts[tuple(vx['g1load'])] = True
    return [list(x) for x in pts.keys()]


def s_in_Sload(inst, enum, s):
    """Exact membership: exists equilibrium with group-1 load vector exactly s.
    Complete: every equilibrium flow is feasible at some arrangement vertex."""
    for vx in enum['eqv']:
        res = flow_lp(inst, vx['st'], split=s)
        if res['status'] == 'optimal':
            return True, vx
    return False, None


def s_in_Scap(inst, s):
    out = c2_lp(inst, s)
    return out['feasible'], out


def piece_support(inst, st, d):
    """max over the flow polytope at structure st of d . g1load; None if infeasible."""
    res = flow_lp(inst, st, objective_dir=d)
    if res['status'] != 'optimal':
        return None, None
    val = sum(F(d[j]) * res['g1load'][j] for j in range(inst.n))
    return val, res['g1load']
