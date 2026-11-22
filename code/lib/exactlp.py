# Copied verbatim from runs/20261121T205429Z/complexity/exactlp.py (stdlib exact simplex, Bland rule).
"""Exact rational linear programming (dense two-phase simplex, Bland's rule).

minimize c.x  subject to  A_ub x <= b_ub,  A_eq x == b_eq,  lo <= x <= hi
All data are converted to fractions.Fraction.  lo/hi entries may be None (= -inf / +inf).
Returns (status, x, value) with status in {"optimal", "infeasible", "unbounded"}.
Stdlib only.  Intended for small instances (tens of variables).
"""
from fractions import Fraction as F


def _simplex_std(A, b, c, basis=None):
    """Solve min c.x, A x = b, x >= 0 with b >= 0 already, using a full tableau.
    If basis is None, run phase 1 with artificials.  Returns (status, x, basis)."""
    m = len(A)
    n = len(c)
    # Phase 1
    # tableau rows: [A | I_art | b]
    T = [list(map(F, A[i])) + [F(1) if k == i else F(0) for k in range(m)] + [F(b[i])] for i in range(m)]
    basis = [n + i for i in range(m)]
    ncols = n + m

    def pivot(r, col):
        pv = T[r][col]
        if pv != 1:
            T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][col] != 0:
                fac = T[i][col]
                Ti = T[i]
                Tr = T[r]
                T[i] = [Ti[k] - fac * Tr[k] for k in range(ncols + 1)]
        basis[r] = col

    def run(cost, allowed):
        # cost: list of length ncols
        while True:
            # reduced costs
            cb = [cost[basis[i]] for i in range(m)]
            enter = None
            for j in range(ncols):
                if not allowed[j] or j in basis:
                    continue
                rc = cost[j] - sum(cb[i] * T[i][j] for i in range(m) if T[i][j] != 0)
                if rc < 0:
                    enter = j
                    break  # Bland: smallest index
            if enter is None:
                return "optimal"
            # ratio test (Bland tie-break on basis index)
            best = None
            for i in range(m):
                a = T[i][enter]
                if a > 0:
                    ratio = T[i][-1] / a
                    if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                        best = (ratio, i)
            if best is None:
                return "unbounded"
            pivot(best[1], enter)

    cost1 = [F(0)] * n + [F(1)] * m
    allowed = [True] * ncols
    run(cost1, allowed)
    val1 = sum(T[i][-1] for i in range(m) if basis[i] >= n)
    if val1 != 0:
        return "infeasible", None, None
    # drive artificials out of basis
    for i in range(m):
        if basis[i] >= n:
            col = None
            for j in range(n):
                if T[i][j] != 0:
                    col = j
                    break
            if col is not None:
                pivot(i, col)
            # else: redundant row, keep artificial at zero (it will stay 0)
    allowed = [True] * n + [False] * m
    cost2 = [F(v) for v in c] + [F(0)] * m
    st = run(cost2, allowed)
    if st == "unbounded":
        return "unbounded", None, None
    x = [F(0)] * n
    for i in range(m):
        if basis[i] < n:
            x[basis[i]] = T[i][-1]
    return "optimal", x, list(basis)


def solve_lp(c, A_ub=None, b_ub=None, A_eq=None, b_eq=None, lo=None, hi=None):
    nv = len(c)
    A_ub = A_ub or []
    b_ub = b_ub or []
    A_eq = A_eq or []
    b_eq = b_eq or []
    if lo is None:
        lo = [F(0)] * nv
    if hi is None:
        hi = [None] * nv
    # build transformed variables
    # each original var j -> list of (newindex, coef) and constant offset
    cols = []  # list of (orig j, coef)
    expr = []  # for each original var: (offset, [(col, coef)])
    extra_rows = []  # (dict col->coef, rhs) equality rows from upper bounds
    for j in range(nv):
        l, h = lo[j], hi[j]
        if l is not None:
            l = F(l)
            k = len(cols)
            cols.append((j, 1))
            expr.append((l, [(k, F(1))]))
            if h is not None:
                h = F(h)
                if h < l:
                    return "infeasible", None, None
                ks = len(cols)
                cols.append((None, 0))  # slack
                extra_rows.append(({k: F(1), ks: F(1)}, h - l))
        elif h is not None:
            h = F(h)
            k = len(cols)
            cols.append((j, -1))
            expr.append((h, [(k, F(-1))]))
        else:
            k1 = len(cols)
            cols.append((j, 1))
            k2 = len(cols)
            cols.append((j, -1))
            expr.append((F(0), [(k1, F(1)), (k2, F(-1))]))
    rows = []
    rhs = []
    nslack_ub = len(A_ub)
    base_cols = len(cols)
    total_cols = base_cols + nslack_ub

    def lin(row):
        d = {}
        const = F(0)
        for j, a in enumerate(row):
            a = F(a)
            if a == 0:
                continue
            off, terms = expr[j]
            const += a * off
            for (k, cf) in terms:
                d[k] = d.get(k, F(0)) + a * cf
        return d, const

    for r, (row, bb) in enumerate(zip(A_ub, b_ub)):
        d, const = lin(row)
        d[base_cols + r] = F(1)
        rows.append(d)
        rhs.append(F(bb) - const)
    for row, bb in zip(A_eq, b_eq):
        d, const = lin(row)
        rows.append(d)
        rhs.append(F(bb) - const)
    for d, h in extra_rows:
        rows.append(dict(d))
        rhs.append(h)
    # objective
    dc, cconst = lin(c)
    cvec = [F(0)] * total_cols
    for k, v in dc.items():
        cvec[k] = v
    A = []
    b = []
    for d, r in zip(rows, rhs):
        rowv = [F(0)] * total_cols
        for k, v in d.items():
            rowv[k] = v
        if r < 0:
            rowv = [-v for v in rowv]
            r = -r
        A.append(rowv)
        b.append(r)
    if not A:
        # no constraints: check boundedness
        for k in range(total_cols):
            if cvec[k] < 0:
                return "unbounded", None, None
        xs = [F(0)] * total_cols
    else:
        st, xs, _ = _simplex_std(A, b, cvec)
        if st != "optimal":
            return st, None, None
    x = []
    for j in range(nv):
        off, terms = expr[j]
        x.append(off + sum(cf * xs[k] for k, cf in terms))
    val = sum(F(c[j]) * x[j] for j in range(nv))
    return "optimal", x, val


if __name__ == "__main__":
    # tiny tests
    st, x, v = solve_lp([-1, -1], A_ub=[[1, 2], [3, 1]], b_ub=[4, 6])
    print(st, x, v)  # optimum at (8/5, 6/5), value -14/5
    st, x, v = solve_lp([1, 0], A_eq=[[1, 1]], b_eq=[1], lo=[None, 0], hi=[None, F(1, 3)])
    print(st, x, v)  # x0 = 2/3
    st, x, v = solve_lp([1], A_ub=[[1]], b_ub=[-1])
    print(st, x, v)  # infeasible
    st, x, v = solve_lp([-1], lo=[0], hi=[None])
    print(st)  # unbounded
