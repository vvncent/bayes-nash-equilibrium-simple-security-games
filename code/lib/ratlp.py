"""Exact rational LP: two-phase simplex with Bland's rule, Fraction arithmetic.

Variables are x >= 0.  System:  A_eq x = b_eq,  A_ub x <= b_ub.
solve(...) returns dict with status in {'optimal','infeasible','unbounded'}.
On 'infeasible' (when want_farkas=True) returns a VERIFIED Farkas certificate:
  y_eq (free), y_ub >= 0 with  y_eq A_eq + y_ub A_ub >= 0 (componentwise)
  and y_eq.b_eq + y_ub.b_ub < 0.
No floats anywhere.
"""
from fractions import Fraction

F = Fraction
ZERO = F(0)
ONE = F(1)


def _simplex(T, basis, nrows, ncols, cost_row, allowed):
    """Min-simplex on tableau T (nrows x (ncols+1), last col = rhs).
    cost_row: list length ncols+1 (reduced costs maintained by pivoting).
    allowed[j] True if column j may enter. Bland's rule. Returns
    ('optimal', None) or ('unbounded', enter_col). Mutates T, basis, cost_row."""
    while True:
        enter = -1
        for j in range(ncols):
            if allowed[j] and cost_row[j] < 0:
                enter = j
                break
        if enter < 0:
            return ('optimal', None)
        # ratio test (Bland: among min ratios pick smallest basis var index)
        leave = -1
        best = None
        for r in range(nrows):
            a = T[r][enter]
            if a > 0:
                ratio = T[r][ncols] / a
                if best is None or ratio < best or (ratio == best and basis[r] < basis[leave]):
                    best = ratio
                    leave = r
        if leave < 0:
            return ('unbounded', enter)
        # pivot
        piv = T[leave][enter]
        row = T[leave]
        if piv != 1:
            for j in range(ncols + 1):
                if row[j]:
                    row[j] /= piv
            row[enter] = ONE
        for r in range(nrows):
            if r != leave:
                m = T[r][enter]
                if m:
                    tr = T[r]
                    for j in range(ncols + 1):
                        if row[j]:
                            tr[j] -= m * row[j]
                    tr[enter] = ZERO
        m = cost_row[enter]
        if m:
            for j in range(ncols + 1):
                if row[j]:
                    cost_row[j] -= m * row[j]
            cost_row[enter] = ZERO
        basis[leave] = enter


def solve(nvars, A_eq, b_eq, A_ub, b_ub, obj=None, maximize=False, want_farkas=False, _no_recurse=False):
    """All entries Fractions/ints. A_eq: list of rows (len nvars). obj: len nvars or None (feasibility).
    Returns dict: status; x (list of Fractions) and value on optimal;
    farkas=(y_eq, y_ub) verified on infeasible when requested."""
    A_eq = [list(map(F, r)) for r in A_eq]
    b_eq = list(map(F, b_eq))
    A_ub = [list(map(F, r)) for r in A_ub]
    b_ub = list(map(F, b_ub))
    me, mu = len(A_eq), len(A_ub)
    m = me + mu
    # columns: x (nvars) | slacks (mu) | artificials (m)
    ncols = nvars + mu + m
    T = []
    rows = []
    for i in range(me):
        rows.append((A_eq[i][:], b_eq[i], None))
    for i in range(mu):
        rows.append((A_ub[i][:], b_ub[i], i))
    for r_i, (arow, b, slack) in enumerate(rows):
        sign = ONE
        if b < 0:
            sign = -ONE
        full = [sign * v for v in arow] + [ZERO] * (mu + m)
        if slack is not None:
            full[nvars + slack] = sign
        full[nvars + mu + r_i] = ONE
        full.append(sign * b)
        T.append(full)
    basis = [nvars + mu + i for i in range(m)]
    # phase 1 cost: sum artificials -> reduced cost row = -(sum of rows) over non-artificial cols
    cost = [ZERO] * (ncols + 1)
    for r in range(m):
        for j in range(ncols + 1):
            if T[r][j]:
                cost[j] -= T[r][j]
    for r in range(m):
        cost[nvars + mu + r] = ZERO
    allowed = [True] * ncols
    st, _ = _simplex(T, basis, m, ncols, cost, allowed)
    assert st == 'optimal'
    p1val = -cost[ncols]
    if p1val > 0:
        res = {'status': 'infeasible'}
        if want_farkas and not _no_recurse:
            res['farkas'] = _farkas(nvars, A_eq, b_eq, A_ub, b_ub)
        return res
    # drive artificials out of basis where possible
    for r in range(m):
        if basis[r] >= nvars + mu:
            piv_col = -1
            for j in range(nvars + mu):
                if T[r][j] != 0:
                    piv_col = j
                    break
            if piv_col >= 0:
                piv = T[r][piv_col]
                for j in range(ncols + 1):
                    if T[r][j]:
                        T[r][j] /= piv
                for r2 in range(m):
                    if r2 != r and T[r2][piv_col]:
                        mmul = T[r2][piv_col]
                        for j in range(ncols + 1):
                            if T[r][j]:
                                T[r2][j] -= mmul * T[r][j]
                        T[r2][piv_col] = ZERO
                basis[r] = piv_col
        # else: zero row (redundant constraint), artificial stays basic at 0
    for j in range(nvars + mu, ncols):
        allowed[j] = False
    if obj is None:
        x = [ZERO] * nvars
        for r in range(m):
            if basis[r] < nvars:
                x[basis[r]] = T[r][ncols]
        return {'status': 'optimal', 'x': x, 'value': ZERO}
    c = [F(v) for v in obj]
    if maximize:
        c = [-v for v in c]
    cost = [ZERO] * (ncols + 1)
    for j in range(nvars):
        cost[j] = c[j]
    for r in range(m):
        bj = basis[r]
        cb = c[bj] if bj < nvars else ZERO
        if cb:
            for j in range(ncols + 1):
                if T[r][j]:
                    cost[j] -= cb * T[r][j]
    st, _ = _simplex(T, basis, m, ncols, cost, allowed)
    if st == 'unbounded':
        return {'status': 'unbounded'}
    x = [ZERO] * nvars
    for r in range(m):
        if basis[r] < nvars:
            x[basis[r]] = T[r][ncols]
    val = sum(c[j] * x[j] for j in range(nvars))
    if maximize:
        val = -val
    return {'status': 'optimal', 'x': x, 'value': val}


def _farkas(nvars, A_eq, b_eq, A_ub, b_ub):
    """Solve the Farkas alternative system by phase-1 and verify.
    Want: y_eq free, y_ub >= 0,  y A >= 0 (cols),  y.b = -1."""
    me, mu = len(A_eq), len(A_ub)
    # vars: u(me) [y_eq+], w(me) [y_eq-], z(mu) >= 0
    nv = 2 * me + mu
    Aub2, bub2 = [], []
    for k in range(nvars):
        row = [ZERO] * nv
        for i in range(me):
            row[i] = -A_eq[i][k]
            row[me + i] = A_eq[i][k]
        for i in range(mu):
            row[2 * me + i] = -A_ub[i][k]
        Aub2.append(row)   # -(yA)_k <= 0
        bub2.append(ZERO)
    eqrow = [ZERO] * nv
    for i in range(me):
        eqrow[i] = b_eq[i]
        eqrow[me + i] = -b_eq[i]
    for i in range(mu):
        eqrow[2 * me + i] = b_ub[i]
    res = solve(nv, [eqrow], [-ONE], Aub2, bub2, _no_recurse=True)
    assert res['status'] == 'optimal', 'Farkas alternative infeasible: logic error'
    y = res['x']
    y_eq = [y[i] - y[me + i] for i in range(me)]
    y_ub = [y[2 * me + i] for i in range(mu)]
    check_farkas(nvars, A_eq, b_eq, A_ub, b_ub, y_eq, y_ub)
    return (y_eq, y_ub)


def check_farkas(nvars, A_eq, b_eq, A_ub, b_ub, y_eq, y_ub):
    """Raise if (y_eq,y_ub) is not a valid infeasibility certificate."""
    me, mu = len(A_eq), len(A_ub)
    assert all(v >= 0 for v in y_ub), 'y_ub must be >= 0'
    for k in range(nvars):
        s = sum(y_eq[i] * F(A_eq[i][k]) for i in range(me)) + \
            sum(y_ub[i] * F(A_ub[i][k]) for i in range(mu))
        assert s >= 0, f'Farkas col {k}: combination {s} < 0'
    rhs = sum(y_eq[i] * F(b_eq[i]) for i in range(me)) + \
          sum(y_ub[i] * F(b_ub[i]) for i in range(mu))
    assert rhs < 0, f'Farkas rhs {rhs} not < 0'
    return True
