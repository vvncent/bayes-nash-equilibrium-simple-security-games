# Lemma 6, fully symbolic: for given m (and constants M, eps), asks z3 whether there exist
#   c > 0, 0 <= x < c, P', P'' in [0,1], a primal f of G(c,x,M-P',M-eps-P'') and a dual (v,pi)
#   satisfying complementary slackness (<=> f optimal, LP duality) with (A,B) != (h0(min(x,K)), h1(min(x,K))).
# unsat  ==> Lemma 6 holds for ALL c, x, P', P'' (for this m and constants).
# Also checks the optimal value set is nonempty for a few concrete points (sanity).
# usage: python -I check_gadget.py mmax [control]
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from ref_lib import splitter

def gadget(m, M, eps, Pbox=(0, 1), cap_x=None):
    nodes, arcs, S, a, b = splitter(m)
    K = 2 ** (m + 1)
    s = z3.Solver()
    c, x, P1, P2 = z3.Reals('c x P1 P2')
    s.add(c > 0, x >= 0, x < c, P1 >= Pbox[0], P1 <= Pbox[1], P2 >= Pbox[0], P2 <= Pbox[1])
    f = [z3.Real('f%d' % i) for i in range(len(arcs))]
    g = [z3.Real('g%d' % i) for i in range(len(arcs))]   # head purchases
    y, A, B = z3.Reals('y A B')
    v = {u: z3.Real('v_%s' % (u,)) for u in nodes}
    pe = [z3.Real('pi%d' % i) for i in range(len(arcs))]
    pp = z3.Real('pip')
    for t in f + g + [y, A, B] + list(v.values()) + pe + [pp]:
        s.add(t >= 0)
    incap = {u: sum(e[2] for e in arcs if e[1] == u) for u in nodes}
    rows = {u: [] for u in nodes}
    for i, (t, h, cap, kap) in enumerate(arcs):
        rows[t].append(f[i]); rows[h].append(g[i])
        # column
        s.add(f[i] + g[i] <= cap, z3.Or(pe[i] == 0, f[i] + g[i] == cap))
        # dual feasibility + CS for the two options
        s.add(v[t] + pe[i] >= 2 * M - kap, z3.Or(f[i] == 0, v[t] + pe[i] == 2 * M - kap))
        s.add(v[h] + pe[i] >= 2 * M, z3.Or(g[i] == 0, v[h] + pe[i] == 2 * M))
    rows[S].append(y); rows[a].append(A); rows[b].append(B)
    s.add(y <= c - x, z3.Or(pp == 0, y == c - x))
    s.add(v[S] + pp >= 2 * M, z3.Or(y == 0, v[S] + pp == 2 * M))
    s.add(v[a] >= M - P1, z3.Or(A == 0, v[a] == M - P1))
    s.add(v[b] >= M - eps - P2, z3.Or(B == 0, v[b] == M - eps - P2))
    for u in nodes:
        mass = c if u == S else incap[u]
        s.add(z3.Sum(rows[u]) <= mass, z3.Or(v[u] == 0, z3.Sum(rows[u]) == mass))
    # target
    xm = z3.If(x < K, x, K)
    zz = z3.Int('zz'); rho = z3.Real('rho')
    s.add(xm == 2 * zz + rho, rho >= 0, rho < 2, zz >= 0)
    H0 = zz + z3.If(rho < 1, rho, 1)
    H1 = zz + z3.If(rho > 1, rho - 1, 0)
    if cap_x is not None:
        s.add(x <= cap_x)
    return s, (c, x, P1, P2, A, B, H0, H1)

if __name__ == '__main__':
    mmax = int(sys.argv[1])
    control = sys.argv[2] if len(sys.argv) > 2 else None
    negctl = control in ('smallM', 'eps1', 'eps55')  # artifact: exit status (Pbox2 is not a control)
    allok = True  # artifact: exit status
    for m in range(1, mmax + 1):
        M = 2 * 3 ** (m + 1); eps = 3
        Pbox = (0, 1)
        if control == 'smallM': M = (3 ** (m + 1)) // 2
        if control == 'eps1': eps = 1
        if control == 'eps55': eps = 5.5
        if control == 'Pbox2': Pbox = (0, 2)
        t0 = time.time()
        s, (c, x, P1, P2, A, B, H0, H1) = gadget(m, M, eps, Pbox)
        s.push(); s.add(z3.Not(z3.And(A == H0, B == H1)))
        r = s.check()
        msg = ''
        if r == z3.sat:
            md = s.model()
            msg = 'CEX c=%s x=%s P1=%s P2=%s A=%s B=%s' % tuple(md.eval(t, model_completion=True) for t in (c, x, P1, P2, A, B))
        s.pop()
        # sanity: optimum exists at a few points
        san = []
        for xv in (0, 1, 2.5, 2 ** (m + 1), 2 ** (m + 1) + 3):
            s.push(); s.add(x == xv, c == 2 ** (m + 2) + 5, P1 == 0, P2 == 1); san.append(str(s.check())); s.pop()
        print('m=%d M=%s eps=%s control=%s : violation query %s %s  sanity %s  (%.1fs)' %
              (m, M, eps, control, r, msg, san, time.time() - t0), flush=True)
        # artifact: exit status -- controls must give a counterexample (sat) for every m; otherwise the
        # violation query must be unsat and every sanity point sat
        allok &= (r == z3.sat) if negctl else (r == z3.unsat and all(t == 'sat' for t in san))
    sys.exit(0 if allok else 1)  # artifact: exit status
