"""matching.typ §8: zero attack slopes / zero defender gains. Perturb by eps=1/(8 Q3), solve the positive
game by §§4-5 through M1 calls, then decode with the original pattern LP (slack t) and verify an exact
BNE of the ORIGINAL game. Usage: $PY -I -B check_degenerate.py N seed"""
import sys, os, random, time
import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
from fractions import Fraction as Fr
import z3
from core import R, val, Game, M1Oracle, check_bne, row_int_bound
from procedure import solve_game, labels01


class Game0(Game):
    def __init__(self, p, a, b, d, r):
        self.p = [Fr(v) for v in p]; self.a = [[Fr(v) for v in row] for row in a]
        self.b = [[Fr(v) for v in row] for row in b]; self.d = [Fr(v) for v in d]
        self.r = r; self.m = len(p); self.n = len(d)
        assert sum(self.p) == 1 and all(v > 0 for v in self.p) and 0 < r < self.n
        assert all(v >= 0 for row in self.b for v in row) and all(v >= 0 for v in self.d)


def Q3_of(G):
    m, n = G.m, G.n
    N3 = n + m * n + 2
    D = 1 + max(G.d)
    X = lambda j: j; Fi = lambda i, j: n + i * n + j; L = N3 - 2; T = N3 - 1
    rows = []
    unit = lambda k: [Fr(1) if q == k else Fr(0) for q in range(N3)]
    for k in range(N3):
        rows.append((unit(k), Fr(0))); rows.append((unit(k), Fr(1)))
    rows.append((unit(L), D))
    for i in range(m):
        co = [Fr(0)] * N3
        for j in range(n):
            co[Fi(i, j)] = Fr(1)
        rows.append((co, G.p[i]))
        for j in range(n):
            for k in range(n):
                if j != k:
                    co = [Fr(0)] * N3
                    co[X(j)] = -G.b[i][j]; co[X(k)] = G.b[i][k]; co[T] = Fr(1)
                    rows.append((co, G.a[i][k] - G.a[i][j]))
    for j in range(n):
        for sg in (1, -1):
            co = [Fr(0)] * N3
            for i in range(m):
                co[Fi(i, j)] = sg * G.d[j]
            co[L] = Fr(-sg); co[T] = Fr(1)
            rows.append((co, Fr(0)))
    rows.append(([Fr(1)] * n + [Fr(0)] * (N3 - n), Fr(G.r)))
    H3 = row_int_bound(rows)
    return (N3 * H3) ** N3


def decode(G, xp, fp):
    m, n = G.m, G.n
    A = [[fp[i][j] > 0 for j in range(n)] for i in range(m)]
    lab = labels01(xp)
    s = z3.Optimize()
    X = [z3.Real(f"x{j}") for j in range(n)]
    Fv = [[z3.Real(f"f{i}_{j}") for j in range(n)] for i in range(m)]
    lam, t = z3.Real("lam"), z3.Real("t")
    s.add(lam >= 0, lam <= R(1 + max(G.d)), t >= 0, t <= 1, z3.Sum(X) == G.r)
    for j in range(n):
        s.add(X[j] >= 0, X[j] <= 1)
    for i in range(m):
        s.add(z3.Sum(Fv[i]) == R(G.p[i]))
        for j in range(n):
            s.add(Fv[i][j] >= 0, Fv[i][j] <= 1)
            if not A[i][j]:
                s.add(Fv[i][j] == 0)
            else:
                for k in range(n):
                    s.add(R(G.a[i][j]) - R(G.b[i][j]) * X[j] - R(G.a[i][k]) + R(G.b[i][k]) * X[k] + t >= 0)
    for j in range(n):
        sc = R(G.d[j]) * z3.Sum([Fv[i][j] for i in range(m)])
        if lab[j] == "zero":
            s.add(X[j] == 0, sc <= lam + t)
        elif lab[j] == "one":
            s.add(X[j] == 1, sc + t >= lam)
        else:
            s.add(sc <= lam + t, sc + t >= lam)
    s.minimize(t)
    assert s.check() == z3.sat
    mod = s.model()
    assert val(mod, t) == 0, "decoding LP optimum positive"
    return [val(mod, e) for e in X], [[val(mod, e) for e in row] for row in Fv]


if __name__ == "__main__":
    N = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed)
    for t in range(N):
        t0 = time.time()
        m, n = rng.randint(1, 2), rng.randint(2, 3)
        w = [rng.randint(1, 3) for _ in range(m)]
        p = [Fr(q, sum(w)) for q in w]
        a = [[Fr(rng.randint(-4, 4), rng.randint(1, 2)) for _ in range(n)] for _ in range(m)]
        b = [[Fr(0) if rng.random() < .4 else Fr(rng.randint(1, 4), rng.randint(1, 2)) for _ in range(n)]
             for _ in range(m)]
        d = [Fr(0) if rng.random() < .35 else Fr(rng.randint(1, 4), rng.randint(1, 2)) for _ in range(n)]
        G0 = Game0(p, a, b, d, rng.randint(1, n - 1))
        eps = Fr(1, 8 * Q3_of(G0))
        Gp = Game(p, [row[:] for row in a], [[q + eps for q in row] for row in b], [q + eps for q in d], G0.r)
        orc = M1Oracle(["opt", "interior", "plain"][t % 3], t)
        xp, fp, st = solve_game(Gp, orc)
        assert check_bne(Gp, xp, fp)[0]
        x0, f0 = decode(G0, xp, fp)
        ok, why = check_bne(G0, x0, f0)
        assert ok, why
        print(f"#{t} m={m} n={n} r={G0.r} zero_b={sum(q == 0 for row in b for q in row)} "
              f"zero_d={sum(q == 0 for q in d)} eps_bits={(1/eps).numerator.bit_length()} "
              f"calls={orc.calls} exit={st['exit']} original BNE={ok} x={[str(q) for q in x0]} "
              f"{time.time()-t0:.0f}s", flush=True)
    print("degenerate decoding OK")
