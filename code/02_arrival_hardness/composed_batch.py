"""Batch of random discriminating ARRIVAL instances (n=5,6) through the book's composed market.
Per instance, exact z3 queries over ALL equilibria of the composed market:
  Q1 SAT   : an equilibrium exists
  Q2 UNSAT : some equilibrium has non-terminal load != 1 on the run's terminal or != 0 on the other
  Q3 UNSAT : some equilibrium has, at some gadget v, x_v > K-1 ... i.e. x_v >= K, or A_v != h0(x_v)
             or B_v != h1(x_v)   (Theorem 4.4 parts 1-2; h encoded with an integer z_v, 2z_v<=x_v<2z_v+2)
Reproduce: .venv/bin/python -I composed_batch.py <n> <count> <seed> [procs]
"""
import sys, os, time, random
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from eh_lib import compose, eq_constraints, run, preprocess, Q

Y, N = "yes", "no"


def term_load(fl, t):
    xs = [f for (b, j), f in fl.items() if j == f"T_{t}" and not b.startswith("term_")]
    return z3.Sum(xs) if xs else Q(0)


def check(args):
    succ0, o0 = args
    n = len(succ0)
    want, steps, _ = run(succ0, o0)
    other = N if want == Y else Y
    succ, o = preprocess(succ0, o0)
    goods, buyers = compose(succ, o, n)
    K = 2 ** (n + 1)
    s = z3.Solver()
    P, fl, vv, load = eq_constraints(goods, buyers, s)
    t0 = time.time()
    r1 = s.check()
    s.push()
    s.add(z3.Or(term_load(fl, want) != 1, term_load(fl, other) != 0))
    r2 = s.check()
    s.pop()
    # Q3
    bad = []
    for v in succ:
        x = z3.Sum([f for (b, j), f in fl.items() if j == f"p_{v}" and b != f"g{v}.s"])
        A = fl[(f"g{v}.a", (f"T_{succ[v][0]}" if succ[v][0] in (Y, N) else f"p_{succ[v][0]}"))]
        B = fl[(f"g{v}.b", (f"T_{succ[v][1]}" if succ[v][1] in (Y, N) else f"p_{succ[v][1]}"))]
        z = z3.Int(f"z{v}")
        rho = x - 2 * z3.ToReal(z)
        s.add(rho >= 0, rho < 2)
        h0 = z3.ToReal(z) + z3.If(rho < 1, rho, Q(1))
        bad.append(z3.Or(x >= K, A != h0, B != x - h0))
    s.add(z3.Or(bad))
    r3 = s.check()
    ok = r1 == z3.sat and r2 == z3.unsat and r3 == z3.unsat
    return (f"succ={succ0} run->{want} {steps} steps kept={len(succ)} | exists={r1} wrong={r2} "
            f"notFP={r3} | {'OK' if ok else 'FAIL'} ({time.time()-t0:.0f}s)", ok)


def gen(n, count, seed):
    rng = random.Random(seed)
    tg = list(range(n)) + [Y, N]
    out, seen = [], set()
    tries = 0
    while len(out) < count and tries < 10 ** 6:
        tries += 1
        succ = {v: (rng.choice(tg), rng.choice(tg)) for v in range(n)}
        key = tuple(succ.items())
        if key in seen:
            continue
        want, steps, term = run(succ, 0)
        alt, _, _ = run({v: (b, a) for v, (a, b) in succ.items()}, 0)
        if alt == want or steps < 2 * n or len(preprocess(succ, 0)[0]) < n:  # discriminating, nontrivial, nothing deleted
            continue
        seen.add(key)
        out.append((succ, 0))
    return out


if __name__ == "__main__":
    n, count, seed = map(int, sys.argv[1:4])
    procs = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    inst = gen(n, count, seed)
    allok = True
    with Pool(procs) as pool:
        for line, ok in pool.imap_unordered(check, inst):
            allok &= ok
            print(line, flush=True)
    print(f"n={n} count={len(inst)} seed={seed}: {'ALL OK' if allok else 'SOME FAILED'}")
    sys.exit(0 if allok else 1)  # artifact: exit status
