"""Exact tests for native one-resource Boolean predicate gates and terminal cloning.

Run `python3 -B round2/check_security_equilibrium_predicate.py` with z3-solver.
The two complete probe examples use a single comparison and a deliberately
small, specifically verified final perturbation. They do not execute the
uniform (potentially far larger) Cramer perturbation or a general compiler.
"""

from fractions import Fraction as F
from itertools import product

import z3

from security_equilibrium_uniqueness import Game


def q(value):
    value = F(value)
    return z3.Q(value.numerator, value.denominator)


def summands(items):
    return z3.Sum(list(items))


def value(model, term):
    result = model.eval(term, model_completion=True)
    return F(result.numerator_as_long(), result.denominator_as_long())


def require(solver, status):
    result = solver.check()
    assert result == status, (result, status, solver.reason_unknown())
    return solver.model() if result == z3.sat else None


def exclude(solver, assertion):
    solver.push()
    solver.add(assertion)
    require(solver, z3.unsat)
    solver.pop()


def fold(a, b, bound, depth):
    """Approximate a+b using monotone min/max/translation and doubling."""
    for _ in range(depth):
        a, b = (z3.If(a >= b, a, b) - bound/4,
                z3.If(a <= b, a, b) + bound/4)
        bound /= 2
    return 2*a


def check_real_circuits():
    checks = 0
    for depth in (0, 1, 2, 4, 7):
        a, b = z3.Reals(f'a_{depth} b_{depth}')
        bound = q(5)
        solver = z3.SolverFor('QF_LRA')
        solver.add(a-b <= bound, b-a <= bound)
        error = fold(a, b, bound, depth) - a - b
        exclude(solver, z3.Or(error < -bound/(2**depth), error > bound/(2**depth)))
        checks += 1

    # The gate's unknown capacity and downstream load are mutually independent.
    for kind in ('min', 'max'):
        solver = z3.SolverFor('QF_LRA')
        a, b, capacity, reader, price = z3.Reals(f'a_{kind} b_{kind} cap_{kind} read_{kind} p_{kind}')
        solver.add(a >= 1, b >= 1, a <= 3, b <= 3, capacity >= 1,
                   capacity <= q(F(5, 4)), reader >= 0, reader <= q(F(1, 4)), price >= 0)
        choices = [z3.If(a <= b, a, b)] if kind == 'min' else [a, b]
        flows = [z3.Real(f'in_{kind}_{i}') for i in range(len(choices))]
        guard = z3.Real(f'guard_{kind}')
        solver.add(guard >= 0, guard <= q(F(1, 4)),
                   z3.Implies(price < 6, guard == q(F(1, 4))),
                   z3.Implies(price > 6, guard == 0))
        for load, threshold in zip(flows, choices):
            solver.add(load >= 0, load <= 2,
                       z3.Implies(price < threshold, load == 2),
                       z3.Implies(price > threshold, load == 0))
        total = guard + summands(flows) + reader
        solver.add(total <= capacity, z3.Implies(price > 0, total == capacity))
        target = z3.If(a <= b, a, b) if kind == 'min' else z3.If(a >= b, a, b)
        require(solver, z3.sat)
        exclude(solver, price != target)
        checks += 1

    # Test difference rails using unrelated common baselines and signed noise.
    tolerance = q(F(1, 32))
    for bit_a, bit_b in product((0, 1), repeat=2):
        p, n, r, s = z3.Reals(f'p{bit_a}{bit_b} n{bit_a}{bit_b} r{bit_a}{bit_b} s{bit_a}{bit_b}')
        solver = z3.SolverFor('QF_LRA')
        solver.add(n >= -1, n <= 1, s >= -1, s <= 1,
                   p-n >= bit_a-tolerance, p-n <= bit_a+tolerance,
                   r-s >= bit_b-tolerance, r-s <= bit_b+tolerance)
        for op, expected in [('min', min(bit_a, bit_b)), ('max', max(bit_a, bit_b))]:
            # Abstract the proven fold error, on three independently approximated sums.
            e1, e2, e3 = [z3.FreshReal('sum_error') for _ in range(3)]
            solver.push()
            for e in (e1,e2,e3):
                solver.add(e >= -q(F(1,128)), e <= q(F(1,128)))
            a, b = p+s+e1, r+n+e2
            out = (z3.If(a <= b, a, b) if op == 'min' else z3.If(a >= b, a, b)) - n-s-e3
            exclude(solver, z3.Or(out < expected-q(F(3,64)), out > expected+q(F(3,64))))
            solver.pop()
            checks += 1
    return checks


def comparison_game(high):
    # A dedicated original attack gives old target x its full one-resource allocation.
    # The native readout sees a small displacement caused by its four auxiliary targets.
    rho = F(1,128)
    scale = F(1,1 << 20)
    names = ('x','other','P','Nshift','T','D')
    rows = []
    def add(name, mass, options):
        rows.append((name, F(mass), {target:tuple(map(F,pair)) for target,pair in options.items()}))
    add('source', 1, {('x' if high else 'other'):(3,1)})
    add('background x', 16, {'x':(3,1)})
    add('background other', 16, {'other':(3,1)})
    for rail in ('P','Nshift'):
        # P=1+max(x+1/8,1/2), Nshift=1+max(x,1/2)+1/16.
        shift = F(0) if rail=='P' else F(1,16)
        c = 8*scale
        input_a = 4-(1+shift+(F(1,8) if rail=='P' else 0))
        add('read '+rail, 2*c, {rail:(4,1/rho),'x':(input_a,1),'D':(0,1)})
        # With y_D=0 this second generator's D option is the constant threshold.
        input_const = 4-(F(3,2)+shift)
        add('floor '+rail, 2*c, {rail:(4,1/rho),'D':(input_const,1)})
        add('guard '+rail, c/4, {rail:(5,1/rho),'D':(0,1)})
    for label,rail in [('A','P'),('B','Nshift')]:
        add(label, scale, {'T':(5,1/rho),rail:(5,1/rho),'D':(0,1)})
    raw = sum(r[1] for r in rows)
    gains = (1,1,16/(8*scale),16/(8*scale),16/(3*scale/2),16/(4*raw))
    a = tuple(tuple(r[2].get(j,(F(-20),F(1)))[0] for j in names) for r in rows)
    b = tuple(tuple(r[2].get(j,(F(-20),F(1)))[1] for j in names) for r in rows)
    return Game(tuple(r[1]/raw for r in rows), gains, a, b, 1), [r[0] for r in rows], names, rho


def perturbed(game, names, precision=10):
    # Same mass/intercept formula as isolation, at instance-specific checked precision.
    m, n = len(game.priors), len(game.gains)
    scale = F(1,1 << precision)
    priors = tuple((*game.priors, *((F(0),)*n)))
    adjusted = tuple(u+scale**(i+1) for i,u in enumerate(priors))
    a = [*game.intercepts, *(tuple(F(2 if j==k else -2) for j in range(n)) for k in range(n))]
    b = (*game.slopes, *((F(1),)*n for _ in range(n)))
    aa = tuple(tuple(a[i][j]+scale**(i*n+j+1) for j in range(n)) for i in range(m+n))
    return Game(tuple(u/sum(adjusted) for u in adjusted),game.gains,aa,b,1), [*names, *(f'dedicate {j}' for j in range(n))]


def clone(game, row):
    p = list(game.priors)
    p[row] /= 2
    return Game(tuple(p)+(p[row],),game.gains,game.intercepts+(game.intercepts[row],),
                game.slopes+(game.slopes[row],),1)


def model_for(game):
    n = len(game.gains)
    solver = z3.SolverFor('QF_LRA')
    x = [z3.FreshReal('coverage') for _ in range(n)]
    solver.add(*(v>=0 for v in x),summands(x)==1)
    flows = {}
    for i,mass in enumerate(game.priors):
        offers = [q(a)-q(b)*v for a,b,v in zip(game.intercepts[i],game.slopes[i],x)]
        floor = max(a-b for a,b in zip(game.intercepts[i],game.slopes[i]))
        allowed = [j for j in range(n) if game.intercepts[i][j]>=floor]
        best = z3.FreshReal('best')
        solver.add(*(best>=offer for offer in offers))
        for j in allowed:
            v = z3.FreshReal('joint')
            flows[i,j]=v
            solver.add(v>=0,z3.Implies(v>0,best==offers[j]))
        solver.add(summands(flows[i,j] for j in allowed)==q(mass))
    peak = z3.FreshReal('peak')
    for j,(v,gain) in enumerate(zip(x,game.gains)):
        score = q(gain)*summands(f for (i,k),f in flows.items() if k==j)
        solver.add(peak>=score,z3.Implies(v>0,peak==score))
    return solver,x,flows


def check_complete(high):
    game,names,goods,rho = comparison_game(high)
    source, P,N,T,D = [goods.index(j) for j in ('x','P','Nshift','T','D')]
    row = names.index('B')
    solver,x,flows = model_for(game)
    require(solver,z3.sat)
    exclude(solver,z3.Or(x[D]!=0, x[source] < q(F(3,4)) if high else x[source]>q(F(1,4)),
                         x[P]-x[N] <= 0 if high else x[P]-x[N]>=0))
    exclude(solver,z3.Or(flows[row,T]<=0,flows[row,N]<=0) if high
            else flows[row,T]!=q(game.priors[row]))
    # Exact complete game at a finite perturbation; no equilibrium is passed in.
    game,_ = perturbed(game,names)
    solver,x,flows=model_for(game)
    m = require(solver,z3.sat)
    coordinates = list(x)+list(flows.values())
    exclude(solver,z3.Or(*(v!=q(value(m,v)) for v in coordinates)))
    on_T, mass = value(m,flows[row,T]),game.priors[row]
    assert (0<on_T<mass and value(m,flows[row,N])==mass-on_T) if high else on_T==mass
    merged_x=[value(m,v) for v in x]
    merged_f={k:value(m,v) for k,v in flows.items()}
    split=clone(game,row)
    solver,x,flows=model_for(split)
    m2=require(solver,z3.sat)
    coordinates=list(x)+list(flows.values())
    if not high:
        exclude(solver,z3.Or(*(v!=q(value(m2,v)) for v in coordinates)))
        return
    last=len(split.priors)-1
    low=max(F(0),on_T-mass/2)
    upper=min(mass/2,on_T)
    assert low<upper
    endpoints=[]
    for fixed in (low,upper):
        solver.push()
        solver.add(flows[row,T]==q(fixed))
        model=require(solver,z3.sat)
        endpoints.append([value(model,v) for v in coordinates])
        solver.pop()
    ref,tip=endpoints
    t=(flows[row,T]-q(low))/q(upper-low)
    exclude(solver,z3.Or(*(v!=q(a)+q(b-a)*t for v,a,b in zip(coordinates,ref,tip))))
    exclude(solver,z3.Or(t<0,t>1))
    # Every convex split with this same slope has all original costs/scores fixed:
    # merged row and all other rows/coverages stay constant along the segment.
    for endpoint in endpoints:
        ev = dict(zip(flows,endpoint[len(x):]))
        assert endpoint[:len(x)]==merged_x
        for (i,j),v in merged_f.items():
            assert ev.get((i,j),0)+(ev.get((last,j),0) if i==row else 0)==v


if __name__=='__main__':
    count=check_real_circuits()
    print(f'All {count} universal real fold, gate, and signed-logic checks passed.',flush=True)
    for high in (False,True):
        check_complete(high)
        print(f'Full 11-type, six-target comparison case {int(high)}: detector and displacement verified. '
              f'17-type final merged equilibrium unique at δ=2^-10; 18-type split is '
              f'{"exactly one segment" if high else "a singleton"}.',flush=True)
