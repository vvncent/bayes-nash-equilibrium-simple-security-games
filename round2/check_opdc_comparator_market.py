"""Independent exact checks for feedback with non-replicated comparator inputs.

Coordinates, literal signs, and low/high outputs are explicit. Uses Fraction
for the real model. The optional full expanded market checks need z3-solver.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations, product
from random import Random


def lit(wire, neg=False):
    return wire, bool(neg)


def unlit(x, literal):
    i, neg = literal
    return 1 - x[i] if neg else x[i]


def value_net(n, gates, x):
    y = [None] * n
    for gate in gates:
        if gate[0] == 'pair':
            _, left, right, lo, hi = gate
            s = unlit(x, left) + unlit(x, right)
            outputs = ((lo, max(Q(0), s-1)), (hi, min(Q(1), s)))
        elif gate[0] == 'copy':
            _, src, dest = gate
            outputs = ((dest, unlit(x, src)),)
        else:
            _, c, dest = gate
            outputs = ((dest, Q(c)),)
        for l, val in outputs:
            if l is None:
                continue
            i, neg = l
            assert y[i] is None
            y[i] = 1 - val if neg else val
    assert not any(v is None for v in y)
    return tuple(y)


def slacks(n, gates, probe):
    """Affine restrictions after independently choosing the branch at a candidate."""
    rows = [None] * n

    def literal_row(w):
        return int(w[1]), {w[0]: -1 if w[1] else 1}

    for gate in gates:
        if gate[0] == 'pair':
            _, l, r, lo, hi = gate
            a, aa = literal_row(l)
            b, bb = literal_row(r)
            assert set(aa).isdisjoint(bb)
            s = (a+b, aa | bb)
            if unlit(probe, l)+unlit(probe, r) <= 1:
                output = ((lo, (0, {})), (hi, s))
            else:
                output = ((lo, (s[0]-1, s[1])), (hi, (1, {})))
        elif gate[0] == 'copy':
            output = ((gate[2], literal_row(gate[1])),)
        else:
            output = ((gate[2], (gate[1], {})),)
        for d, (c, linear) in output:
            if d is not None:
                i, neg = d
                assert rows[i] is None
                rows[i] = (1-c, {j: -v for j, v in linear.items()}) if neg else (c, linear)
    assert all(r is not None for r in rows)
    used = [j for _, linear in rows for j in linear]; assert len(used) == len(set(used))
    return rows


def tree_cycle_repair(n, gates, x):
    """Direct exact repair of an inverse-polynomial residual, via outdegree-one columns."""
    assert all(0 <= v <= 1 for v in x)
    e = max((abs(a-b) for a,b in zip(value_net(n,gates,x),x)), default=Q())
    assert e < Q(1,16*max(1,n))
    rows = slacks(n,gates,x)
    pending = set(range(n)); y = {}
    while True:
        progress = []
        for i in pending:
            c, inc = rows[i]
            if all(j in y for j in inc):
                y[i] = Q(c) + sum(s*y[j] for j,s in inc.items())
                assert y[i] in (0,1) and abs(y[i]-x[i]) <= n*e
                progress.append(i)
        if not progress: break
        pending.difference_update(progress)
    nxt={}; delta={}
    for i in pending:
        c, inc = rows[i]
        pred, = [j for j in inc if j in pending]
        assert pred not in nxt
        nxt[pred]=i
        delta[i]=int(inc[pred]),Q(c)+sum(s*y[j] for j,s in inc.items() if j in y)
    while pending:
        root=next(iter(pending)); chain=[root]; v=nxt[root]
        while v!=root:
            chain.append(v); v=nxt[v]
        param={root:(1,Q(0))}
        for u in chain:
            v=nxt[u]
            a,b=delta[v]; p,c=param[u]; q,k=a*p,a*c+b
            if v!=root: param[v]=(q,k)
        if q==-1:
            t=k/2
        else:
            assert k==0
            lo,hi=Q(0),Q(1)
            for p,c in param.values():
                endpoints=sorted((p * -c,p*(1-c)))
                lo=max(lo,endpoints[0]); hi=min(hi,endpoints[1]);
            assert lo<=hi
            t=min(hi,max(lo,x[root]))
        for v,(p,c) in param.items():
            y[v]=p*t+c
            assert 0<=y[v]<=1 and abs(y[v]-x[v])<=2*n*e
        pending.difference_update(chain)
    out=tuple(y[i] for i in range(n))
    assert value_net(n,gates,out)==out
    return out


def damped_solution(n, gates):
    """Polynomial-bit solver; evaluate until the inverse-polynomial test succeeds."""
    alpha=Q(1,64*max(n,1)); x=(Q(1,2),)*n
    iterations=0
    # H is an l1 contraction with factor 1-alpha; coordinate residual is used as stopping test.
    while True:
        y=value_net(n,gates,x)
        if max((abs(a-b) for a,b in zip(x,y)),default=0) < Q(1,16*max(1,n)):
            break
        x=tuple((1-alpha)*b+alpha/2 for b in y)
        iterations+=1
        assert iterations <= 1024*max(n,1)*(n.bit_length()+1)
    fixed=tree_cycle_repair(n,gates,x)
    half=tuple(v if v in (0,1) else Q(1,2) for v in fixed)
    assert value_net(n,gates,half)==half
    return x,fixed,half,iterations


def ordered_check(answer,n,gates):
    if answer[0]=='root':
        _,x=answer
        assert len(x)==n and all(i in (0,1) for i in x) and tuple(x)==value_net(n,gates,x)
    else:
        tag,axis,lo,hi=answer
        assert tag=='OV2' and 0<=axis<n and len(lo)==len(hi)==n
        assert all(v in (0,1) for v in lo+hi) and lo[axis]==0 and hi[axis]==1 and lo[axis+1:]==hi[axis+1:]
        flo,fhi=value_net(n,gates,lo),value_net(n,gates,hi)
        assert flo[:axis]==lo[:axis] and fhi[:axis]==hi[:axis] and flo[axis]==1 and fhi[axis]==0


def enumerate_answers(n,gates):
    """Include every OV1, including two roots at the same side of a prefix slice."""
    pts=tuple(product((0,1),repeat=n)); f={p:value_net(n,gates,p) for p in pts}
    answers={('root',p) for p in pts if f[p]==p}
    for a in range(n):
        for suffix in product((0,1),repeat=n-a-1):
            kept=[p for p in pts if p[a+1:]==suffix and f[p][:a]==p[:a]]
            roots=[p for p in kept if f[p][a]==p[a]]
            for i,p in enumerate(roots):
                for q in roots[i+1:]:answers.add(('OV1',a,p,q))
            for p in kept:
                if p[a] or f[p][a]!=1:continue
                for q in kept:
                    if q[a] and f[q][a]==0:answers.add(('OV2',a,p,q))
    return answers


def as_network(n,gates):
    from opdc_comparator_market import Literal, Comparator, Unary, Constant, ComparatorNetwork
    def convert(l):return None if l is None else Literal(*l)
    converted=[]
    for item in gates:
        if item[0]=='pair': converted.append(Comparator(*(convert(l) for l in item[1:])))
        elif item[0]=='copy': converted.append(Unary(convert(item[1]),convert(item[2])))
        else:converted.append(Constant(item[1],convert(item[2])))
    return ComparatorNetwork(n,tuple(converted))


def compiled_decoding(n,gates,x,original=None):
    net=original if original is not None else as_network(n,gates)
    assert tuple(net.evaluate(x))==value_net(n,gates,x)==x
    out=net.decode_fixed_point(x)
    ordered_check(out,n,gates)
    return out


def four_wire_benchmarks():
    examples=[((('pair',lit(2),lit(3),lit(0),lit(1,1)),
                ('pair',lit(0),lit(1),lit(2,1),lit(3,1))),
               ('OV2',3,(0,0,1,0),(1,0,1,1))),
              ((('pair',lit(0),lit(1),lit(3,1),lit(2)),
                ('pair',lit(2),lit(3),lit(1,1),lit(0,1))),
               ('OV2',2,(0,1,0,1),(0,0,1,1)))]
    for gates,certificate in examples:
        assert enumerate_answers(4,gates)=={certificate}
        x,real,half,_=damped_solution(4,gates)
        net=as_network(4,gates)
        assert compiled_decoding(4,gates,real,net)==compiled_decoding(4,gates,half,net)==certificate
    return examples


def exhaustive_two_wire():
    fractional = (Q(0), Q(1,4), Q(1,2), Q(3,4), Q(1))
    exact=total=0; residual_checks=0
    for perm in permutations(range(2)):
        for signs in product((0,1), repeat=4):
            gates=(('pair',lit(0,signs[0]),lit(1,signs[1]),lit(perm[0],signs[2]),lit(perm[1],signs[3])),)
            net=as_network(2,gates); total+=1
            for x in product(fractional,repeat=2):
                f=value_net(2,gates,x)
                assert tuple(net.evaluate(x))==f
                if f!=x: continue
                exact+=1;compiled_decoding(2,gates,x,net)
                for d in (Q(-1,700),Q(0),Q(1,700)):
                    near=tuple(min(1,max(0,v+(1-2*i)*d)) for i,v in enumerate(x))
                    recovered=tree_cycle_repair(2,gates,near)
                    assert tuple(net.evaluate(recovered))==recovered
                    assert net.evaluate(net.recover_fixed_point(near))==net.recover_fixed_point(near)
                    residual_checks+=1
    return total,exact,residual_checks


def indicator_gates(rng, n):
    """Random legal producer/consumer network including unsigned, truncated and source cases."""
    wires=list(range(n));rng.shuffle(wires);cons=list(range(n));rng.shuffle(cons)
    out=[]
    while wires:
        source=len(cons)
        if not source or rng.random()<0.16:
            out.append(('const',rng.randrange(2),lit(wires.pop(),rng.randrange(2))));continue
        if len(cons)==1 or rng.random()<0.45:
            out.append(('copy',lit(cons.pop(),rng.randrange(2)),lit(wires.pop(),rng.randrange(2))));continue
        l,r=lit(cons.pop(),rng.randrange(2)),lit(cons.pop(),rng.randrange(2))
        a=lit(wires.pop(),rng.randrange(2)); b=lit(wires.pop(),rng.randrange(2)) if wires and rng.random()<0.65 else None
        if rng.randrange(2): a,b=b,a
        out.append(('pair',l,r,a,b))
    return tuple(out)


def hard_pair_ring(pairs):
    """A strongly connected odd unary cycle encoded entirely by full two-input comparators."""
    # Every pair receives the previous pair's moving rail and an integral control rail.
    # Its positive OR is the next moving rail, AND is the next zero integral control.
    # One moving output inversion closes an odd cycle with all comparator output wires live.
    out=[]
    for i in range(pairs):
        j=(i+1)%pairs
        out.append(('pair',lit(2*i),lit(2*i+1),lit(2*j+1),lit(2*j,i==pairs-1)))
    return tuple(out)


def scalable_controls():
    rng=Random(314159);counts=Counter();worst=0; total=0
    for n in range(1,9):
        for _ in range(10):
            gates=indicator_gates(rng,n);net=as_network(n,gates)
            near,exact,half,it=damped_solution(n,gates);worst=max(it,worst)
            # Exercise the actual selected-cell LP at an independently found approximate point.
            repaired=net.recover_fixed_point(near)
            for solved in (exact,half,repaired):
                answer=compiled_decoding(n,gates,solved,net)
                counts[answer[0]]+=1
            from opdc_comparator_repair import recover_approximate, solve_by_damping
            independently = recover_approximate(net,near)
            assert tuple(net.evaluate(independently)) == independently
            assert all(abs(a-b)<=2*n*max(abs(z-v) for z,v in zip(near,net.evaluate(near)))
                       for a,b in zip(independently,near))
            if n<=4:
                direct=solve_by_damping(net)
                assert net.evaluate(direct)==direct
            total+=1
    known=[]
    for k in (2,3,5,9,18):
        n=2*k;gates=hard_pair_ring(k);net=as_network(n,gates)
        point=tuple(Q(1,2) if not i%2 else Q(0) for i in range(n))
        assert value_net(n,gates,point)==point
        assert all(sum(j//2==i for g in gates for j in (g[1][0],g[2][0]))==2 for i in range(k))
        ans=compiled_decoding(n,gates,point,net)
        assert ans[0]=='OV2' and ans[1]==n-2
        # The dependency graph is strongly connected, including the integral control wires.
        dependencies={j:set() for j in range(n)}
        for g in gates:
            for a in g[1:3]:
                dependencies[a[0]].update(b[0] for b in g[3:])
        for start in range(n):
            reached={start};stack=[start]
            while stack:
                p=stack.pop()
                for v in dependencies[p]-reached:
                    reached.add(v);stack.append(v)
            assert len(reached)==n
        known.append((n,ans[1]))
    return total,counts,worst,known


def physical_equations(model, timeout_ms=30000):
    import z3
    rat=lambda d:z3.RealVal(str(Q(d)))
    z=z3.SolverFor('QF_LRA');z.set(timeout=timeout_ms)
    price={j:z3.Real(f'P{idx}') for idx,j in enumerate(model.capacities)}
    load={j:[] for j in price};f={}
    for r,(row,(mass,bids)) in enumerate(model.buyers.items()):
        u=z3.Real(f'U{r}');fset=[];z.add(u>=0)
        for h,(good,(a,b)) in enumerate(bids.items()):
            assert good in price and b>0
            x=z3.Real(f'Q{r}_{h}');payoff=rat(a)-rat(b)*price[good]
            z.add(x>=0,u>=payoff,z3.Or(x==0,u==payoff));load[good].append(x);fset.append(x);f[row,good]=x
        total=z3.Sum(fset);z.add(total<=rat(mass),z3.Or(total==rat(mass),u==0))
    for good,cap in model.capacities.items():
        total=z3.Sum(load[good]) if load[good] else rat(0)
        z.add(price[good]>=0,total<=rat(cap),z3.Or(price[good]==0,total==rat(cap)))
    return z,f


def physical_chamber_tests(n,gates,m,k,expect_bad=False):
    """Search only original ordinary market equilibria. Quantities are actual buyer flows."""
    import z3
    from opdc_comparator_market import compile_market
    net=as_network(n,gates);market=compile_market(net,m,k)
    s,f=physical_equations(market)
    pairs=[[f[a],f[b]] for a,b in market.delivery]
    est=tuple((p+1-r)/2 for p,r in pairs)
    status=s.check();assert status==z3.sat,(status,s.reason_unknown())
    witness={}
    for edge,var in f.items():
        val=s.model().eval(var,model_completion=True);witness[edge]=Q(val.numerator_as_long(),val.denominator_as_long())
    physical_state=tuple((p+1-r)/2 for p,r in market.read_quantities(witness))
    actual=None
    if not expect_bad:
        actual=market.decode(witness);ordered_check(actual,n,gates)
    # To certify all equilibria at the coarse precision, forbid every chosen cell whose
    # undamped affine equations have no solution. Ties are always decoded on their lower side.
    comparators=[g for g in gates if g[0]=='pair'];bad=[]
    for mask in product((0,1),repeat=len(comparators)):
        yy=[z3.Real(f'Y{i}') for i in range(n)];fp=z3.SolverFor('QF_LRA');fp.add(*(v>=0 for v in yy),*(v<=1 for v in yy));obs=[]
        it=iter(mask)
        for g in gates:
            if g[0]=='pair':
                branch=next(it);logical=unlit(yy,g[1])+unlit(yy,g[2]);measured=unlit(est,g[1])+unlit(est,g[2]);
                fp.add(logical>=1 if branch else logical<=1);obs.append(measured>1 if branch else measured<=1)
                outputs=((g[3],logical-1),(g[4],1)) if branch else ((g[3],0),(g[4],logical))
            elif g[0]=='copy':outputs=((g[2],unlit(yy,g[1])),)
            else:outputs=((g[2],g[1]),)
            for d,v in outputs:
                if d is not None:fp.add(yy[d[0]]==(1-v if d[1] else v))
        st=fp.check();assert st in (z3.sat,z3.unsat)
        if st==z3.unsat:bad.append(z3.And(*obs))
    if bad:
        s.push();s.add(z3.Or(*bad));st=s.check()
        if expect_bad:
            assert st==z3.sat, ('expected a real equilibrium in an infeasible cell',st)
            negative=s.model(); off={}
            for edge,var in f.items():
                value=negative.eval(var,model_completion=True)
                off[edge]=Q(value.numerator_as_long(),value.denominator_as_long())
            physical_state=tuple((p+1-r)/2 for p,r in market.read_quantities(off))
            try:
                market.decode(off)
            except ValueError:
                pass
            else:
                raise AssertionError('Coarse override accepted an infeasible cell')
        else:
            assert st==z3.unsat, ('unrecoverable observed cell at coarse precision',st,m,k)
        s.pop()
    else:
        assert not expect_bad
    return len(market.capacities),len(market.buyers),physical_state,actual,len(bad)


def discard_control():
    """Only the constant output survives in the observed cell; its discarded sum is near a kink."""
    from opdc_comparator_repair import recover_approximate

    for sign in (0,1):
        gates=(('const',0,lit(0)), ('const',1,lit(1)),
               ('pair',lit(0,sign),lit(1,sign),None if sign else lit(2),lit(2) if sign else None))
        net=as_network(3,gates)
        exact=(Q(0),Q(1),Q(sign))
        assert value_net(3,gates,exact)==exact
        for h in (Q(1,400),Q(1,800)):
            x=(h,1-2*h,h if not sign else 1-h)
            assert net.evaluate(recover_approximate(net,x))==exact


def main():
    if not __debug__:
        raise RuntimeError('Use Python assertions when running this verifier.')
    examples=four_wire_benchmarks()
    for _,answer in examples: print('All 16 Boolean points give only',answer)
    total,points,near=exhaustive_two_wire(); print(f'{total} two-wire signed wirings, {points} exact grid states, {near} near-cell checks.')
    discard_control()
    cases,counts,worst,rings=scalable_controls()
    print(f'{cases} source/sink/signed random networks; {sum(counts.values())} valid certificates; '
          f'max {worst} direct damping iterations. Fully live strongly connected rings (size,axis): {rings}.',flush=True)
    solo=(('copy',lit(0,True),lit(0)),)
    two=(('pair',lit(0),lit(1),lit(1,True),lit(0)),)
    for n,gates,m,k in [(1,solo,1,1),(2,two,1,2),
                          *((4,gs,1,k) for gs,_ in examples for k in (2,3))]:
        goods,buyers,state,answer,bad=physical_chamber_tests(n,gates,m,k)
        print(f'Expanded rational M1 n={n}, m={m}, k={k}: {goods} goods, {buyers} buyers; '
              f'{bad} infeasible decoded cells jointly excluded. One readout {state} yields {answer}.',flush=True)
    goods,buyers,state,_,_=physical_chamber_tests(4,examples[0][0],1,1,expect_bad=True)
    print(f'Coarse negative control m=1,k=1: {goods} goods, {buyers} buyers; an actual equilibrium '
          f'has estimate {state} in an infeasible cell.')


if __name__=='__main__':
    main()
