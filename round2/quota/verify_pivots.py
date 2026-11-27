"""Check the eight-cycle and its explicit rectangular subdivision with exact fractions."""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product


@dataclass(frozen=True)
class Row:
    tail: int
    head: int
    cap: int
    left: int
    right: int
    intercept: F


BASE = tuple(Row(*v) for v in [
    (0, 1, 1, 2, 1, -1), (0, 2, 3, 1, 2, 1), (0, 3, 2, 1, 2, 8),
    (2, 3, 1, 2, 1, 4), (2, 3, 2, 1, 4, 2), (3, 1, 3, 8, 1, -9), (1, 3, 3, 4, 1, 1)])
NET = tuple(F(v, 7) for v in (-23, 8, 10, 5))
FLOWS = [tuple(F(v, 7) for v in xs) for xs in [(6,17,0,7,0,21,19), (2,21,0,7,4,21,15),
    (2,21,0,0,11,21,15), (2,21,0,0,11,6,0), (7,16,0,0,6,1,0), (7,10,6,0,0,1,0),
    (7,10,6,0,0,21,20), (7,16,0,6,0,21,20)]]
VIOLATIONS = [F(29,2),F(21),F(32),F(3),F(27,4),F(89),F(1),F(2)]


def net_load(rows, w, n):
    b = [F(0)]*n
    for e, value in zip(rows,w):
        b[e.tail] -= value
        b[e.head] += value
    return b


def tree_prices(rows, tree, n, pin=0):
    adj = [[] for _ in range(n)]
    for i in tree:
        e = rows[i]
        adj[e.tail].append((e.head, i))
        adj[e.head].append((e.tail, i))
    seq = [(0, None, None)]
    price = {0: F(pin)}
    for u, _, _ in seq:
        for v, i in adj[u]:
            if v in price:
                continue
            e = rows[i]
            price[v] = (e.intercept+e.left*price[u])/e.right if u == e.tail else (e.right*price[u]-e.intercept)/e.left
            seq.append((v,u,i))
    return (price, seq) if len(seq)==n and len(tree)==n-1 else (None,None)


def slack(e,p):
    return e.right*p[e.head]-e.left*p[e.tail]-e.intercept


def enumerated_vertices():
    vertices = {}
    for tree in combinations(range(7), 3):
        p, sequence = tree_prices(BASE, tree, 4)
        if p is None:
            continue
        chords = sorted(set(range(7))-set(tree))
        assert all(slack(BASE[e],p) for e in chords)
        for bits in product((0,1), repeat=len(chords)):
            w = [F(0)]*7
            for i, h in zip(chords,bits):
                w[i] = F(h*BASE[i].cap)
            net = net_load(BASE,w,4)
            deficit = [v-u for v,u in zip(NET,net)]
            for j, par, i in reversed(sequence[1:]):
                w[i] = deficit[j] if j==BASE[i].head else -deficit[j]
                deficit[par] += deficit[j]
            if any(x<0 or x>e.cap for x,e in zip(w,BASE)):
                continue
            assert all(0<w[i]<BASE[i].cap for i in tree)
            assert tuple(net_load(BASE,w,4))==NET
            active = frozenset(zip(chords,bits))
            outgoing = {i for i,h in active if (1 if h else -1)*slack(BASE[i],p)>0}
            vertices[tuple(w)] = active, outgoing, tuple(p[j] for j in range(4))
    return vertices


def construct(w):
    # One physical junction port per incidence. The root uses the first port on good zero.
    ports = {j: [] for j in range(4)}
    for i,e in enumerate(BASE):
        ports[e.tail].append(i)
        ports[e.head].append(i)
    ids = {}
    for j in ports:
        for i in ports[j]:
            ids[j,i] = len(ids)
    n = len(ids)
    rows, flows, exceptional, group, initial = [], [], set(), set(), []
    for i,e in enumerate(BASE):
        u = ids[e.tail,i]
        v = ids[e.head,i]
        exponent = e.left.bit_length()-e.right.bit_length()
        steps = abs(exponent)
        # A spacer pair of ordinary goods between consecutive factors ensures disjoint nonunit pipes.
        sequence = []
        for step in range(steps):
            exc = n; exceptional.add(exc); n += 1
            end = v if step==steps-1 else n
            if end!=v:
                n += 1
            sequence.extend([(u, exc, exponent<0), (exc, end, exponent>0)])
            u = end
            if step+1<steps:
                seq_next = n; n+=1
                sequence.append((u,seq_next,False)); u = seq_next
        initial.append(len(rows))
        for t,(a,b,is_b) in enumerate(sequence):
            left = 1+int(is_b and a in exceptional); right = 1+int(is_b and b in exceptional)
            if is_b:
                group.add(len(rows))
            off=F(e.intercept,e.right)*right if t==len(sequence)-1 else F(0)
            rows.append(Row(a,b,e.cap if t==0 else e.cap+2,left,right,off))
            flows.append(w[i]+(t!=0))
    base_reference = FLOWS[0]
    cover = 1+sum(e.cap for e in BASE)
    for j, selection in ports.items():
        shift = F(0)
        for old, following in zip(selection,selection[1:]):
            e = BASE[old]
            shift += (1 if j==e.head else -1)*(w[old]-base_reference[old])
            rows.append(Row(ids[j,old],ids[j,following],2*cover,1,1,F(0)))
            flows.append(cover+shift)
    return rows, flows, n, exceptional, group, initial, ids


def main():
    vs=enumerated_vertices()
    assert len(vs)==20
    subsets={frozenset(s) for active,_,_ in vs.values() for k in range(5) for s in combinations(active,k)}
    for face in subsets:
        assert sum(1 for active,dirs,_ in vs.values() if face<=active and not (dirs-{e for e,_ in face}))==1
    assert len(subsets)==99
    unique, = [w for w,(_,dirs,_) in vs.items() if not dirs]
    assert vs[unique][2] == (0,F(3,4),F(1,2),4)
    common_b = None
    for w,(active,dirs,pbase) in vs.items():
        rows, wnew, n, E, B, first, ids = construct(w)
        for i,e in enumerate(rows):
            assert (e.left,e.right)==tuple(1+int(i in B and j in E) for j in (e.tail,e.head))
        degrees=Counter(j for e in rows for j in (e.head,e.tail))
        assert max(degrees.values())<=3
        doubled=Counter(j for e in rows if e.left!=e.right for j in (e.head,e.tail))
        assert max(doubled.values())==1
        b = net_load(rows,wnew,n)
        if common_b is None:
            common_b=b
        assert b==common_b and all(0<=x<=e.cap for x,e in zip(wnew,rows))
        for j in range(n):
            assert b[j]+sum(e.cap for e in rows if e.tail==j)>0
        tr=[i for i,(x,e) in enumerate(zip(wnew,rows)) if 0<x<e.cap]
        p,_ = tree_prices(rows,tr,n)
        assert p is not None
        assert all(p[new]==pbase[old] for (old,_),new in ids.items())
        lifted_dirs = {i for i,h in active if (1 if h else -1)*slack(rows[first[i]],p)>0}
        assert dirs==lifted_dirs and all(slack(rows[i],p)==0 for i in tr)
    for a,b,expected in zip(FLOWS,FLOWS[1:]+FLOWS[:1],VIOLATIONS):
        basis,outs,p=vs[a]; other=vs[b][0]
        assert len(basis & other)==3
        i,h=next(iter(basis-other))
        assert i in outs and (1 if h else -1)*slack(BASE[i],p)==expected
    print(f'20 original and {n}-good/{len(rows)}-buyer rectangular lifted vertices checked, 99 unique-sink faces, 8 strict cycle edges. Sink {unique}, prices {vs[unique][2]}.')

if __name__=='__main__':
    main()
