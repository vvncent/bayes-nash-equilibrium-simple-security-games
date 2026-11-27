"""Lift an exact directed cycle onto a face of a dense, full, half-quota transport."""
from collections import defaultdict
from fractions import Fraction as F

from verify_pivots import FLOWS, construct, enumerated_vertices, tree_prices


def tree_transport(tree, supply, demand):
    rows = len(supply)
    nodes = list(map(F,supply)) + [-F(c) for c in demand]
    neighbors = defaultdict(list)
    for i,j in tree:
        neighbors[i].append(rows+j)
        neighbors[rows+j].append(i)
    order = [(0, None)]
    seen = {0}
    for a, _ in order:
        for b in neighbors[a]:
            if b not in seen:
                seen.add(b); order.append((b,a))
    assert len(seen)==len(nodes) and len(tree)==len(nodes)-1
    f = {}
    for a,b in reversed(order[1:]):
        if a<rows:
            f[a,b-rows] = nodes[a]
        else:
            f[b,a-rows] = -nodes[a]
        nodes[b] += nodes[a]
    assert nodes[0]==0 and min(f.values())>0
    return f


def quota_vertex(old_vertex):
    rows, w, n, E, B, first, _ = construct(old_vertex)
    m = len(rows)
    J = 2**16
    scale = 7*J
    K = 1+sum(row.cap for row in rows)
    top = [F(0) for _ in range(n)]
    support = set()
    for i,(x,row) in enumerate(zip(w,rows)):
        for j,value in [(row.head,x),(row.tail,row.cap-x)]:
            top[j] += scale*value
            if value>0:
                support.add((i,j))
    top[0]+=2*m
    supply=[scale*row.cap+2 for row in rows]
    f=tree_transport(support,supply,top)
    group = B|{m+1}; exc = E|{n}
    supply.extend([scale*8*K+2,scale*2*K+1]); quota=F(sum(supply[i] for i in group),2)
    base_weight=sum(val for (i,j),val in f.items() if i in B and j in E)
    B_to_S=quota-base_weight
    top += [scale*5*K]; top[0]+=scale*5*K+3
    f[m+1,n]=B_to_S
    f[m+1,0]=supply[m+1]-B_to_S
    f[m,n]=top[n]-B_to_S
    f[m,0]=supply[m]-f[m,n]
    assert min(f.values())>0
    assert all(sum(v for (i,j),v in f.items() if i==k)==val for k,val in enumerate(supply))
    assert all(sum(v for (i,j),v in f.items() if j==k)==val for k,val in enumerate(top))
    assert sum(v for (i,j),v in f.items() if i in group and j in exc)==quota
    assert quota.denominator==2 and len(f)==len(supply)+len(top)
    residue=2*(m+1)+1
    assert [b%J for b in supply] == [2]*(m+1)+[1]
    assert [c%J for c in top]==[residue]+[0]*n
    tr=[i for i,(v,row) in enumerate(zip(w,rows)) if 0<v<row.cap]
    p,_=tree_prices(rows,tr,n);p[n]=F(0)
    u={m:F(0),m+1:F(0)}
    for i,e in enumerate(rows):
        u[i]=(-e.left*p[e.tail] if (i,e.tail) in f else e.intercept-e.right*p[e.head])
    violated=set()
    for i in range(m+2):
        for j in range(n+1):
            if i<m and j==rows[i].tail: a=0
            elif i<m and j==rows[i].head: a=rows[i].intercept
            elif i>=m and j in (0,n): a=0
            else: a=-1000000
            b=1+int(i in group and j in exc)
            g=u[i]+b*p[j]-a
            if (i,j) in f: assert g==0
            else:
                assert g!=0
                if g<0: violated.add((i,j))
    return f,violated,quota,tuple(supply),tuple(top)


def main():
    old=enumerated_vertices()
    current={w:quota_vertex(w) for w in old}
    q,rows,cols=next(iter(current.values()))[2:]
    assert all((q,rows,cols)==v[2:] for v in current.values())
    for i,(x,y) in enumerate(zip(FLOWS,FLOWS[1:]+FLOWS[:1])):
        f, violated=current[x][:2]; g=current[y][0]
        inc, = set(g)-set(f)
        out, = set(f)-set(g)
        assert inc in violated and out not in current[y][1]
    true_vertex, = [w for w, (_,wrong,*_) in current.items() if not wrong]
    assert old[true_vertex][2]==(F(0),F(3,4),F(1,2),F(4))
    print(f'{len(rows)} buyers, {len(cols)} goods, {len(rows)*len(cols)} dense pairs; Q={q}, margin residues verified. All 20 lifted bases and 8 strict quota-pivot comparisons passed.')

if __name__=='__main__':
    main()
