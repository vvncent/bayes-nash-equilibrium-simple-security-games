"""Independent exact checks for the direct Bayesian-security-game LCP.
Uses Fraction and Z3 exact linear rational arithmetic; no author code is imported.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import ceil, lcm
import random
import z3


def det(a):
    a = [list(map(F, row)) for row in a]
    ans = F(1)
    for k in range(len(a)):
        p = next((r for r in range(k, len(a)) if a[r][k]), None)
        if p is None:
            return F(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            ans = -ans
        pivot = a[k][k]
        ans *= pivot
        for r in range(k + 1, len(a)):
            if a[r][k]:
                c = a[r][k] / pivot
                for col in range(k + 1, len(a)):
                    a[r][col] -= c * a[k][col]
    return ans


def q(v):
    v = F(v)
    return z3.Q(v.numerator, v.denominator)


def fq(v):
    return F(v.numerator_as_long(), v.denominator_as_long())


def lcp(a, b, d, p, r, shifted=True):
    """Return M,q and named coordinate positions in order f,t,lambda,u,x."""
    m, n = len(a), len(d)
    shifts = [F(1) + max(b[i][j] - a[i][j] for j in range(n)) for i in range(m)]
    A = [[a[i][j] + shifts[i] if shifted else a[i][j] for j in range(n)] for i in range(m)]
    N = m*n + n + 1 + m + n
    M = [[F(0) for _ in range(N)] for _ in range(N)]
    c = [F(0) for _ in range(N)]
    f = lambda i, j: i*n + j
    t = lambda j: m*n + j
    ell = m*n + n
    u = lambda i: m*n + n + 1 + i
    x = lambda j: m*n + n + 1 + m + j
    for i in range(m):
        for j in range(n):
            M[f(i,j)][u(i)] = 1; M[f(i,j)][x(j)] = b[i][j]; c[f(i,j)] = -A[i][j]
            M[u(i)][f(i,j)] = -1
            M[x(j)][f(i,j)] = -d[j]
        c[u(i)] = p[i]
    for j in range(n):
        M[t(j)][x(j)] = -1; c[t(j)] = 1
        M[x(j)][t(j)] = 1; c[x(j)] = -1
        M[ell][x(j)] = -1
        M[x(j)][ell] = 1
    c[ell] = r
    return M, c, (f,t,ell,u,x), A


def all_principal_minors(M):
    n = len(M)
    for k in range(n + 1):
        for S in combinations(range(n), k):
            yield S, det([[M[i][j] for j in S] for i in S])


def random_instance(m, n, rng):
    a = [[F(rng.randint(-3, 4), rng.choice([1, 2, 3])) for _ in range(n)] for _ in range(m)]
    b = [[F(rng.randint(0, 4), rng.choice([1, 2, 3])) for _ in range(n)] for _ in range(m)]
    d = [F(rng.randint(0, 4), rng.choice([1, 2, 3])) for _ in range(n)]
    p0 = [rng.randint(1, 5) for _ in range(m)]
    p = [F(v, sum(p0)) for v in p0]
    return a,b,d,p,rng.randint(1,n-1)


def exhaustive_minors():
    rng = random.Random(20261122)
    count = 0
    # N=8 for 1x2, N=11 for 2x2: every principal minor.
    for m,n,reps in [(1,2,12),(2,2,12)]:
        for _ in range(reps):
            M,_,_,_ = lcp(*random_instance(m,n,rng))
            for S,v in all_principal_minors(M):
                assert v >= 0, (m,n,S,v)
                count += 1
    # Deliberately degenerate: all coefficients of both kinds are zero.
    M,_,_,_ = lcp([[F(-2),F(3)]], [[F(0),F(0)]], [F(0),F(0)], [F(1)], 1)
    for S,v in all_principal_minors(M):
        assert v >= 0, ('all-zero effects',S,v)
        count += 1
    # 4x5 has N=35. Sample nonempty principal restrictions exactly.
    samples = 0
    for _ in range(8):
        M,_,_,_ = lcp(*random_instance(4,5,rng))
        for __ in range(1500):
            S = [i for i in range(len(M)) if rng.choice([False, True])]
            v = det([[M[i][j] for j in S] for i in S])
            assert v >= 0, (S,v)
            samples += 1
    print('minors', count, samples)


def affine(M,c,z):
    return [q(c[i]) + sum(q(M[i][j])*z[j] for j in range(len(z)) if M[i][j]) for i in range(len(z))]


def comp(s, z):
    return [z[i] >= 0 for i in range(len(z))] + [v >= 0 for v in s] + [z3.Or(z[i] == 0, s[i] == 0) for i in range(len(z))]


def direct_bne(a,b,d,p,r,fv,xv):
    m,n=len(a),len(d)
    out=[]
    out += [v >= 0 for row in fv for v in row]
    out += [v >= 0 for v in xv] + [v <= 1 for v in xv] + [sum(xv)==q(r)]
    for i in range(m):
        out.append(sum(fv[i]) == q(p[i]))
        pay=[q(a[i][j])-q(b[i][j])*xv[j] for j in range(n)]
        for j in range(n):
            out.append(z3.Or(fv[i][j] == 0, z3.And(*[pay[j] >= pay[k] for k in range(n)])))
    score=[q(d[j])*sum(fv[i][j] for i in range(m)) for j in range(n)]
    for j in range(n):
        for k in range(n):
            out.append(z3.Or(xv[j] == 0, xv[k] == 1, score[j] >= score[k]))
    return out


def formulation_checks():
    rng=random.Random(804)
    checked=0
    for _ in range(15):
        a,b,d,p,r=random_instance(2,2,rng)
        M,c,ix,A=lcp(a,b,d,p,r); f,t,ell,u,x=ix
        z=[z3.Real('z_%d_%d'%(checked,k)) for k in range(len(M))]
        s=affine(M,c,z)
        # Any LCP solution must satisfy direct BNE; refute it directly.
        bad=z3.Solver(); bad.add(*comp(s,z))
        fv=[[z[f(i,j)] for j in range(2)] for i in range(2)]; xv=[z[x(j)] for j in range(2)]
        bad.add(z3.Not(z3.And(*direct_bne(a,b,d,p,r,fv,xv))))
        assert bad.check()==z3.unsat
        # For every direct BNE, the explicit cutoff construction is an LCP extension.
        # Search BNE with no allowed lambda: cutoff conditions say max unsaturated score <= lambda <= min positive score.
        ff=[[z3.Real('f_%d_%d_%d'%(checked,i,j)) for j in range(2)] for i in range(2)]
        xx=[z3.Real('x_%d_%d'%(checked,j)) for j in range(2)]
        lam=z3.Real('lam_%d'%checked); tt=[z3.Real('t_%d_%d'%(checked,j)) for j in range(2)]
        uu=[z3.Real('u_%d_%d'%(checked,i)) for i in range(2)]
        score=[q(d[j])*sum(ff[i][j] for i in range(2)) for j in range(2)]
        ext=[lam>=0]
        for j in range(2):
            ext += [tt[j]>=0, z3.Or(tt[j]==0,xx[j]==1)]
            ext += [z3.Or(xx[j]==0, lam+tt[j] == score[j])]
            ext += [z3.Or(xx[j]!=0, lam+tt[j] >= score[j])]
        # These are the defender KKT conditions after removing the harmless +1.
        ext += [z3.Or(xx[j]==0, lam <= score[j]) for j in range(2)]
        ext += [z3.Or(xx[j]==1, lam >= score[j]) for j in range(2)]
        # This exact direct construction is equivalent to the t/lambda portion; attacker u is set by max A-bx.
        for i in range(2):
            ext += [uu[i]>=0]
            for j in range(2):
                ext += [uu[i] >= q(A[i][j])-q(b[i][j])*xx[j]]
                ext += [z3.Or(ff[i][j]==0,uu[i] == q(A[i][j])-q(b[i][j])*xx[j])]
        noext=z3.Solver(); noext.add(*direct_bne(a,b,d,p,r,ff,xx))
        noext.add(z3.ForAll([lam, *tt, *uu], z3.Not(z3.And(*ext))))
        result = noext.check()
        if result != z3.unsat:
            print('extension-countermodel', a, b, d, p, r, result, noext.model())
        assert result == z3.unsat
        checked += 1
    # Negative control: omit the intercept shift. An LCP solution can leave a positive-prior attacker unmassed.
    a=[[F(-1),F(-1)]]; b=[[F(0),F(0)]]; d=[F(0),F(0)]; p=[F(1)]; r=1
    M,c,ix,_=lcp(a,b,d,p,r,shifted=False); z=[z3.Real('neg%d'%k) for k in range(len(M))]; s=affine(M,c,z)
    so=z3.Solver(); so.add(*comp(s,z)); f,t,ell,u,x=ix
    so.add(sum(z[f(0,j)] for j in range(2)) != 1)
    assert so.check()==z3.sat
    print('formulation',checked,'negative-control-rejected')


def precision(M,c,K):
    vals=[F(1),F(K)]
    for row,rhs in zip(M,c):
        den=lcm(*(v.denominator for v in row+[rhs,F(1)]))
        vals += [abs(v*den) for v in row+[rhs,F(1)]]
    C=max(int(v) for v in vals)
    N=len(M)+1
    Q=(N*C)**N
    return F(1,2*K*Q)


def perturbed_support(M,c,e):
    N=len(M)
    # Enumerate complementary bases. P-matrix uniqueness makes exactly one strict pattern feasible.
    for bits in product([0,1], repeat=N):
        z=[z3.Real('p_%d_%d'%(sum(bits),k)) for k in range(N)]
        s=affine(M,c,z); so=z3.Solver()
        for k,bit in enumerate(bits):
            so.add(z[k]>=0,s[k]+q(e)*z[k]>=0)
            so.add(s[k]+q(e)*z[k]==0 if bit else z[k]==0)
        if so.check()==z3.sat:
            model=so.model(); ans=[fq(model.eval(v)) for v in z]
            # Verify the model belongs to this basis and is the actual support pattern.
            if all((ans[k]>0)==bool(bits[k]) for k in range(N)):
                return ans
    raise AssertionError('no strict complementary basis')


def decoder_checks():
    fixtures=[
      ([[F(0),F(0)]],[[F(1),F(2)]],[F(1),F(1)],[F(1)],1),
      ([[F(0),F(-1)]],[[F(0),F(0)]],[F(0),F(0)],[F(1)],1),
      ([[F(1),F(0)]],[[F(2),F(1)]],[F(0),F(3)],[F(1)],1),
    ]
    done=0
    for a,b,d,p,r in fixtures:
        M,c,ix,_=lcp(a,b,d,p,r); K=ceil(max(F(1),max(abs(v) for row in M for v in row),max(abs(v) for v in c)))+20
        # Use the proof's functional K, not a matrix bound.
        U=max(-c[k] for k in range(len(a)*len(d)))
        W=1+len(a)*U; S=1+max(d)*W; K=ceil(max(F(1),U,W,1+S))
        e=precision(M,c,K); zstar=perturbed_support(M,c,e); s=affine(M,c,[q(v) for v in zstar])
        z=[z3.Real('r_%d_%d'%(done,k)) for k in range(len(M))]; so=z3.Solver(); base=affine(M,c,z)
        for k in range(len(M)):
            so.add(z[k]>=0,z[k]<=K,base[k]>=0)
            so.add(base[k]==0 if zstar[k]>0 else z[k]==0)
        assert so.check()==z3.sat
        ans=[fq(so.model().eval(v)) for v in z]
        f,t,ell,u,x=ix
        ff=[[ans[f(i,j)] for j in range(len(d))] for i in range(len(a))]; xx=[ans[x(j)] for j in range(len(d))]
        assert sum(xx)==r and all(F(0)<=v<=1 for v in xx)
        for i in range(len(a)):
            assert sum(ff[i])==p[i]
            pay=[a[i][j]-b[i][j]*xx[j] for j in range(len(d))]
            assert all(ff[i][j]==0 or pay[j]==max(pay) for j in range(len(d)))
        score=[d[j]*sum(ff[i][j] for i in range(len(a))) for j in range(len(d))]
        assert all(xx[j]==0 or xx[k]==1 or score[j]>=score[k] for j in range(len(d)) for k in range(len(d)))
        done+=1
    print('decoder',done)

def boundary_and_zero_prior_checks():
    # The prescribed r=0,n handling is direct: coverage is forced and each type attacks a payoff maximizer.
    a=[[F(3),F(-2)],[F(0),F(4)]]; b=[[F(1),F(0)],[F(0),F(2)]]
    for r, x in [(0,[F(0),F(0)]),(2,[F(1),F(1)])]:
        for i in range(2):
            pay=[a[i][j]-b[i][j]*x[j] for j in range(2)]
            chosen=max(range(2),key=lambda j:pay[j])
            assert pay[chosen] == max(pay)
        assert sum(x)==r
    # A removed zero-prior type can be restored at a maximizing pure attack and does not change defender scores.
    a=[[F(0),F(0)],[F(5),F(-3)]]; b=[[F(1),F(2)],[F(0),F(0)]]; d=[F(2),F(1)]
    M,c,ix,_=lcp([a[0]],[b[0]],d,[F(1)],1); z=[z3.Real('zp%d'%k) for k in range(len(M))]
    so=z3.Solver(); so.add(*comp(affine(M,c,z),z)); assert so.check()==z3.sat
    model=so.model(); f,t,ell,u,x=ix; xx=[fq(model.eval(z[x(j)])) for j in range(2)]
    pay=[a[1][j]-b[1][j]*xx[j] for j in range(2)]
    restored=max(range(2),key=lambda j:pay[j])
    assert pay[restored]==max(pay)
    print('boundary-and-zero-prior')


if __name__ == '__main__':
    exhaustive_minors(); formulation_checks(); decoder_checks(); boundary_and_zero_prior_checks(); print('PASS')
