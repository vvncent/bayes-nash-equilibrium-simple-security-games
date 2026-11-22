"""Bayesian simple security games -> CE games (Section 3.1 reduction), and an
independent exact Bayes-Nash check written directly in security-game terms."""
from fractions import Fraction as F
import random

from lck_alg import CEGame


class SecurityGame:
    def __init__(self, rd, prior, uu, uc, ddu, ddc):
        # prior[i]; attacker uu[i][t] uncovered, uc[i][t] covered; defender ddu[t], ddc[t]
        self.rd, self.prior = F(rd), [F(p) for p in prior]
        self.uu = [[F(v) for v in row] for row in uu]
        self.uc = [[F(v) for v in row] for row in uc]
        self.ddu, self.ddc = [F(v) for v in ddu], [F(v) for v in ddc]
        self.n, self.m = len(prior), len(ddu)

    def to_ce(self):
        n, m = self.n, self.m
        return CEGame(
            r0=self.rd, l0=[1] * m, b0=[0] * m, d0=[self.ddc[t] - self.ddu[t] for t in range(m)],
            r=list(self.prior), l=[[self.prior[i]] * m for i in range(n)],
            b=[list(self.uu[i]) for i in range(n)],
            d=[[self.uc[i][t] - self.uu[i][t] for t in range(m)] for i in range(n)])


def is_bne_security(S, coverage, attack):
    """coverage[t] marginal; attack[i][t] = probability type i attacks t (sums to 1)."""
    m, n = S.m, S.n
    if sum(coverage) != S.rd or any(not (0 <= c <= 1) for c in coverage):
        return False
    for i in range(n):
        if sum(attack[i]) != 1 or any(q < 0 for q in attack[i]):
            return False
        pay = [coverage[t] * S.uc[i][t] + (1 - coverage[t]) * S.uu[i][t] for t in range(m)]
        best = max(pay)
        if any(attack[i][t] > 0 and pay[t] != best for t in range(m)):
            return False
    marg = [sum(S.prior[i] * attack[i][t] for i in range(n)) * (S.ddc[t] - S.ddu[t]) for t in range(m)]
    lo = [marg[t] for t in range(m) if coverage[t] < 1]
    hi = [marg[t] for t in range(m) if coverage[t] > 0]
    return not (lo and hi and max(lo) > min(hi))


def random_security_game(rng, n, m, R):
    rd = rng.randint(1, m - 1)
    w = [rng.randint(1, 5) for _ in range(n)]
    prior = [F(v, sum(w)) for v in w]
    uu = [[rng.randint(0, R) for _ in range(m)] for _ in range(n)]
    uc = [[uu[i][t] - rng.randint(1, R) for t in range(m)] for i in range(n)]
    ddu = [-rng.randint(0, R) for _ in range(m)]
    ddc = [ddu[t] + rng.randint(1, R) for t in range(m)]
    return SecurityGame(rd, prior, uu, uc, ddu, ddc)
