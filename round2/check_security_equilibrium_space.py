"""Exact QF_LRA regressions for the original game's BNE coverage and cutoff geometry."""

from fractions import Fraction as F
import z3

from wardrop.check_wardrop import add, expect, q, rule_out


def conditions(x, f, cutoff, offers, masses, gains, resources):
    tests = [add(*x) == resources, cutoff >= 0, cutoff <= q(max(gains))]
    tests.extend(z3.And(value >= 0, value <= 1) for value in x)
    for i, row in enumerate(offers):
        utility = [q(a) - q(b)*v for (a, b), v in zip(row, x)]
        tests.append(add(*f[i]) == q(masses[i]))
        for j, edge in enumerate(f[i]):
            tests.extend((edge >= 0,
                          z3.Or(edge == 0, z3.And(*(utility[j] >= u for u in utility)))))
    for j, value in enumerate(x):
        score = q(gains[j])*add(*(f[i][j] for i in range(len(masses))))
        tests.extend((z3.Or(value == 0, score >= cutoff),
                      z3.Or(value == 1, score <= cutoff)))
    return z3.And(*tests)


def variables(tag, m, n):
    return ([z3.Real(f"{tag}_x{j}") for j in range(n)],
            [[z3.Real(f"{tag}_f{i}_{j}") for j in range(n)] for i in range(m)],
            z3.Real(f"{tag}_cutoff"))


def unique_cutoff_and_switching_assignments():
    offers = (
        ((5, 8), (F(7, 2), 4), (-10, 1)),
        ((4, 4), (F(11, 2), 8), (-10, 1)),
        ((-10, 1), (-10, 1), (10, 1)),
    )
    third = q(F(1, 3))
    game = (offers, (F(1, 3),)*3, (1,)*3, 1)
    x, f, cutoff = variables("switch", 3, 3)
    solver = z3.SolverFor("QF_LRA")
    solver.add(conditions(x, f, cutoff, *game))
    expect(solver, z3.sat, "game has an equilibrium")
    rule_out(solver, cutoff != third, "some BNE has a different cutoff")

    t, share = z3.Reals("coverage_t assignment_share")
    tie = q(F(3, 8))
    domain = z3.And(t >= q(F(1, 4)), t <= q(F(1, 2)))
    assignment = [
        [share*third, (1-share)*third, q(0)],
        [(1-share)*third, share*third, q(0)],
        [q(0), q(0), third],
    ]
    expected = z3.Or(z3.And(t < tie, share == 1),
                     z3.And(t == tie, share >= 0, share <= 1),
                     z3.And(t > tie, share == 0))
    path = z3.SolverFor("QF_LRA")
    path.add(domain)
    rule_out(path, z3.Xor(conditions([t, t, 1-2*t], assignment, third, *game), expected),
             "literal BNE conditions differ from the entire claimed assignment path")
    solver.add(domain, x[0] == t, x[1] == t, f[0][0] == share*third)
    matches = [f[i][j] == assignment[i][j] for i in range(3) for j in range(3)]
    rule_out(solver, z3.Not(z3.And(expected, *matches)), "one slice equilibrium was omitted")


def unique_coverage_and_cutoff_interval():
    game = ((((10, 1), (0, 1)),), (1,), (1, 1), 1)
    x, f, cutoff = variables("interval", 1, 2)
    solver = z3.SolverFor("QF_LRA")
    direct = conditions(x, f, cutoff, *game)
    shape = z3.And(x[0] == 1, x[1] == 0, f[0][0] == 1, f[0][1] == 0,
                   cutoff >= 0, cutoff <= 1)
    rule_out(solver, z3.Xor(direct, shape), "full BNE text differs from the proposed cutoff segment")
    solver.add(direct, cutoff == q(F(1, 2)))
    expect(solver, z3.sat, "an interior cutoff clears")


def published_nonconvex_example():
    third = q(F(1, 3))
    offers = (
        ((2, 1), (3, 6), (0, 1)),
        ((3, 4), (2, 1), (0, 1)),
        ((0, 1), (0, 1), (2, 1)),
    )
    game = (offers, (F(1, 3),)*3, (1,)*3, 1)
    p = [q(F(n, 8)) for n in (3, 3, 2)]
    t = [q(F(n, 23)) for n in (7, 5, 11)]
    r = [q(F(n, 8)) for n in (1, 1, 6)]
    s = z3.Real("published_segment_parameter")
    solvent = z3.SolverFor("QF_LRA")
    solvent.add(0 <= s, s <= 1)
    for start, end, first_share in ((p, t, q(1)), (t, t, s), (t, r, q(0))):
        x = [a+(b-a)*s for a, b in zip(start, end)]
        f = [[first_share*third, (1-first_share)*third, q(0)],
             [(1-first_share)*third, first_share*third, q(0)],
             [q(0), q(0), third]]
        rule_out(solvent, z3.Not(conditions(x, f, third, *game)),
                 "the explicit nonconvex example's detour failed")
    x, f, cutoff = variables("midpoint", 3, 3)
    check = z3.SolverFor("QF_LRA")
    check.add(conditions(x, f, cutoff, *game))
    rule_out(check, z3.And(*(2*a == left+right for a, left, right in zip(x, p, r))),
             "the published straight midpoint unexpectedly admits a BNE")


if __name__ == "__main__":
    unique_cutoff_and_switching_assignments()
    unique_coverage_and_cutoff_interval()
    published_nonconvex_example()
    print("Three-target game: all BNE use cutoff 1/3; the full real switching path and tie fiber pass.")
    print("Two-target game: exact full BNE set has one coverage and all cutoffs in [0,1].")
    print("Published nonconvex example: the entire detour through (7,5,11)/23 clears; the straight midpoint cannot.")
