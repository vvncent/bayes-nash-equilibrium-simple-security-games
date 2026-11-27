"""Exact point-versus-segment and weighted-LP witnesses, using Z3 QF_LRA."""

from fractions import Fraction as F

import z3


def q(value):
    value = F(value)
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def switch(threshold, left=1, right=1):
    return ((left * threshold, left), (right * (1 - threshold), right))


HALF = F(1, 2)
QUARTER = F(1, 4)
ROWS = (
    switch(HALF), switch(HALF, 3, 5),
    ((HALF, 1), (-2, 1)), ((-2, 1), (HALF, 1)),
    switch(3 * QUARTER), switch(QUARTER),
)


def exclude(statement, label):
    solver = z3.SolverFor("QF_LRA")
    solver.add(statement)
    result = solver.check()
    if result != z3.unsat:
        detail = solver.model() if result == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{label}: {result}, {detail}")


def offers(x):
    return [(q(a) - q(b) * x, q(c) - q(d) * (1 - x))
            for (a, b), (c, d) in ROWS]


def conditions(x, first, masses, weighted):
    """The same buyer conditions, with physical or slope-weighted defender scores."""
    constraints = [x >= 0, x <= 1]
    left_score, right_score = [], []
    for mass, first_mass, row, (left, right) in zip(masses, first, ROWS, offers(x)):
        second_mass = q(mass) - first_mass
        constraints += [first_mass >= 0, second_mass >= 0,
                        z3.Or(first_mass == 0, left >= right),
                        z3.Or(second_mass == 0, right >= left)]
        left_score.append(first_mass * q(row[0][1] if weighted else 1))
        right_score.append(second_mass * q(row[1][1] if weighted else 1))
    difference = z3.Sum(*left_score) - z3.Sum(*right_score)
    constraints += [z3.Or(x == 0, difference >= 0), z3.Or(x == 1, difference <= 0)]
    return z3.And(*constraints)


def objective(x, masses):
    return z3.Sum(*(q(mass) * z3.If(left >= right, left, right)
                    for mass, (left, right) in zip(masses, offers(x))))


def main():
    x = z3.Real("first_coverage")
    first = tuple(z3.Real(f"first_mass{i}") for i in range(len(ROWS)))
    a, b, left, right, c, u = first
    point = tuple(F(v, 25) for v in (4, 2, 11, 3, 2, 3))
    segment = tuple(F(v, 25) for v in (8, 1, 9, 2, 2, 3))

    physical_point = z3.And(x == q(3 * QUARTER), a == 0, b == 0, left == q(point[2]),
                            right == 0, c == q(F(3, 50)), u == 0)
    physical_segment = z3.And(x == q(HALF), a + b == q(F(3, 50)),
                              b >= 0, b <= q(F(1, 25)), left == q(segment[2]),
                              right == 0, c == q(segment[4]), u == 0)
    for name, masses, physical in (("point", point, physical_point),
                                   ("segment", segment, physical_segment)):
        true_bne = conditions(x, first, masses, weighted=False)
        exclude(z3.Xor(true_bne, physical), f"{name}: physical equilibrium set")
        weighted_face = z3.And(x == q(HALF), 2 * a + 8 * b == q(F(7, 25)),
                               b >= 0, b <= q(F(7, 200)), left == q(masses[2]),
                               right == 0, c == q(masses[4]), u == 0)
        kkt = conditions(x, first, masses, weighted=True)
        exclude(z3.Xor(kkt, weighted_face), f"{name}: complete LP saddle set")

    phi_point, phi_segment = objective(x, point), objective(x, segment)
    exclude(z3.And(x >= 0, x <= 1, phi_point != phi_segment), "two value functions")
    exclude(z3.And(x >= 0, x <= 1, x != q(HALF), phi_point <= q(F(1, 20))),
            "unique LP minimizer")
    assert z3.is_true(z3.simplify(z3.substitute(phi_point, (x, q(HALF))) == q(F(1, 20))))

    t1, t2 = z3.Reals("anchor_1 anchor_2")
    anchor_constraints = []
    for i in (0, 1, 4):
        (a1, b1), (a2, b2) = ROWS[i]
        anchor_constraints.append(q(a1) - q(b1) * t1 == q(a2) - q(b2) * t2)
    exclude(z3.And(*anchor_constraints), "common anchor on eligible edges")
    print("Four full real set equalities passed (physical and weighted, both priors).")
    print("The full scalar objectives coincide; each has unique minimum 1/20 at 1/2.")
    print("True coverage is 3/4 in the point game and 1/2 in the segment game.")
    print("The eligible edges admit no common affine anchor.")


if __name__ == "__main__":
    main()
