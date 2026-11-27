"""Polynomial-bit recovery for signed, non-replicating real comparator networks."""
from collections import deque
from fractions import Fraction


def _literal_form(literal):
    if literal.negated:
        return 1, {literal.wire: -1}
    return 0, {literal.wire: 1}


def _cell_equations(network, point):
    # Lazy import lets the physical market use this module for its decoder.
    if __package__:
        from .opdc_comparator_market import Comparator, Unary
    else:
        from opdc_comparator_market import Comparator, Unary

    rows = [None] * network.size
    for gate in network.gates:
        if isinstance(gate, Comparator):
            c, left = _literal_form(gate.left)
            d, right = _literal_form(gate.right)
            if left.keys() & right.keys():
                raise ValueError('A comparator cannot consume one wire twice')
            summed = left | right
            lower = gate.left.read(point) + gate.right.read(point) <= 1
            if lower:
                outputs = ((gate.and_output, (0, {})), (gate.or_output, (c + d, summed)))
            else:
                outputs = ((gate.and_output, (c + d - 1, summed)), (gate.or_output, (1, {})))
        elif isinstance(gate, Unary):
            outputs = ((gate.output, _literal_form(gate.source)),)
        else:
            outputs = ((gate.output, (int(gate.value), {})),)
        for dest, (offset, coefficients) in outputs:
            if dest is None:
                continue
            if dest.negated:
                offset = 1 - offset
                coefficients = {i: -sign for i, sign in coefficients.items()}
            rows[dest.wire] = (offset, coefficients)
    return rows


def recover_approximate(network, estimate):
    """Recover an exact point in the observed cell when the max residual is < 1/(16 n)."""
    estimate = tuple(Fraction(x) for x in estimate)
    n = network.size
    if len(estimate) != n or any(x < 0 or x > 1 for x in estimate):
        raise ValueError('The estimate must lie in the network cube')
    residual = max(abs(x - y) for x, y in zip(estimate, network.evaluate(estimate)))
    if residual >= Fraction(1, 16 * n):
        raise ValueError('This estimate exceeds the inverse-polynomial recovery tolerance')
    rows = _cell_equations(network, estimate)
    offsets = [Fraction(a) for a, _ in rows]
    indegree = [len(inc) for _, inc in rows]
    successor = [None] * n
    for head, (_, inc) in enumerate(rows):
        for tail, sign in inc.items():
            if successor[tail] is not None:
                raise ValueError('The active network has a repeated input')
            successor[tail] = (head, sign)
    # Accumulate exact integer trees into their unique successors.
    result = [None] * n
    ready = deque(i for i in range(n) if indegree[i] == 0)
    while ready:
        u = ready.popleft()
        result[u] = offsets[u]
        edge = successor[u]
        if edge is None:
            continue
        v, sign = edge
        offsets[v] += sign * result[u]
        indegree[v] -= 1
        if indegree[v] == 0:
            ready.append(v)
    # Removing acyclic vertices leaves disjoint signed cycles. Parameterize one at a time.
    for root in range(n):
        if result[root] is not None:
            continue
        v = root
        forms = {root: (1, Fraction(0))}
        while True:
            dest, edge_sign = successor[v]
            coefficient, offset = forms[v]
            coefficient *= edge_sign
            offset = edge_sign * offset + offsets[dest]
            if dest == root:
                break
            forms[dest] = coefficient, offset
            v = dest
        if coefficient == -1:
            parameter = offset / 2
        else:
            if offset != 0:
                raise ArithmeticError('An even signed cycle has nonzero integer net translation')
            lower, upper = Fraction(0), Fraction(1)
            for sign, value in forms.values():
                a, b = sorted((-sign * value, sign * (1 - value)))
                lower, upper = max(lower, a), min(upper, b)
            if lower > upper:
                raise ArithmeticError('The signed cycle has incompatible parameter intervals')
            parameter = min(upper, max(lower, estimate[root]))
        for v, (sign, offset) in forms.items():
            result[v] = sign * parameter + offset
    result = tuple(result)
    if any(x < 0 or x > 1 for x in result) or network.evaluate(result) != result:
        raise ArithmeticError('The recovered point fails the network equations')
    return result


def solve_by_damping(network):
    """Return an exact real fixed point using polynomially many rational operations."""
    n = network.size
    alpha = Fraction(1, 64 * n)
    tolerance = Fraction(1, 16 * n)
    x = (Fraction(1, 2),) * n
    while True:
        targets = network.evaluate(x)
        if max(abs(y - value) for y, value in zip(targets, x)) < tolerance:
            return recover_approximate(network, x)
        x = tuple((1 - alpha) * y + alpha / 2 for y in targets)
