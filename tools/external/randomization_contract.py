"""Independent finite-field span checks and ideal-draw bounds for the research contract."""
from fractions import Fraction


def maximum_atom(prime, bits=64):
    if prime < 2 or bits < 1:
        raise ValueError('positive draw width and prime characteristic required')
    words = 1 << bits
    return Fraction((words + prime - 2) // (prime - 1), words)


def signature_draws(prime):
    if prime <= 3:
        return None
    count, power = 1, prime - 1
    while power < 1 << 31:
        count, power = count + 1, power * (prime - 1)
    return count


def plain_bound(prime):
    alpha = maximum_atom(prime)
    return min(Fraction(1), alpha**2 / ((1-alpha) * (1-alpha**2))) if alpha < 1 else Fraction(1)


def check_span(rows, candidates, witnesses, prime, complete=True):
    if not complete:
        return False
    width = len(rows[0]) if rows else len(candidates[0]) if candidates else 0
    if len(candidates) != len(witnesses):
        raise ValueError('one combination certificate per candidate row required')
    for values, expected in [(rows, width), (candidates, width), (witnesses, len(rows))]:
        if any(len(row) != expected or any(type(c) is not int or not 0 <= c < prime for c in row)
               for row in values):
            raise ValueError('invalid row dimensions or noncanonical coefficients')
    # Certificates establish the inclusion a residual-only guard cannot establish on its own.
    for candidate, witness in zip(candidates, witnesses):
        if any(candidate[col] != sum(c * rows[i][col] for i, c in enumerate(witness)) % prime
               for col in range(width)):
            return False
    pivots = {}
    for candidate in candidates:
        row = _remainder(candidate, pivots, prime)
        lead = next((i for i, value in enumerate(row) if value), None)
        if lead is not None:
            inverse = pow(row[lead], -1, prime)
            pivots[lead] = [c * inverse % prime for c in row]
    return all(not any(_remainder(row, pivots, prime)) for row in rows)


def _remainder(row, pivots, prime):
    result = list(row)
    for col, pivot in sorted(pivots.items()):
        coefficient = result[col]
        if coefficient:
            result = [(a-coefficient*b) % prime for a, b in zip(result, pivot)]
    return result
