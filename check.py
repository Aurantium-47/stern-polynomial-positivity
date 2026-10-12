#!/usr/bin/env python3
"""Exact finite arithmetic checks; the general theorem is proved in Lean.
Python 3.8 or later; no external packages.
"""
from fractions import Fraction
from functools import lru_cache
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(p, q):
    return trim((p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0) for i in range(max(len(p), len(q))))


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return trim(out)


@lru_cache(None)
def stern(n):
    """Coefficients in ascending order, directly from the Stern recurrence."""
    if n == 0:
        return (0,)
    if n == 1:
        return (1,)
    if n % 2 == 0:
        return (0,) + stern(n // 2)
    return add(stern(n // 2), stern(n // 2 + 1))


def evaluate(p, x):
    value = Fraction(0)
    for c in reversed(p):
        value = value * x + c
    return value


def h(n):
    numerator = 2 * (2 ** (2 * n) - 1) * (2 ** (2 * n + 1) + 1)
    assert numerator % 3 == 0
    return numerator // 3 + 1


def main():
    p = stern(183)
    assert p == (1, 5, 9, 7, 3, 1)
    derivative = tuple(i * p[i] for i in range(1, len(p)))
    x, y = Fraction(-2, 3), Fraction(-3, 5)
    assert evaluate(derivative, x) == Fraction(-19, 81)
    assert -1 < x < y < 0
    assert evaluate(p, x) == Fraction(13, 243)
    assert evaluate(p, y) == Fraction(122, 3125)
    assert evaluate(p, y) < evaluate(p, x)
    assert 2 ** (2 * 2 + 4) - 9 * 2 ** (2 + 1) - 1 == 183
    for n in range(21):
        a = (4 ** n - 1) // 3
        A, C = stern(a), stern(a + 1)
        quadratic = add(add(mul((1, 1, 1), mul(A, A)),
                            mul((2, 1), mul(A, C))), mul(C, C))
        assert stern(h(n)) == quadratic
    print(json.dumps({
        "status": "passed",
        "B183_coefficients_ascending": p,
        "derivative_at_minus_two_thirds": str(evaluate(derivative, x)),
        "left_value": str(evaluate(p, x)),
        "right_value": str(evaluate(p, y)),
        "right_minus_left": str(evaluate(p, y) - evaluate(p, x)),
        "quadratic_identity_finite_check": {"n_min": 0, "n_max": 20},
        "scope": "Finite exact checks only; see Lean for universal proofs."
    }, indent=2))


if __name__ == "__main__":
    main()


