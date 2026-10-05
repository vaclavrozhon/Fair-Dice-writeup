"""Exact small-instance checks for shelf_bound.tex; standard library only."""
from fractions import Fraction
from itertools import permutations
from math import factorial, exp, sqrt, ceil


def pattern_count(word, pattern):
    counts = [1] + [0] * len(pattern)
    index = {letter: i + 1 for i, letter in enumerate(pattern)}
    for letter in word:
        j = index.get(letter)
        if j is not None:
            counts[j] += counts[j - 1]
    return counts[-1]


def maximum_formula(n, m):
    # Integer coefficient of ((1+z)/(1-z))^m, divided by (2m)^n.
    coefficients = [1] + [0] * n
    for _ in range(m):
        coefficients = [sum(coefficients[k] * (1 if k == r else 2)
                            for k in range(r + 1)) for r in range(n + 1)]
    return Fraction(factorial(n) * coefficients[n], (2 * m) ** n)


def verify():
    checked = 0
    for n in range(2, 8):
        block = list(range(n)) + list(range(n - 1, -1, -1))
        for m in range(1, 7):
            ratios = [Fraction(factorial(n) * pattern_count(block * m, p),
                               (2 * m) ** n) for p in permutations(range(n))]
            lo, hi = min(ratios), max(ratios)
            assert hi == maximum_formula(n, m)
            falling3 = n * (n - 1) * (n - 2)
            assert lo >= 1 - Fraction(falling3, 6 * m * m)
            assert hi >= 1 + Fraction(falling3, 12 * m * m)
            if m > n / 2:
                exponent = Fraction(falling3, 12 * m * m - 3 * n * n)
                assert float(hi) <= exp(float(exponent)) + 1e-12
            checked += factorial(n)
            print(f"n={n} m={m}: min={lo}, max={hi}")
    for n in range(3, 21):
        for epsilon in (1, .5, .1, .01):
            m = ceil(sqrt(n*n/4 + n*(n-1)*(n-2)/(6*epsilon)))
            assert float(maximum_formula(n, m)) <= 1 + epsilon + 1e-12
            assert n*(n-1)*(n-2)/(6*m*m) <= epsilon + 1e-12
    print(f"PASS: checked {checked} permutation counts and 72 parameter choices")


if __name__ == "__main__":
    verify()
