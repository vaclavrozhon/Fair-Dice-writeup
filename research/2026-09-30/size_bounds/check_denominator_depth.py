#!/usr/bin/env python3
"""Exact checks of the denominator-depth interval-integral estimate.

Builds H in the rational binomial basis and integrates over Q directly;
no cyclotomic or generating-function identities are used by this checker.
"""
from fractions import Fraction
from math import comb
import json
from independent_checks import integrated_binomials


def valuation(q, p):
    q = Fraction(q)
    if not q:
        return None
    numerator, denominator = abs(q.numerator), q.denominator
    value = 0
    while numerator % p == 0:
        numerator //= p
        value += 1
    while denominator % p == 0:
        denominator //= p
        value -= 1
    return value


def run():
    rows = []
    degree = 60
    for p in [2, 3, 5, 7, 11]:
        for depth in range(1, 5):
            for unit in [1, 2 if p != 2 else 3]:
                scale = p**depth * unit
                moments = integrated_binomials(scale, degree)
                integral = Fraction(0)
                tight = []
                for r in range(1, degree+1):
                    coefficient = -sum((-1)**(r-k)*comb(r, k)
                                       for k in range(0, r+1, p))
                    integral += coefficient * moments[r]
                    denominator = (p-1)*p**depth
                    numerator = (p**depth-1)*(r+1)
                    bound = (numerator + denominator-1)//denominator-1
                    v = valuation(integral, p)
                    assert v is None or v >= bound, (p, depth, unit, r, v, bound)
                    if v == bound:
                        tight.append(r)
                rows.append(dict(prime=p, depth=depth, scale_unit=unit,
                                 degrees_checked=degree, tight_degrees=tight))
    return dict(total_integral_checks=degree*len(rows), rows=rows)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
