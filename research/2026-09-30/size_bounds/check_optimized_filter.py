#!/usr/bin/env python3
"""Independent exact verification of the optimized zero-mean parity filter."""
from fractions import Fraction as Q
import json
from independent_checks import integrated_binomials, v2


def binomials(y, degree):
    values = [Q(1)]
    for j in range(1, degree+1):
        values.append(values[-1]*(y-j+1)/j)
    return values


def check():
    rows = []
    evaluations = 0
    for depth in range(1, 7):
        scale = 2**depth
        moments = integrated_binomials(scale, 40)
        for j, moment in enumerate(moments):
            assert v2(moment) >= -(j//scale)
            if j % scale == 0:
                assert v2(moment) == -(j//scale)
        for degree in range(2, 41, 2):
            integral = sum(((-2)**(j-1)*moments[j]
                            for j in range(1, degree+1)), Q(0))
            pivot = scale*(degree//scale)
            correction = -integral/(2**degree*moments[pivot])
            assert v2(correction) >= 0
            assert integral+2**degree*correction*moments[pivot] == 0
            for numerator in range(-6, 7):
                for denominator in [1, 3, 5]:
                    y = Q(numerator, denominator)
                    choose = binomials(y, degree)
                    value = sum(((-2)**(j-1)*choose[j]
                                 for j in range(1, degree+1)), Q(0))
                    value += 2**degree*correction*choose[pivot]
                    assert v2(value-(numerator % 2)) >= degree
                    evaluations += 1
            rows.append(dict(degree=degree, depth=depth, pivot=pivot,
                             correction=str(correction),
                             correction_valuation=None if correction == 0 else v2(correction)))
    return dict(filters_checked=len(rows), exact_filter_evaluations=evaluations, rows=rows)


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
