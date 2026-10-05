"""Exact checks supporting optimized_two_adic_filter.tex; no float arithmetic."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json


def valuation(x):
    x = Q(x)
    if not x:
        return 10**9
    num, den, v = x.numerator, x.denominator, 0
    while num % 2 == 0:
        num //= 2
        v += 1
    while den % 2 == 0:
        den //= 2
        v -= 1
    return v


def integral(poly, scale):
    return sum(c * Q(scale**j, j + 1) for j, c in enumerate(poly))


def evaluate(poly, x):
    result = Q(0)
    for c in reversed(poly):
        result = result * x + c
    return result


max_degree = 40
binomial = [[Q(1)]]
for degree in range(1, max_degree + 1):
    poly = [Q(0)] * (degree + 1)
    for j, c in enumerate(binomial[-1]):
        poly[j] -= Q(degree - 1, degree) * c
        poly[j + 1] += c / degree
    binomial.append(poly)

records = []
checks = 0
odd_checks = 0
equality_checks = 0
test_nodes = list(range(-10, 70)) + [127, 256, 1025, 100003]
for depth in range(1, 9):
    scale = 2**depth
    integrals = [integral(poly, scale) for poly in binomial]
    for j, value in enumerate(integrals):
        assert valuation(value) >= -(j // scale)
        if j % scale == 0:
            assert valuation(value) == -(j // scale)
    for degree in range(2, max_degree + 1, 2):
        poly = [Q(0)] * (degree + 1)
        for j in range(1, degree + 1):
            for k, c in enumerate(binomial[j]):
                poly[k] += (-2) ** (j - 1) * c
        base_integral = integral(poly, scale)
        last = scale * (degree // scale)
        correction = -base_integral / (2**degree * integrals[last])
        assert valuation(correction) >= 0
        for j, c in enumerate(binomial[last]):
            poly[j] += 2**degree * correction * c
        assert integral(poly, scale) == 0
        # In fact the ordinary coefficients are 2-adically integral too.
        assert all(valuation(c) >= 0 for c in poly)
        for x in test_nodes:
            assert valuation(evaluate(poly, x) - (x % 2)) >= degree
        checks += 1
        if degree <= 8 and depth <= 3:
            records.append({
                "degree": degree, "normalization": scale,
                "correction_index": last, "correction_scalar": str(correction),
                "coefficients_ascending": [str(c) for c in poly],
            })
    for degree in range(3, max_degree + 1, 2):
        value = sum((-2)**(j - 1) * integrals[j]
                    for j in range(1, degree + 1))
        if (degree + 1) % scale == 0:
            quotient = (degree + 1) // scale
            assert valuation(value) == degree - quotient
        else:
            last = scale * (degree // scale)
            correction = -value / (2**degree * integrals[last])
            assert valuation(correction) >= 0
        odd_checks += 1
    for degree in range(2, 31, 2):
        poly = [Q(1)]
        for j in range(degree):
            out = [Q(0)]*(len(poly)+1)
            for k,c in enumerate(poly):
                out[k] -= Q(2*j+1,2)*c
                out[k+1] += (scale//2)*c
            poly = out
        shifted = integral(poly,1)/factorial(degree)
        assert valuation(shifted) == -degree-valuation(factorial(degree))
        equality_checks += 1

output = {"status": "passed", "degree_max": max_degree,
          "normalization_depth_max": 8, "filter_count": checks,
          "odd_degree_valuation_checks": odd_checks,
          "equality_case_shifted_integral_checks": equality_checks,
          "small_filters": records}
Path(__file__).with_suffix(".json").write_text(json.dumps(output, indent=2))
print(f"PASS: {checks} exact filters, even degrees 2..40, N=2^a with a=1..8.")
print("All dilation valuations, null integrals, coefficient integrality, and tested parity values passed.")
print(f"PASS: {odd_checks} odd-degree resonance/nonresonance valuation checks.")
print(f"PASS: {equality_checks} equality-case shifted integral checks.")
