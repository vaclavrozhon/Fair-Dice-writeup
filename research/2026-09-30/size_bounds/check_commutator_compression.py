#!/usr/bin/env python3
"""Exact reduced-algebra checks of the base-digit signed-word compression."""
import json
from math import prod
from check_signed_signatures import add, mul, inverse, bracket_basis


def powered_nested_signature(powers):
    k = len(powers)
    value = {(): 1, (k-1,): powers[-1]}
    length = abs(powers[-1])
    for i in range(k-2, -1, -1):
        left = {(): 1, (i,): powers[i]}
        value = mul(mul(mul(left, value), inverse(left, k)), inverse(value, k))
        length = 2*(abs(powers[i])+length)
    expected = add({(): 1}, bracket_basis(tuple(range(k-1)), k-1), prod(powers))
    assert value == expected
    return value, length


def compress(coefficient, degree, base):
    assert abs(coefficient) < base**degree
    remaining = abs(coefficient)
    sign = -1 if coefficient < 0 else 1
    result = {(): 1}
    length = 0
    digits = 0
    for j in range(degree):
        digit = remaining % base
        remaining //= base
        if digit:
            powers = [sign*digit] + [base]*j + [1]*(degree-j-1)
            factor, cost = powered_nested_signature(powers)
            result = mul(result, factor)
            length += cost
            digits += 1
    assert remaining == 0
    expected = add({(): 1}, bracket_basis(tuple(range(degree-1)), degree-1), coefficient)
    assert result == expected
    assert length <= degree**2 * 2**degree * base
    return dict(degree=degree, base=base, coefficient=coefficient,
                nonzero_digits=digits, signed_length=length)


if __name__ == '__main__':
    cases = []
    for k in range(2, 8):
        for base in [2, 3, 10, 101]:
            for coefficient in [0, 1, -1, base**k-1, -(base**k-1), base**(k-1)+1]:
                cases.append(compress(coefficient, k, base))
    print(json.dumps(dict(exact_cases=len(cases), cases=cases), indent=2))
