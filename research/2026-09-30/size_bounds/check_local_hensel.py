#!/usr/bin/env python3
"""Exact modular checks for the exponential rational-design local construction.

No p-adic floating point arithmetic. Faulhaber sums are computed as exact
integers, and the contraction uses rational matrices reduced modulo p^T.
The proof does not depend on these finite checks.
"""
from fractions import Fraction
import json
import math
import sympy as sp


def vp(n, p):
    if not n:
        return 10**9
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def power_sum(M, degree):
    # Sum_{x=0}^{M-1} x^degree, by the Bernoulli polynomial identity.
    value = (sp.bernoulli(degree + 1, M) - sp.bernoulli(degree + 1)) / (degree + 1)
    assert value.q == 1
    return int(value)


def check(r, p, extra_digits=12):
    b = vp(math.factorial(r - 1), p)
    power = p
    while power <= r:
        b += 1
        power *= p
    a = 2*b + 2
    M = p**a
    T = b + 1 + extra_digits
    modulus = p**T
    A = sp.Matrix([[j*i**(j-1) for i in range(r)] for j in range(1,r+1)])
    inverse = [[Fraction(x) for x in row] for row in A.inv().tolist()]
    inverse_valuation = min(vp(x.numerator,p)-vp(x.denominator,p)
                            for row in inverse for x in row if x)
    assert inverse_valuation >= -b
    residual = [power_sum(M,j) for j in range(1,r+1)]
    assert min(vp(x,p) for x in residual) >= a-1
    h = [0]*r
    for iteration in range(extra_digits+2):
        nonlinear = [sum((i+h[i])**j-i**j-j*i**(j-1)*h[i]
                         for i in range(r)) for j in range(1,r+1)]
        new_h = []
        for row in inverse:
            value = -sum(coef*(residual[j]+nonlinear[j])
                         for j,coef in enumerate(row))
            assert value.denominator % p
            new_h.append(value.numerator * pow(value.denominator,-1,modulus) % modulus)
        assert all(x % p**(b+1) == 0 for x in new_h)
        h = new_h
    actual_residual = [residual[j-1] + sum((i+h[i])**j-i**j for i in range(r))
                       for j in range(1,r+1)]
    assert all(x % modulus == 0 for x in actual_residual)
    points = [i+h[i] for i in range(r)]
    assert all(vp(points[i]-points[j],p) == vp(i-j,p)
               for i in range(r) for j in range(i))
    return dict(r=r,p=p,b=b,a=a,M=M,precision=T,
                inverse_valuation=inverse_valuation,
                residual_valuation=min(vp(x,p) for x in actual_residual),
                pivots=points)


if __name__ == '__main__':
    for r in range(2,11):
        for p in [2,3,5,7,11]:
            print(json.dumps(check(r,p)), flush=True)
