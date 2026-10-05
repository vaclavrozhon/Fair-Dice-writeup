#!/usr/bin/env python3
"""Exact checks for the identities in two_adic_lower_bound.tex.

These finite checks complement, and do not replace, the proof.
No third-party dependencies are required.
"""
from fractions import Fraction as Q
from math import comb
import argparse


def v2(x):
    x = Q(x)
    if not x:
        return float('inf')
    n, d = abs(x.numerator), x.denominator
    return (n & -n).bit_length() - (d & -d).bit_length()


def mul(a, b, degree):
    c = [Q(0)] * (degree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:degree + 1 - i]):
            c[i+j] += x*y
    return c


def inverse(a, degree):
    assert a[0] == 1
    b = [Q(1)]
    for k in range(1, degree + 1):
        b.append(-sum(a[j] * b[k-j] for j in range(1, k+1)))
    return b


def rational_binom(y, j):
    z = Q(1)
    for k in range(j):
        z *= (y-k)/(k+1)
    return z


def direct_integral_h(r, N):
    # Coefficients of binomial(N*x,j), and its H_r sum.
    b = [Q(1)]
    out = Q(0)
    for j in range(1, r+1):
        c = [Q(0)] * (len(b)+1)
        for k, v in enumerate(b):
            c[k] -= Q(j-1, j) * v
            c[k+1] += Q(N, j) * v
        b = c
        out += (-2)**(j-1) * sum(v/Q(k+1) for k, v in enumerate(b))
    return out


def main(degree, max_scale):
    D = [Q(2**j, j+1) for j in range(degree+1)]
    G = inverse(D, degree)
    assert all(v2(g) == 0 for g in G), 'Gregory coefficient valuation'
    E, acc = [], Q(0)
    for k, d in enumerate(D):
        acc += d
        E.append(acc)
        assert v2(acc) >= (k+1)//2
    F = inverse(E, degree)
    for a in range(1, max_scale+1):
        assert all(v2(F[k]) >= (k+1)//2 for k in range(1, degree+1))
        h = Q(0)
        valuations = []
        for r in range(1, degree+1):
            h -= F[r]/2
            assert v2(h) >= r//2, (a, r, h)
            if r <= min(20, degree):
                assert h == direct_integral_h(r, 2**a), (a, r)
            valuations.append(v2(h))
        print(f'a={a}: checked r=1..{degree}; first 16 integral valuations={valuations[:16]}')
        M = 2**a
        B = [Q(1)] + [Q((-2)**k*comb(M,k),2) if k <= M else Q(0)
                        for k in range(1,degree+1)]
        F = mul(F, B, degree)
    for r in range(1, min(degree, 24)+1):
        for denominator in (1, 3, 5, 17):
            for numerator in range(-12, 13):
                y = Q(numerator, denominator)
                h = sum((-2)**(j-1)*rational_binom(y,j) for j in range(1,r+1))
                assert v2(h - (numerator % 2)) >= r
    print('All exact coefficient, direct integral, and rational parity checks passed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--degree', type=int, default=128)
    parser.add_argument('--max-scale', type=int, default=6)
    args = parser.parse_args()
    main(args.degree, args.max_scale)
