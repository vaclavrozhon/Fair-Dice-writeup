#!/usr/bin/env python3
"""Independent exact checks: Jacobi barrier and rational design p-adic proof.

The p-adic check constructs binomial polynomials directly over Fraction;
it does not use the generating functions in the proposed proof.
"""
from fractions import Fraction as Q
from math import prod
import json


def v2(q):
    q = Q(q)
    if not q:
        return 10**9
    n, d = abs(q.numerator), q.denominator
    return (n & -n).bit_length() - (d & -d).bit_length()


def integrated_binomials(scale, degree):
    poly = [Q(1)]
    answer = [Q(1)]
    for k in range(1, degree + 1):
        out = [Q(0)] * (len(poly) + 1)
        for j, c in enumerate(poly):
            out[j] -= c * Q(k-1, k)
            out[j+1] += c * Q(scale, k)
        poly = out
        answer.append(sum((c / (j+1) for j, c in enumerate(poly)), Q(0)))
    return answer


def h_value(y, r):
    choose = Q(1)
    total = Q(0)
    for j in range(1, r+1):
        choose *= (y-j+1) / j
        total += (-2)**(j-1) * choose
    return total


def check_two_adic():
    rmax = 70
    base = integrated_binomials(1, rmax)
    assert all(v2(base[r]) == -r for r in range(rmax+1))
    rows = []
    for a in range(1, 7):
        moments = integrated_binomials(2**a, rmax)
        h_integral = Q(0)
        vals = []
        for r in range(1, rmax+1):
            assert v2((-2)**r * moments[r]) >= (r+1)//2
            h_integral += (-2)**(r-1) * moments[r]
            assert v2(h_integral) >= r//2
            vals.append(None if h_integral == 0 else v2(h_integral))
        rows.append(dict(a=a, degree=rmax, integral_valuations_first_20=vals[:20]))
    parity_cases = 0
    for numerator in range(-12, 13):
        for denominator in [1, 3, 5, 7, 9, 11, 15]:
            y = Q(numerator, denominator)
            odd = numerator % 2
            for r in range(1, 21):
                assert v2(h_value(y, r)-odd) >= r
                parity_cases += 1
    return dict(gregory_degree=rmax, scaled_tests=rows, parity_cases=parity_cases)


def check_jacobi():
    import sympy as s
    x = s.symbols('x')
    rows = []
    for m in range(0, 18):
        q = s.Poly(s.jacobi(m, 0, 3, 2*x-1), x)
        square = q*q
        a = sum(c/s.Integer(j[0]+2) for j, c in square.terms())
        b = sum(c/s.Integer(j[0]+3) for j, c in square.terms())
        assert a == s.Rational(m*m+4*m+6, 12)
        assert b == s.Rational(1, 3)
        # Check the connection identities separately, as polynomial identities.
        d = (m+1)*(m+2)*(m+3)
        one = sum((-1)**(m-k)*(2*k+3)*(k+1)*(k+2)*
                  s.jacobi(k, 0, 2, 2*x-1) for k in range(m+1))/d
        two = sum((-1)**(m-j)*2*(j+1)**2*((m+2)**2-(j+1)**2)*
                  s.jacobi(j, 0, 1, 2*x-1) for j in range(m+1))/d
        assert s.Poly(one-q.as_expr(), x).is_zero
        assert s.Poly(two-q.as_expr(), x).is_zero
        rows.append(dict(m=m, A=str(a), B=str(b), grid_lower_bound=str(a/b)))
    return rows


if __name__ == '__main__':
    print(json.dumps(dict(two_adic=check_two_adic(), jacobi=check_jacobi()), indent=2))
