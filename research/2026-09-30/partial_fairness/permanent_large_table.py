"""Exact coefficients, an independent 3x3 permanent, and rational Sturm tests."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json
import sympy as sp

x = sp.Symbol('x')

def polynomial(m, K):
    coefficients = [F(0)] * (m + 1)
    coefficients[0] = F(1)
    for degree in range(1, m + 1):
        coefficients[degree] = sum((-F(K, j + 1) * coefficients[degree - j]
                                   for j in range(2, degree + 1, 2)), F(0)) / degree
    ratio = F(1)
    result = []
    for degree, coefficient in enumerate(coefficients):
        if degree:
            ratio *= F(m - degree + 1, K - degree + 1)
        value = ratio * coefficient
        result.append(sp.Rational(value.numerator, value.denominator))
    return sp.Poly.from_list(result, x)

table=[]
for m in [40,50,60,80,100,150,200]:
    excluded=[]
    for K in range(m,2*m):
        poly=polynomial(m,K)
        root_count=int(sum(mult*f.count_roots(-1,1) for f,mult in poly.sqf_list()[1]))
        if root_count==m:
            table.append({'m':m,'first_passing_K':K,'excluded':excluded})
            print(m,K,flush=True)
            Path(__file__).with_suffix('.json').write_text(json.dumps(table,indent=2))
            break
        excluded.append((K,root_count))
