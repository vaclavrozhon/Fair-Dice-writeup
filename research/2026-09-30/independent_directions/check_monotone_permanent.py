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

columns = [[F(-5, 7), F(1, 70), F(7, 10)],
           [F(-23, 33), F(-1, 48), F(379, 528)],
           [F(-326, 459), F(1, 153), F(19, 27)]]
direct = 0
for assignment in permutations(range(3)):
    product = 1
    for j, row in enumerate(assignment):
        y = columns[j][row]
        product *= x - sp.Rational(y.numerator, y.denominator)
    direct += product / 6
assert sp.Poly(sp.expand(direct), x) == polynomial(3, 3)

table = []
for m in range(2, 31):
    excluded = []
    for K in range(m, m * m + 1):
        poly = polynomial(m, K)
        root_count = int(sum(multiplicity * factor.count_roots(-1, 1)
                            for factor, multiplicity in poly.sqf_list()[1]))
        if root_count == m:
            table.append({'m': m, 'first_passing_K': K, 'excluded': excluded})
            print(m, K, flush=True)
            break
        excluded.append({'K': K, 'real_interval_roots_with_multiplicity': root_count})
    else:
        raise AssertionError(('no passing K found', m))

path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps({'direct_permanent_check': 'PASS', 'table': table}, indent=2) + '\n')
print('PASS: exact permanent identity and all Sturm exclusions through m=30.')
