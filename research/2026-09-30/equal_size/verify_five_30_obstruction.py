"""Fraction-free independent verification of the 15-palindrome obstruction.

No optimization package is needed.  This certifies only the specified
palindrome-block construction, not nonexistence of arbitrary 30-face dice.
"""
from itertools import combinations, permutations
import json
from pathlib import Path


def subsequences(word, pattern):
    d = [1] + [0] * len(pattern)
    for x in word:
        for j in range(len(pattern)-1, -1, -1):
            if x == pattern[j]:
                d[j+1] += d[j]
    return d[-1]


def main():
    cert = json.loads(Path(__file__).with_name('five_30_farkas.json').read_text())
    dual = cert['dual_coefficients']
    perms = list(permutations(range(5)))
    triples = list(combinations(range(5), 3))
    assert len(dual) == 165
    rows = {k: list(permutations(range(5), k)) for k in (3, 4, 5)}
    defects = []
    for rho in perms:
        word = rho + rho[::-1]
        defects.append({p: (15 if k == 5 else 3)*subsequences(word, p)
                       - {3: 4, 4: 2, 5: 4}[k]
                        for k in (3, 4, 5) for p in rows[k]})

    def column(i, r):
        j = 14-i
        d = defects[r]
        result = []
        for p in perms:
            result.append(d[p] + 10*i*d[p[1:]] + 10*j*d[p[:4]]
                          + 10*i*i*d[p[2:]] + 20*i*j*d[p[1:4]]
                          + 10*j*j*d[p[:3]])
        result += [int(i == k) for k in range(15)]
        for t in triples:
            winner = next(x for x in perms[r] if x in t)
            result += [int(x == winner) for x in t]
        return result

    first = column(0, 0)
    rhs = [x-y for x, y in zip([0]*120+[1]*15+[5]*30, first)]
    rhs_dot = sum(x*y for x, y in zip(dual, rhs))
    column_dots = [sum(x*y for x, y in zip(dual, column(i, r)))
                   for i in range(1, 15) for r in range(120)]
    assert min(column_dots) >= 0
    assert rhs_dot < 0
    assert rhs_dot == cert['rhs_dot']
    assert min(column_dots) == cert['column_dot_min']
    print(json.dumps({'verified': True, 'remaining_columns': len(column_dots),
                      'minimum_dual_column': min(column_dots),
                      'dual_rhs': rhs_dot, 'scope': cert['scope']}, indent=2))


if __name__ == '__main__':
    main()
