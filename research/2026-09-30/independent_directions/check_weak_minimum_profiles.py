"""Exact necessary profiles at q=n-1=3h, without any permutation solver."""
from fractions import Fraction as F
from math import prod, isqrt
from pathlib import Path
import json

def compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, length - 1):
            yield (first,) + tail

output = []
for h in range(1, 6):
    q = 3 * h
    profiles = []
    visited = 0
    for counts in compositions(q, h):
        visited += 1
        E = sum(e * c for e, c in enumerate(counts, 1))
        S = sum((F(c, e) for e, c in enumerate(counts, 1)), F(0))
        if E + h - F(h * (q - 1) ** 2) / (1 + h * S) != q:
            continue
        determinant = prod(e ** c for e, c in enumerate(counts, 1)) * (1 + h * S)
        assert determinant.denominator == 1
        determinant = determinant.numerator
        square = isqrt(determinant) ** 2 == determinant
        profiles.append({'counts': counts, 'determinant': determinant,
                         'square': square,
                         'square_root': isqrt(determinant) if square else None})
    output.append({'h': h, 'q': q, 'visited_profiles': visited, 'profiles': profiles})
    print(h, profiles)

assert [tuple(p['counts']) for p in output[1]['profiles']] == [(3, 3)]
assert output[2]['profiles'] == []
assert [tuple(p['counts']) for p in output[3]['profiles'] if p['square']] == [(9, 0, 1, 2)]
assert [tuple(p['counts']) for p in output[4]['profiles'] if p['square']] == [(1, 5, 7, 2, 0)]
Path(__file__).with_suffix('.json').write_text(json.dumps(output, indent=2) + '\n')
print('PASS: exact complete profile enumeration for h=1,...,5.')
