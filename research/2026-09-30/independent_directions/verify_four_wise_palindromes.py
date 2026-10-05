"""Literal index enumeration, independent of the constructor's dynamic program."""
from collections import Counter
from itertools import combinations
from math import factorial
from pathlib import Path
import json

directory = Path(__file__).resolve().parent
reports = []
for n, h in ((5, 6), (6, 6), (5, 9)):
    source = directory.parent / 'partial_fairness' / f'triple_winner_half_n{n}_M{h}_seed0.json'
    data = json.loads(source.read_text())
    word, half = data['word'], data['half_word']
    assert word == half[::-1] + half
    assert Counter(half) == dict.fromkeys(range(n), h)
    checks = []
    for k in range(1, 5):
        counts = Counter(tuple(word[i] for i in indices)
                         for indices in combinations(range(len(word)), k)
                         if len({word[i] for i in indices}) == k)
        assert len(counts) == factorial(n) // factorial(n - k)
        assert set(counts.values()) == {(2*h) ** k // factorial(k)}
        checks.append({'order_length': k, 'distinct_orders': len(counts),
                       'count_per_order': (2*h) ** k // factorial(k)})
    triples = Counter(tuple(half[i] for i in indices)
                      for indices in combinations(range(len(half)), 3)
                      if len({half[i] for i in indices}) == 3)
    last = []
    for labels in combinations(range(n), 3):
        for label in labels:
            count = sum(value for order, value in triples.items()
                        if set(order) == set(labels) and order[-1] == label)
            assert count == h**3 // 3
            last.append({'triple': labels, 'last_label': label, 'count': count})
    reports.append({'n': n, 'half_faces': h, 'status': 'PASS', 'half_word': ''.join(map(str, half)),
                    'full_order_checks': checks, 'half_last_checks': last})
    print(n, h, reports[-1]['half_word'], checks, flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(reports, indent=2) + '\n')
print('PASS: all exact palindrome constructions through all quadruple orders.')
