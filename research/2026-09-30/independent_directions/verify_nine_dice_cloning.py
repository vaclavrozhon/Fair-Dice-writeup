"""Independent literal triple enumeration and reconstruction of the cloning certificate."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

directory = Path(__file__).resolve().parent
data = json.loads((directory.parent / 'partial_fairness/nine_dice_twelve_three_wise.json').read_text())
word = data['word']
assert Counter(word) == dict.fromkeys(range(9), 12)
counts = Counter(tuple(word[i] for i in indices)
                 for indices in combinations(range(len(word)), 3)
                 if len({word[i] for i in indices}) == 3)
assert len(counts) == 504 and set(counts.values()) == {288}

seed = '012332103102201321033012'
seed_counts = Counter(tuple(seed[i] for i in indices)
                      for indices in combinations(range(len(seed)), 3)
                      if len({seed[i] for i in indices}) == 3)
assert len(seed_counts) == 24 and set(seed_counts.values()) == {36}
cursor = 0
permutations = []
mapping = {'0': 6, '2': 7, '3': 8}
for letter in seed:
    if letter == '1':
        block = word[cursor:cursor + 12]
        assert block[6:] == block[:6][::-1]
        assert set(block[:6]) == set(range(6))
        permutations.append(block[:6])
        cursor += 12
    else:
        assert word[cursor:cursor + 2] == [mapping[letter]] * 2
        cursor += 2
assert cursor == len(word)

minimum_checks = []
for triple in combinations(range(6), 3):
    minima = Counter(min(triple, key=permutation.index) for permutation in permutations)
    assert minima == dict.fromkeys(triple, 2)
    minimum_checks.append({'triple': triple, 'counts': dict(minima)})
prefix_checks = []
for label in '023':
    h = [seed[:j].count('1') for j, letter in enumerate(seed) if letter == label]
    assert sum(h) == 18 and sum(value * value for value in h) == 72
    prefix_checks.append({'label': label, 'prefix_counts': h, 'sum': 18, 'square_sum': 72})

report = {'status': 'PASS', 'seed_triple_orders': 24, 'seed_count_per_order': 36,
          'final_triple_orders': 504, 'final_count_per_order': 288,
          'permutations': permutations, 'minimum_checks': minimum_checks,
          'prefix_checks': prefix_checks}
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
print('PASS: seed, all 20 weak-minimum triples, all prefix moments, exact cloning, all 504 final orders.')
