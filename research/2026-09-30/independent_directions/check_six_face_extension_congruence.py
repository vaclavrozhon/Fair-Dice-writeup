"""Exact, standard-library verification of the eight mod-four certificates."""
from pathlib import Path
import json

directory = Path(__file__).resolve().parent
seeds = (directory.parent / 'partial_fairness/four_dice_six_canonical_words.txt').read_text().split()
certificates = []
assert len(seeds) == 8
for index, word in enumerate(seeds):
    t = 2 if index < 4 else 3
    values = []
    after_ones = []
    for gap in range(len(word) + 1):
        prefix = word[:gap]
        pairs = {a: sum(prefix[i] == str(a) and prefix[j] == '1'
                        for i in range(gap) for j in range(i + 1, gap))
                 for a in (0, 2, 3)}
        value = prefix.count('1') - sum(pairs.values()) - 2 * pairs[t]
        assert value % 4 == 0
        values.append(value)
        if gap and word[gap - 1] == '1':
            after_ones.append(value)
    assert after_ones == [0, -8, -20, -36, -56, -84]
    certificates.append({'word': word, 't': t, 'prefix_values': values,
                         'values_after_letter_1': after_ones,
                         'target_coefficient': -27})
(directory / 'six_face_extension_congruence.json').write_text(json.dumps(certificates, indent=2) + '\n')
print('PASS: all 200 prefix congruences; all eight seeds force 4 | M.')
