"""Independent stdlib-only audit; enumerate position subsets instead of DP."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import factorial
from pathlib import Path
import json

source = Path(__file__).parents[1] / "approximate_random" / "linear_extraction_counterexample.json"
certificate = json.loads(source.read_text())
n, blocks = certificate["labels"], certificate["blocks"]
orders = list(permutations(range(n)))
full, triple = [Q(0)]*len(orders), [Q(0)]*len(orders)
slots = [0]*blocks
for column, weight in certificate["indices_weights"]:
    slot, index = divmod(column, factorial(n))
    slots[slot] += weight
    word = orders[index] + orders[index][::-1]
    counts = {}
    for degree in (3,4,5):
        counts[degree] = Counter(tuple(word[j] for j in positions)
                                for positions in combinations(range(2*n), degree))
    for row, order in enumerate(orders):
        for left in range(3):
            for right in range(3-left):
                degree = n-left-right
                middle = order[left:left+degree]
                defect = counts[degree][middle] - Q(2**degree, factorial(degree))
                contribution = (15 * weight * Q((2*slot)**left, factorial(left))
                                * defect * Q((2*(blocks-1-slot))**right, factorial(right)))
                full[row] += contribution
                if degree == 3:
                    triple[row] += contribution
assert slots == [0]*blocks
assert all(x == 0 for x in full)
assert triple == list(map(Q, certificate["triple_output"]))
assert triple[0] == -120 and any(triple)
output = {"status": "passed", "support": len(certificate["indices_weights"]),
          "slot_sums": slots, "all_full_outputs_zero": True,
          "nonzero_triple_outputs": sum(bool(x) for x in triple),
          "first_triple_output": str(triple[0]),
          "method": "position-subset enumeration and Fraction arithmetic"}
Path(__file__).with_suffix(".json").write_text(json.dumps(output, indent=2))
print(json.dumps(output))
