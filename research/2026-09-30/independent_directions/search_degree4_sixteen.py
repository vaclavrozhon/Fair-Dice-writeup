"""Integer-grid search; a found rule is checked with Fraction arithmetic.

Negative MILP output is only a report about that bounded denominator grid.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

for denominator in [15, 45, 75, 105, 135, 165, 195, 225]:
    z = list(range(-denominator, denominator + 1, 2))
    rows = np.array([[float(Q(a, denominator)**j) for a in z]
                     for j in range(5)])
    target = np.array([16/(j + 1) if j % 2 == 0 else 0 for j in range(5)])
    result = milp(np.zeros(len(z)), integrality=np.ones(len(z)),
                  bounds=Bounds(0,16),
                  constraints=LinearConstraint(rows, target, target),
                  options={"time_limit": 45, "mip_rel_gap": 0})
    print("denominator", denominator, "status", result.message, flush=True)
    if result.x is None:
        continue
    counts = np.rint(result.x).astype(int)
    nodes = [Q(a, denominator) for a,c in zip(z,counts) for _ in range(c)]
    exact = len(nodes)==16 and all(sum(x**j for x in nodes)==
              (Q(16,j+1) if j%2==0 else 0) for j in range(5))
    if exact:
        record={"degree":4,"size":16,"denominator":denominator,
                "centered_nodes":[str(x) for x in nodes],
                "interval_nodes":[str((x+1)/2) for x in nodes]}
        print("EXACT CERTIFICATE",record,flush=True)
        Path(__file__).with_suffix(".json").write_text(json.dumps(record,indent=2))
        break
    print("Rounded candidate failed exact check",flush=True)
