"""Exact linear constraints for 15 independently relabelled palindrome blocks.

The MILP search uses floating point internally; any reported solution is
independently verified by integer subsequence counting before acceptance.
"""
import argparse
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csc_matrix, vstack


def count(word, pattern):
    d = [1] + [0] * len(pattern)
    for x in word:
        for j in range(len(pattern) - 1, -1, -1):
            if pattern[j] == x:
                d[j + 1] += d[j]
    return d[-1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--blocks', type=int, default=15)
    ap.add_argument('--seconds', type=float, default=300)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--relax', action='store_true')
    ap.add_argument('--free-first', action='store_true')
    ap.add_argument('--matrix-output')
    ap.add_argument('--zero-objective', action='store_true')
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    m = args.blocks
    perms = list(itertools.permutations(range(5)))
    blocks = [p + p[::-1] for p in perms]
    pats = {k: list(itertools.permutations(range(5), k)) for k in (3, 4, 5)}
    defects = [{p: F(count(w, p)) - F(2 ** k, math.factorial(k))
                for k in (3, 4, 5) for p in pats[k]} for w in blocks]
    # Products of two block errors have degree >=6, so the degree5 error
    # is exactly the sum of these individually transported errors.
    A = np.zeros((120, m * 120), dtype=np.int64)
    for i in range(m):
        for r, delta in enumerate(defects):
            for row, p in enumerate(perms):
                value = F(0)
                for a in range(3):
                    for b in range(3 - a):
                        k = 5 - a - b
                        value += (F((2*i)**a, math.factorial(a)) *
                                  delta[p[a:a+k]] *
                                  F((2*(m-1-i))**b, math.factorial(b)))
                value *= 15
                assert value.denominator == 1
                A[row, i*120+r] = value.numerator
    slot = np.zeros((m, m * 120), dtype=np.int64)
    for i in range(m):
        slot[i, i*120:(i+1)*120] = 1
    # Expose the simpler triple constraints to help integer presolve.
    triples = list(itertools.combinations(range(5), 3))
    mins = np.zeros((len(triples) * 3, m * 120), dtype=np.int64)
    for ti, t in enumerate(triples):
        for r, p in enumerate(perms):
            winner = next(x for x in p if x in t)
            row = 3*ti+t.index(winner)
            mins[row, r::120] = 1
    matrix = vstack([csc_matrix(A), csc_matrix(slot), csc_matrix(mins)], format='csc')
    rhs = np.array([0]*120 + [1]*m + [m/3]*len(mins))
    if args.matrix_output:
        np.savez_compressed(args.matrix_output, matrix=matrix.toarray(), rhs=rhs)
    lower = np.zeros(m*120)
    upper = np.ones(m*120)
    if not args.free_first:
        lower[0] = 1
        upper[1:120] = 0  # Global relabelling fixes the first permutation.
    rng = np.random.default_rng(args.seed)
    objective = np.zeros(m*120) if args.zero_objective else rng.uniform(-1, 1, m*120)
    result = milp(objective, integrality=np.zeros(m*120) if args.relax else np.ones(m*120),
                  bounds=Bounds(lower, upper),
                  constraints=LinearConstraint(matrix, rhs, rhs),
                  options={'time_limit': args.seconds, 'disp': True})
    out = {'blocks': m, 'seed': args.seed, 'status': int(result.status),
           'message': result.message, 'solution': None}
    if result.x is not None and not args.relax:
        selected = np.rint(result.x).astype(np.int64)
        assert np.array_equal(matrix @ selected, rhs)
        indices = [int(np.flatnonzero(selected[i*120:(i+1)*120])[0]) for i in range(m)]
        word = tuple(x for r in indices for x in blocks[r])
        values = [count(word, p) for p in perms]
        target = F((2*m)**5, math.factorial(5))
        assert all(v == target for v in values)
        out['solution'] = {'indices': indices, 'word': ''.join(map(str, word)),
                           'full_order_count': str(target)}
    Path(args.output).write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
