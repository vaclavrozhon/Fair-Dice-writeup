"""Exploratory exhaustive order errors for randomly relabelled palindrome blocks.

This is a numerical experiment, not an existence proof for growing n.
Each row checks ALL n! orders, using double precision subsequence counts.
"""
import argparse
import itertools
import json
import math
import random
import numpy as np


def order_errors(n, blocks, palindromic=True):
    permutations = np.array(list(itertools.permutations(range(n))), dtype=np.int16)
    positions = np.argsort(permutations, axis=1) + 1
    rows = np.arange(len(permutations))
    counts = np.zeros((len(permutations), n + 1))
    counts[:, 0] = 1
    for block in blocks:
        word = list(block) + list(reversed(block)) if palindromic else list(block)
        for letter in word:
            j = positions[:, letter]
            counts[rows, j] += counts[rows, j - 1]
    faces = len(blocks) * (2 if palindromic else 1)
    ratios = counts[:, n] * math.factorial(n) / faces ** n
    return {
        "n": n, "blocks": len(blocks), "faces": faces,
        "minimum": float(ratios.min()), "maximum": float(ratios.max()),
        "max_error": float(np.abs(ratios - 1).max()),
        "rms_error": float(np.sqrt(np.mean((ratios - 1) ** 2))),
        "total_variation": float(np.mean(np.abs(ratios - 1)) / 2),
        "normalization_error": float(abs(ratios.mean() - 1)),
        "worst_order": permutations[np.argmax(np.abs(ratios - 1))].tolist(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--seed", type=int, default=30092026)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    for n in range(3, args.max_n + 1):
        for multiple in (1, 2, 4, 8):
            m = multiple * n
            fixed = order_errors(n, [list(range(n))] * m)
            fixed.update(kind="fixed_palindrome", seed=args.seed)
            print(json.dumps(fixed), flush=True)
            for trial in range(args.trials):
                blocks = [rng.sample(range(n), n) for _ in range(m)]
                row = order_errors(n, blocks)
                row.update(kind="random_palindrome", trial=trial, seed=args.seed)
                print(json.dumps(row), flush=True)
                row = order_errors(n, blocks, palindromic=False)
                row.update(kind="random_permutation", trial=trial, seed=args.seed)
                print(json.dumps(row), flush=True)


if __name__ == "__main__":
    main()
