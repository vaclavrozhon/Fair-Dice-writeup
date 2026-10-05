#!/usr/bin/env python3
"""Exact integer checks for the arithmetic relaxation (not dice existence)."""
from itertools import combinations
from math import factorial, prod
import argparse
import json


def primes(n):
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, int(p ** .5) + 1))]


def check_subsets(c):
    return all(prod(c[i] for i in s) % factorial(k) == 0
               for k in range(1, len(c) + 1)
               for s in combinations(range(len(c)), k))


def greedy(n):
    c = [1] * n
    for p in primes(n):
        c.sort()
        c[:n-p+1] = [x*p for x in c[:n-p+1]]
    return tuple(sorted(c))


def exact_optimum(n):
    # A sum minimizer has valuation one at exactly n-p+1 coordinates
    # for every p<=n: removing any unnecessary prime only lowers the sum.
    states = {(1,) * n}
    sizes = []
    for p in primes(n):
        next_states = set()
        for c in states:
            # Choose the omitted p-1 coordinates, or the included ones,
            # whichever has fewer combinations (the counts are equal).
            for indices in combinations(range(n), n-p+1):
                selected = set(indices)
                next_states.add(tuple(sorted(x*p if i in selected else x
                                             for i, x in enumerate(c))))
        states = next_states
        sizes.append([p, len(states)])
    winner = min(states, key=lambda c: (sum(c), c))
    return winner, sizes


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=10)
    args = parser.parse_args()
    rows = []
    for n in range(1, args.max_n + 1):
        p_n = prod(p ** (n-p+1) for p in primes(n))
        g = greedy(n)
        winner, sizes = exact_optimum(n)
        assert prod(g) == prod(winner) == p_n
        assert g[-1] <= n*g[0]
        assert check_subsets(g) and check_subsets(winner)
        row = dict(n=n, product=p_n, greedy=g, greedy_sum=sum(g),
                   optimum=winner, optimum_sum=sum(winner), states=sizes,
                   equal_optimum_sum=n*prod(primes(n)))
        rows.append(row)
        print(json.dumps(row), flush=True)
    return rows


if __name__ == '__main__':
    main()
