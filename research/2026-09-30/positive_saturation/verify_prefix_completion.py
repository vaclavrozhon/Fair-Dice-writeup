#!/usr/bin/env python3
"""Exact checks of permutation symmetrization and literal fair completion.

The construction uses actual positive words; a separate integer subsequence
DP verifies every distinct-letter coefficient after each symmetrization.
"""
from itertools import permutations
from math import factorial
from random import Random


def signature(word, n):
    out = {(): 1}
    for letter in word:
        for prefix, count in list(out.items()):
            if letter not in prefix:
                key = prefix + (letter,)
                out[key] = out.get(key, 0) + count
    return out


def complete(word, n):
    original = tuple(word)
    counts = [word.count(i) for i in range(n)]
    count = max(1, *counts)
    word = list(word)
    for i in range(n):
        word.extend([i] * (count - counts[i]))
    for degree in range(2, n + 1):
        word = [p[i] for p in permutations(range(n)) for i in word]
        count *= factorial(n)
        assert tuple(word[:len(original)]) == original
        got = signature(word, n)
        for k in range(1, degree + 1):
            target, rem = divmod(count**k, factorial(k))
            assert rem == 0
            for order in permutations(range(n), k):
                assert got.get(order, 0) == target, (n, degree, order)
    got = signature(word, n)
    for k in range(1, n + 1):
        for order in permutations(range(n), k):
            assert got.get(order, 0) * factorial(k) == count**k
    return count, len(word)


def main():
    rng = Random(20260930)
    tested = 0
    for n in range(1, 5):
        words = [[], list(range(n)), list(reversed(range(n)))]
        words += [[rng.randrange(n) for _ in range(2*n)] for _ in range(2)]
        for word in words:
            count, length = complete(word, n)
            print({'n': n, 'prefix': word, 'count': count, 'length': length}, flush=True)
            tested += 1
    print(f'PASS: {tested} exact positive prefix completions, all subset orders.')

if __name__ == '__main__':
    main()
