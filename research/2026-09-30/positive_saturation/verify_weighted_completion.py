#!/usr/bin/env python3
"""Independent exact test of the weighted-power prefix-completion extension."""
from itertools import permutations
from math import factorial, lcm, prod
from verify_prefix_completion import signature


def complete(prefix, c):
    n = len(c)
    D = lcm(*c)
    B = max(1, *[(prefix.count(i) + c[i] - 1)//c[i] for i in range(n)])
    word = list(prefix)
    for i in range(n):
        word.extend([i] * (B*c[i] - word.count(i)))
    for degree in range(2, n+1):
        old = word
        word = old * (D**degree)
        for sigma in list(permutations(range(n)))[1:]:
            for i in old:
                amount, rem = divmod(D*c[sigma[i]], c[i])
                assert rem == 0
                word.extend([sigma[i]]*amount)
        B *= D**degree + (factorial(n)-1)*D
        assert word[:len(prefix)] == prefix
        assert [word.count(i) for i in range(n)] == [B*x for x in c]
        got = signature(word, n)
        for k in range(1, degree+1):
            for order in permutations(range(n), k):
                assert got[order]*factorial(k) == B**k*prod(c[i] for i in order)
    return B, len(word)


if __name__ == '__main__':
    examples = [([0,1,0], [1,2]), ([1,0,1], [2,3]),
                ([0,1,2,0], [1,1,2]), ([2,0,1,2], [1,2,3]),
                ([0,2,1], [2,2,3]), ([0,1,2,3], [1,1,1,2])]
    for prefix, c in examples:
        B, length = complete(prefix, c)
        print({'prefix': prefix, 'ray': c, 'multiplier': B, 'length': length}, flush=True)
    print('PASS: all 6 unequal-ray prefix completions, all subset-order counts.')
