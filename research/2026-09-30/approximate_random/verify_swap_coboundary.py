#!/usr/bin/env python3
"""Exact verification of the six-window averaging/coboundary identities."""
from itertools import combinations, permutations, product
from fractions import Fraction as F
from random import Random

rng = Random(20260930)
for n in [6, 7, 9]:
    delta = {}
    for triple in combinations(range(n), 3):
        values = [rng.randrange(-3, 4), rng.randrange(-3, 4)]
        values.append(-sum(values))
        for center, value in zip(triple, values):
            x, y = [a for a in triple if a != center]
            delta[x, center, y] = delta[y, center, x] = F(value, 6)
    def f(a,b,c): return delta.get((a,b,c), F(0))
    U = {(b,c):sum((f(a,b,c) for a in range(n)),F(0))/n
         for b,c in product(range(n), repeat=2)}
    r = {b:sum((U[b,c] for c in range(n)),F(0))/n for b in range(n)}
    for c in range(n):
        assert sum((U[b,c] for b in range(n)),F(0))/n == -r[c]/2
    def K(b,c,d): return f(b,c,d)-f(b,d,c)+U[b,c]-U[b,d]
    def V(c,d): return U[c,d]-U[d,c]-r[c]/2+r[d]/2
    def e(b,c,d): return K(b,c,d)-V(c,d)
    def A(b,c): return (U[b,c]-U[c,b])/2+(r[c]-r[b])/4
    def S(b,c): return U[b,c]+U[c,b]-(r[b]+r[c])/2
    def D(a,b,c,d,z,f0):
        return (f(a,b,c)+f(b,c,d)+f(c,d,z)+f(d,z,f0)
                -f(a,b,d)-f(b,d,c)-f(d,c,z)-f(c,z,f0))
    for b,c,d in product(range(n),repeat=3):
        assert sum((K(a,c,d) for a in range(n)),F(0))/n == V(c,d)
        assert 3*(f(b,c,d)-A(c,b)-A(c,d)) == (
            -S(c,b)/2-S(c,d)/2+S(b,d)+e(d,c,b)+e(b,c,d))
    for b,c in product(range(n),repeat=2):
        assert sum((e(b,c,d) for d in range(n)),F(0))/n == 2*S(b,c)
    for _ in range(50):
        b,c,d,z = rng.sample(range(n),4)
        average = sum((D(a,b,c,d,z,f0) for a,f0 in product(range(n), repeat=2)), F(0))/n**2
        assert average == K(b,c,d)-K(z,c,d)
    print(f'n={n}: exact identities passed for all triples, all pairs, 50 contexts.')
print('PASS: six-window averaging and coboundary algebra.')
