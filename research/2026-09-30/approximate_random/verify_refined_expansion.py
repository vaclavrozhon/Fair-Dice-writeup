#!/usr/bin/env python3
"""Exact checks for refined_random_palindrome_bound.tex; no numerical tolerance.
Run: python3 research/2026-09-30/approximate_random/verify_refined_expansion.py
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import factorial, comb
from random import Random


def compositions(total, parts, minimum=0):
    if parts == 0:
        if total == 0:
            yield ()
        return
    if parts == 1:
        if total >= minimum:
            yield (total,)
        return
    for first in range(minimum, total - minimum*(parts-1) + 1):
        for rest in compositions(total-first, parts-1, minimum):
            yield (first,) + rest


def subsequences(word, target):
    dp = [1] + [0]*len(target)
    for letter in word:
        for pos in range(len(target)-1, -1, -1):
            if letter == target[pos]:
                dp[pos+1] += dp[pos]
    return dp[-1]


def delta(rho, target):
    k = len(target)
    if k == 0:
        return F(0)
    count = subsequences(rho + rho[::-1], target)
    assert count <= 2
    value = F(factorial(k)*count, 2**k)-1
    if k <= 2:
        assert value == 0
    else:
        assert abs(value) <= F(factorial(k),2**(k-1))
    return value


def full_ratio(rhos, target):
    word = tuple(x for rho in rhos for x in rho + rho[::-1])
    return F(factorial(len(target))*subsequences(word, target),
             (2*len(rhos))**len(target))


def occupancy_ratio(rhos, target):
    n, m = len(target), len(rhos)
    result = F(0)
    for lengths in compositions(n,m):
        coefficient = F(factorial(n), m**n)
        pos, product = 0, F(1)
        for rho,k in zip(rhos,lengths):
            coefficient /= factorial(k)
            product *= 1 + delta(rho,target[pos:pos+k])
            pos += k
        result += coefficient*product
    return result


def coefficient_expansion(rhos, target):
    n,m = len(target),len(rhos)
    result, short, long = F(0),F(0),F(0)
    for ell in range(1,n//3+1):
        for selected in combinations(range(m),ell):
            gaps = (selected[0],) + tuple(selected[j+1]-selected[j]-1
                          for j in range(ell-1)) + (m-selected[-1]-1,)
            assert sum(gaps) == m-ell
            for total in range(3*ell,n+1):
                for lengths in compositions(total,ell,3):
                    d=n-total
                    # This is the direct gap-count form of equation (3).
                    for counts in compositions(d,ell+1):
                        coefficient = F(factorial(n),m**n)
                        for k in lengths:
                            coefficient /= factorial(k)
                        for gap,count in zip(gaps,counts):
                            coefficient *= F(gap**count,factorial(count))
                        pos,product=counts[0],F(1)
                        for j,(i,k) in enumerate(zip(selected,lengths)):
                            product *= delta(rhos[i],target[pos:pos+k])
                            pos += k+counts[j+1]
                        assert pos==n
                        term=coefficient*product
                        result += term
                        if 2*total <= n:
                            short += term
                        else:
                            long += term
    assert short+long==result
    return result


def collision(d,gaps):
    M=sum(gaps)
    result=F(0)
    for counts in compositions(d,len(gaps)):
        mass=F(factorial(d),M**d)
        for g,a in zip(gaps,counts):
            mass *= F(g**a,factorial(a))
        result += mass*mass
    return result


def main():
    rng=Random(271828)
    cases=0
    for n in range(3,9):
        m=n+1
        for trial in range(4):
            rhos=[]
            for i in range(m):
                rho=list(range(n));rng.shuffle(rho);rhos.append(tuple(rho))
            target=list(range(n));rng.shuffle(target);target=tuple(target)
            direct=full_ratio(rhos,target)
            by_occupancy=occupancy_ratio(rhos,target)
            by_expansion=1+coefficient_expansion(rhos,target)
            assert direct==by_occupancy==by_expansion,(n,trial,direct,by_occupancy,by_expansion)
            cases+=1
        print(f'n={n}, m={m}: 4 exact DP/occupancy/gap-expansion identities passed',flush=True)
    checks=0
    for ell in range(1,4):
        for d in range(0,7):
            for M in range(d+1,d+5):
                total=sum((collision(d,g) for g in compositions(M,ell+1)),F(0))
                # Square to avoid the irrational square root in the bound.
                assert total*total*(d+1)**ell <= (108*M)**(2*ell)
                checks+=1
    print(f'{cases} exact expansion checks and {checks} collision-sum checks passed.')

if __name__=='__main__':
    main()
