#!/usr/bin/env python3
"""Exact local covariance and swap-additivity checks for the lower-bound note."""
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial, comb
from random import Random


def valley_delta(values):
    return F(1,2)-F(3,2)*(values[1]<values[0] and values[1]<values[2])


def difference_vector(values):
    switched=list(values)
    switched[2],switched[3]=switched[3],switched[2]
    return tuple(valley_delta(switched[a:a+3])-valley_delta(values[a:a+3])
                 for a in range(4))


def projection(priorities,target):
    m,n=len(priorities),len(target);d=n-3
    h=F(comb(n,3),m**3)*F(m-1,m)**d
    result=F(0)
    for i,row in enumerate(priorities):
        p=F(i,m-1)
        for a in range(d+1):
            w=comb(d,a)*p**a*(1-p)**(d-a)
            result+=w*valley_delta([row[target[a+j]] for j in range(3)])
    return h*result


def main():
    for lag,expected in enumerate([F(1,2),-F(1,4),F(1,20),F(0)]):
        length=lag+3
        covariance=sum((valley_delta(v[:3])*valley_delta(v[lag:lag+3])
                       for v in permutations(range(length))),F(0))/factorial(length)
        assert covariance==expected,(lag,covariance)
    event=(6,1,3,2,4,5)
    reverse=(6,1,2,3,4,5)
    assert difference_vector(event)==(0,0,F(3,2),0)
    assert difference_vector(reverse)==(0,0,-F(3,2),0)
    mean=[F(0)]*4
    for v in permutations(range(6)):
        for i,d in enumerate(difference_vector(v)):
            mean[i]+=d
    assert mean==[0]*4
    rng=Random(20260930)
    for trial in range(12):
        n,m=18,9
        priorities=[]
        for i in range(m):
            values=list(range(n));rng.shuffle(values);priorities.append(values)
        base=list(range(n));windows=[2,8,14]
        initial=projection(priorities,base)
        differences=[]
        for u in windows:
            target=base.copy();target[u],target[u+1]=target[u+1],target[u]
            differences.append(projection(priorities,target)-initial)
        values=[]
        for bits in product([0,1],repeat=len(windows)):
            target=base.copy()
            for u,b in zip(windows,bits):
                if b:target[u],target[u+1]=target[u+1],target[u]
            value=projection(priorities,target)
            assert value==initial+sum((b*d for b,d in zip(bits,differences)),F(0))
            values.append(value)
        assert max(values)-min(values)==sum(abs(d) for d in differences)
    print('Exact covariance at lags0..3, both rank events, swap centering, and 12 binary-family range checks passed.')

if __name__=='__main__':main()
