#!/usr/bin/env python3
"""Construct and verify the integer quadrature used for C(n!)^2 fair dice.

All calculations, including flooring, use exact integer/rational arithmetic.
The output is a compact insertion plan; no exponential-length word is expanded.
"""
from fractions import Fraction as Q
from math import comb, factorial
from hahn_denominators import coefficients, integrated_binomials
import argparse
import json


def construct(r, C=2**25, include_weights=False):
    N=(r+1)**2
    K=C*factorial(r+1)**2
    coeff=coefficients(r,N)
    weights=[sum((a*comb(i,j) for j,a in enumerate(coeff) if j<=i),Q(0))/N
             for i in range(N+1)]
    assert min(weights)>Q(1,8*N)
    assert sum(weights)==1
    target=[K*x/N for x in integrated_binomials(N,r)]
    assert all(x.denominator==1 for x in target)
    floors=[(K*w).numerator//(K*w).denominator for w in weights]
    b=[int(target[j])-sum(k*comb(i,j) for i,k in enumerate(floors) if i>=j)
       for j in range(r+1)]
    assert all(0<=x<=comb(N+1,j+1) for j,x in enumerate(b))
    correction=[sum((-1)**(j-i)*comb(j,i)*b[j] for j in range(i,r+1))
                for i in range(r+1)]
    k=[v+(correction[i] if i<=r else 0) for i,v in enumerate(floors)]
    assert min(k)>=0
    assert sum(k)==K
    # Verify moments independently in the monomial basis.
    for j in range(r+1):
        assert sum(v*i**j for i,v in enumerate(k)) == Q(K*N**j,j+1)
    result=dict(r=r,N=N,C=C,total_faces=str(K),minimum_gap=str(min(k)),
                maximum_correction=str(max(abs(x) for x in correction)),
                minimum_initial_weight=str(min(weights)),
                monomial_moments_verified=r+1)
    if include_weights:
        result['gaps']=[str(x) for x in k]
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-r',type=int,default=16)
    parser.add_argument('--C',type=int,default=2**25)
    parser.add_argument('--weights',action='store_true')
    args=parser.parse_args()
    for r in range(1,args.max_r+1):
        print(json.dumps(construct(r,args.C,args.weights)),flush=True)
