#!/usr/bin/env python3
"""Compute exact least denominator of Wilson/Hahn projection grid weights.

Binomial-basis coefficients characterize integer-valued polynomials:
all W(0),...,W(N) are integers iff all Newton coefficients are integers,
provided N>=degree. Thus their denominator LCM is the exact answer.
"""
from fractions import Fraction as Q
from math import comb, lcm, log2, prod
import argparse
import json


def integrated_binomials(N, n):
    p = [Q(1)]
    js = [Q(N)]
    for j in range(1, n+1):
        out = [Q(0)]*(j+1)
        for i, c in enumerate(p):
            out[i] -= Q(j-1, j)*c
            out[i+1] += c/j
        p = out
        js.append(sum((c*Q(N**(i+1), i+1) for i, c in enumerate(p)), Q(0)))
    return js


def coefficients(n, N):
    js = integrated_binomials(N, n)
    a = [Q(0)]*(n+1)
    for k in range(n+1):
        qk = [Q((-1)**j*comb(k, j)*comb(k+j, j), comb(N, j))
              for j in range(k+1)]
        ik = sum((c*x for c, x in zip(qk, js)), Q(0))
        if k % 2:
            assert ik == 0
            continue
        hk = Q((N+1)*comb(N+k+1, k), (2*k+1)*comb(N, k))
        for j, c in enumerate(qk):
            a[j] += ik*c/hk
    return a


def compute(n, verify=False):
    N = n*(n+2)
    a = coefficients(n, N)
    M = lcm(*(x.denominator for x in a))
    legacy = (N+1)*lcm(*range(1, n+2))*prod(range(N-n+1, N+1))*prod(range(N+2, N+n+2))
    assert legacy % M == 0
    if verify:
        w = [sum((c*comb(i,j) for j,c in enumerate(a) if j<=i), Q(0))
             for i in range(N+1)]
        assert min(w)>0
        assert sum(w)==N
        assert lcm(*(x.denominator for x in w))==M
        for k in range(n+1):
            assert sum(x*i**k for i,x in enumerate(w)) == Q(N**(k+1), k+1)
    return dict(n=n,N=N,M=str(M),M_bits=log2(M),
                leading_ratio=log2(M)/(n*log2(n)) if n>1 else None,
                legacy_bits=log2(legacy),improvement_bits=log2(legacy//M),
                final_faces_bits=log2(M)+(n-1)*log2(N))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('n',type=int,nargs='*',default=list(range(2,21)))
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    for n in args.n:
        print(json.dumps(compute(n,args.verify)),flush=True)
