#!/usr/bin/env python3
"""Exact integer reduced-algebra certificates for signed fair signatures."""
from itertools import combinations, permutations
from fractions import Fraction
from math import factorial, prod
import json


def clean(a): return {w:c for w,c in a.items() if c}
def add(a,b,scale=1):
    c=a.copy()
    for w,x in b.items(): c[w]=c.get(w,0)+scale*x
    return clean(c)
def mul(a,b):
    out={}
    for u,x in a.items():
        for v,y in b.items():
            if set(u).isdisjoint(v):out[u+v]=out.get(u+v,0)+x*y
    return clean(out)
def inverse(g,n):
    z=add(g,{():1},-1)
    ans={():1};power={():1}
    for k in range(1,n+1):
        power=mul(power,z)
        ans=add(ans,power,(-1)**k)
    assert mul(g,ans)=={():1}
    return ans
def bracket_basis(pi,a):
    b={(a,):1}
    for letter in reversed(pi):
        x={(letter,):1}
        b=add(mul(x,b),mul(b,x),-1)
    return b

def construct(counts):
    n=len(counts)
    target={():1}
    for k in range(1,n+1):
        for subset in combinations(range(n),k):
            val=Fraction(prod(counts[i] for i in subset),factorial(k))
            assert val.denominator==1
            for w in permutations(subset):target[w]=int(val)
    g={():1};certificate=[]
    for k in range(1,n+1):
        error=add(mul(inverse(g,n),target),{():1},-1)
        assert all(len(w)>=k for w in error)
        homogeneous={w:c for w,c in error.items() if len(w)==k}
        reconstruction={}
        factors=[]
        for subset in combinations(range(n),k):
            a=subset[0]
            for pi in permutations(subset[1:]):
                c=homogeneous.get(pi+(a,),0)
                if not c:continue
                basis=bracket_basis(pi,a)
                reconstruction=add(reconstruction,basis,c)
                factors.append(add({():1},basis,c))
                certificate.append(dict(order=list(pi+(a,)),power=c))
        assert reconstruction==homogeneous
        for factor in factors:g=mul(g,factor)
    assert g==target
    return dict(counts=counts,coefficients_verified=len(target),
                commutator_factors=len(certificate),certificate=certificate)

if __name__=='__main__':
    for counts in [[2,2],[2,2,3],[6]*3,[6]*4,[18]*4,[30]*5]:
        print(json.dumps(construct(counts)),flush=True)
