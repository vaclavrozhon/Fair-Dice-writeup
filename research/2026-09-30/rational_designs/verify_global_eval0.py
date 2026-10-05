#!/usr/bin/env python3
"""Independent full-order exact integration test for eval-at-zero lifting.

This implements the original global proof, with moment bumps constructed
by exact Gaussian elimination. It does not use the centered-kernel code.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import factorial
from pathlib import Path
import json
import sys


def solve(A,b):
    n=len(b);A=[row[:]+[v] for row,v in zip(A,b)]
    for k in range(n):
        row=next(i for i in range(k,n) if A[i][k])
        A[k],A[row]=A[row],A[k]
        pivot=A[k][k];A[k]=[x/pivot for x in A[k]]
        for i in range(n):
            if i!=k:
                q=A[i][k]
                A[i]=[a-q*b for a,b in zip(A[i],A[k])]
    return [row[-1] for row in A]


def construct(source):
    a=json.loads(Path(source).read_text())
    m,K=a['m'],a['K'];D=int(a['denominator'])
    t=[Q(int(x),D) for x in a['baseline_numerators']]
    corr=[{int(q):Q(v) for q,v in row.items()} for row in a['corrections']]
    width=min(t[0],1-t[-1],*(t[q+1]-t[q] for q in range(K-1)))/10
    pieces=[]
    for j,row in enumerate(corr):
        for q,delta in row.items():
            moments=[]
            for sign,start in ((1,t[q]-2*width),(-1,t[q]+width)):
                intervals=[(start+width*l/m,start+width*(l+1)/m) for l in range(m)]
                M=[[(b**(s+1)-a**(s+1))/(s+1) for a,b in intervals] for s in range(m)]
                coeff=solve(M,[Q(sign)]+[Q(0)]*(m-1))
                assert all(sum(M[s][l]*coeff[l] for l in range(m))==(sign if s==0 else 0) for s in range(m))
                for (left,right),c in zip(intervals,coeff):pieces.append((left,right,j,delta*c))
    boundaries=sorted(set([Q(0),Q(1)]+t+[x for a,b,_,_ in pieces for x in (a,b)]))
    atoms=set(t);operations=[];total=[Q(0)]*m;minimum=Q(1)
    for left,right in zip(boundaries,boundaries[1:]):
        middle=(left+right)/2;densities=[Q(1)]*m
        for a,b,j,c in pieces:
            if a<middle<b:densities[j]+=c
        assert min(densities)>0
        minimum=min(minimum,min(densities))
        mass=[v*(right-left) for v in densities]
        total=[a+b for a,b in zip(total,mass)]
        operations.append(('interval',mass))
        if right in atoms:operations.append(('atom',Q(1,K)))
    assert total==[1]*m
    print(f'm={m}, K={K}: moment bumps and positive normalized densities certified; min density approximately {float(minimum):.12g}',flush=True)
    n=m+1;checked=0
    for order in permutations(range(n)):
        dp=[Q(1)]+[Q(0)]*n
        for kind,data in operations:
            if kind=='atom':
                at=order.index(m)+1
                dp[at]+=data*dp[at-1]
            else:
                old=dp[:]
                for end in range(1,n+1):
                    product=Q(1)
                    for start in range(end-1,-1,-1):
                        die=order[start]
                        if die==m:break
                        product*=data[die]
                        dp[end]+=old[start]*product/factorial(end-start)
        assert dp[n]==Q(1,factorial(n)),(order,dp[n])
        checked+=1
    print(f'All {checked} full ranking probabilities equal exactly 1/{factorial(n)}.',flush=True)


if __name__=='__main__':
    source=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('local_model_m3.json')
    construct(source)
