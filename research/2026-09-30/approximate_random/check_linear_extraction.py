"""Test whether degree-five order errors linearly determine triple projection.
Numerical ranks are diagnostic only; exact modular/rational certificates follow.
"""
from itertools import permutations
from fractions import Fraction as Q
import math
import numpy as np

def count(word, pattern):
    dp = [1] + [0]*len(pattern)
    for x in word:
        for j in range(len(pattern)-1,-1,-1):
            if pattern[j]==x: dp[j+1]+=dp[j]
    return dp[-1]

def matrices(m):
    ps=list(permutations(range(5)))
    ds=[]
    for p in ps:
        w=p+p[::-1]
        ds.append({t: Q(count(w,t))-Q(2**k, math.factorial(k))
                   for k in (3,4,5) for t in permutations(range(5),k)})
    A=np.zeros((120,m*120),dtype=np.int64)
    B=np.zeros_like(A)
    for i in range(m):
        for r,delta in enumerate(ds):
            for row,p in enumerate(ps):
                for a in range(3):
                    for b in range(3-a):
                        k=5-a-b
                        v=15*Q((2*i)**a,math.factorial(a))*delta[p[a:a+k]]*Q((2*(m-1-i))**b,math.factorial(b))
                        assert v.denominator==1
                        A[row,i*120+r]+=v.numerator
                        if k==3:B[row,i*120+r]+=v.numerator
    slot=np.zeros((m,m*120),dtype=np.int64)
    for i in range(m):slot[i,i*120:(i+1)*120]=1
    return A,B,slot
if __name__=='__main__':
    for m in (1,2,3,4,6):
        A,B,slot=matrices(m)
        C=np.concatenate([A,slot])
        print(m, np.linalg.matrix_rank(C), np.linalg.matrix_rank(np.concatenate([C,B])), flush=True)
    np.savez_compressed('research/2026-09-30/approximate_random/linear_extraction_n5.npz',A=A,B=B,slot=slot)
