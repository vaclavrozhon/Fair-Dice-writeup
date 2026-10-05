#!/usr/bin/env python3
"""Finite exact checks for p_adic_lower_bound.tex; not a replacement for proof."""
from fractions import Fraction as Q
from math import comb
from verify_two_adic import rational_binom


def vp(x,p):
    x=Q(x)
    if not x:return float('inf')
    n,d=abs(x.numerator),x.denominator
    v=0
    while n%p==0:n//=p;v+=1
    while d%p==0:d//=p;v-=1
    return v


def check(p,N,R):
    b=[Q(1)];h=Q(0);vals=[]
    for j in range(1,R+1):
        c=[Q(0)]*(len(b)+1)
        for k,v in enumerate(b):
            c[k]-=Q(j-1,j)*v
            c[k+1]+=Q(N,j)*v
        b=c
        coefficient=-sum((-1)**(j-k)*comb(j,k) for k in range(0,j+1,p))
        h+=coefficient*sum(v/(k+1) for k,v in enumerate(b))
        assert vp(h,p)>=j//p,(p,N,j,h,vp(h,p))
        vals.append(vp(h,p))
    return vals


for p in (2,3,5,7,11):
    for a in (1,2,3):
        vals=check(p,p**a,64)
        print(f'p={p},a={a}: degree<=64 passed; first12={vals[:12]}')
    for r in range(1,17):
        coeff=[0]+[-sum((-1)**(j-k)*comb(j,k) for k in range(0,j+1,p))
                   for j in range(1,r+1)]
        for den in range(1,9):
            if den%p==0:continue
            for num in range(-8,9):
                y=Q(num,den)
                h=sum(coeff[j]*rational_binom(y,j) for j in range(1,r+1))
                assert vp(h-(num%p!=0),p)>=r//(p-1),(p,r,y,h)
print('All general-prime integral and unit-filter exact checks passed.')
