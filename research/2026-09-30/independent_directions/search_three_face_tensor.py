"""Search rational ordered 3-component mixtures for three comparison bits.
Coordinates y=2p-1. Column sums=0, pair dot products=1,
triple coordinatewise-product sum=0. All columns use denominator D.
"""
from fractions import Fraction
from math import gcd
from time import monotonic
start=monotonic()
for D in range(1, 81):
    columns=[]
    for a in range(-D,1):
        for b in range(a,D+1):
            c=-a-b
            if b<=c<=D:
                columns.append((a,b,c))
    nbr=[set() for _ in columns]
    for i,x in enumerate(columns):
        for j in range(i,len(columns)):
            y=columns[j]
            if sum(a*b for a,b in zip(x,y))==D*D:
                nbr[i].add(j)
                nbr[j].add(i)
    count=0
    for i,x in enumerate(columns):
        for j in nbr[i]:
            if j<i: continue
            y=columns[j]
            for k in nbr[i]&nbr[j]:
                if k<j: continue
                z=columns[k]
                count+=1
                if sum(a*b*c for a,b,c in zip(x,y,z))==0:
                    print('FOUND',D,x,y,z,flush=True)
                    raise SystemExit
    print('D',D,'columns',len(columns),'pair-cliques',count,'sec',round(monotonic()-start,1),flush=True)
