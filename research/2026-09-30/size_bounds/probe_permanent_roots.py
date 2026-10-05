#!/usr/bin/env python3
import sympy as s
from math import factorial
import json,time
z=s.Symbol('z')
def roots(m,K):
 c=[s.Rational(1)]+[s.Rational(0)]*m
 for j in range(2,m+1,2):c[j]=-K*sum(c[j-h]/(h+1) for h in range(2,j+1,2))/j
 p=s.Poly.from_list([s.Rational(factorial(m)//factorial(m-j),factorial(K)//factorial(K-j))*c[j] for j in range(m+1)],z)
 return p.count_roots(-1,1)
for m in (40,60,80,100,150,200):
 start=time.monotonic();lo=m;hi=2*m
 while lo<hi:
  K=(lo+hi)//2;r=roots(m,K)
  print(json.dumps({'m':m,'K':K,'real_roots':int(r),'elapsed':time.monotonic()-start}),flush=True)
  if r==m:hi=K
  else:lo=K+1
 print(json.dumps({'m':m,'threshold_assuming_monotonicity':lo,'seconds':time.monotonic()-start}),flush=True)
