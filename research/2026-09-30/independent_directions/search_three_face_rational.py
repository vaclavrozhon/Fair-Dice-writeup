"""Rational-point search on the exact c=m=3 comparison-tensor variety.
Select first centered comparison column (a,b,-a-b) with denominator D.
The other columns are rational exactly when a displayed discriminant is a square,
apart from degenerate cases which are separately checked.
"""
from math import gcd,isqrt
from fractions import Fraction as F
from time import monotonic
start=monotonic();cand=0
for D in range(1, 1001):
 for A in range(-D,0):
  for B in range(A,min(D,(-A)//2)+1):
   if -A-B>D or gcd(gcd(abs(A),abs(B)),D)>1:continue
   Q=A*A+A*B+B*B
   z=81*A*A*B*B*(A+B)*(A+B)+12*D*D*Q*(D*D-2*Q)
   if z<0:continue
   sz=isqrt(z)
   if sz*sz!=z:continue
   a,b=F(A,D),F(B,D)
   ca=6*a*a-3*a*b-3*b*b
   cb=9*a*a*b+9*a*b*b-6*a
   cc=a*a-2*a*b-2*b*b+1
   if not ca or not a+2*b:continue
   for c in [(-cb+F(sz,D**3))/(2*ca),(-cb-F(sz,D**3))/(2*ca)]:
    d=(1-(2*a+b)*c)/(a+2*b)
    v=(c,d,-c-d);u=(a,b,-a-b)
    if list(v)!=sorted(v) or min(v)<-1 or max(v)>1:continue
    det=(2*a+b)*(c+2*d)-(a+2*b)*(2*c+d)
    if not det:continue
    e=(c+2*d-a-2*b)/det
    f=(2*a+b-2*c-d)/det
    w=(e,f,-e-f)
    if list(w)!=sorted(w) or min(w)<-1 or max(w)>1:continue
    assert sum(x*y for x,y in zip(u,v))==1
    assert sum(x*y for x,y in zip(u,w))==1
    assert sum(x*y for x,y in zip(v,w))==1
    assert sum(x*y*z for x,y,z in zip(u,v,w))==0
    print('FOUND',D,u,v,w,flush=True)
    raise SystemExit
   cand+=1
 if D%25==0:print('D',D,'square candidates',cand,'sec',round(monotonic()-start,1),flush=True)
