"""Exact independent check of the localized evaluation kernels, m=1,...,20."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
rows=[]
for m in range(1,21):
 H=sum(F(1,j) for j in range(1,m+1))
 cs=[H+sum(F((-1)**j*comb(m,j),j) for j in range(1,l+1)) for l in range(m)]
 moments=[sum(c*F((-l)**(a+1)-(-l-1)**(a+1),a+1) for l,c in enumerate(cs)) for a in range(m)]
 assert moments==[F(1)]+[F(0)]*(m-1),(m,moments)
 assert max(abs(c) for c in cs)<=H+2**m
 # Derivative weights, including the last endpoint coefficient.
 assert -cs[-1]==F((-1)**m,m)
 # Test a nonzero rational center and rational total half-width, not only the origin.
 t,h=F(2,5),F(3,70)
 left=[];right=[]
 for a in range(m):
  lv=rv=F(0)
  for l,c in enumerate(cs):
   L=t-h*F(l+1,m);R=t-h*F(l,m)
   lv+=F(m,1)/h*c*(R**(a+1)-L**(a+1))/F(a+1)
   L=t+h*F(l,m);R=t+h*F(l+1,m)
   rv-=F(m,1)/h*c*(R**(a+1)-L**(a+1))/F(a+1)
  assert lv==t**a and rv==-t**a,(m,a,lv,rv)
 rows.append(f'm={m}: all {m} unshifted and {2*m} shifted moments verified exactly; maxabs(c)={max(abs(c) for c in cs)}')
print('\n'.join(rows))
Path(__file__).with_suffix('.txt').write_text('\n'.join(rows)+'\n')
