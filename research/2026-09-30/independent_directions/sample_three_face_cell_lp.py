"""Explore necessary four-cell LP for real c=m=3 local comparison tensors."""
from itertools import permutations,product
import numpy as np
from scipy.optimize import linprog
from math import sqrt
P=list(permutations(range(4))); O=list(permutations(range(3)))
# Precompute assignment-to-order maps independent of masses.
assign=[]
for qi in range(3):
 for cells in product(range(4),repeat=3):
  occup=[[i for i in range(3) if cells[i]==g] for g in range(4)]
  together=next((g for g,I in enumerate(occup) if len(I)>1),None)
  if together is None:
   pi=tuple(sorted(range(4),key=lambda i:2*qi+1 if i==3 else 2*cells[i]))
   assign.append((cells,None,P.index(pi)))
  else:
   inds=[]
   for sigma in O:
    pi=tuple(sorted(range(4),key=lambda i:(2*qi+1,0) if i==3 else (2*cells[i],sigma.index(i))))
    inds.append(P.index(pi))
   assign.append((cells,together,inds))
def lp(ys):
 p=(np.array(ys)+1)/2
 w=np.diff(np.c_[np.zeros(3),p,np.ones(3)],axis=1)
 if w.min()<-1e-7:return None
 A=np.zeros((28,24));b=np.r_[np.ones(24)/24,np.ones(4)]
 for cells,g,inds in assign:
  wt=np.prod(w[np.arange(3),cells])/3
  if g is None:b[inds]-=wt
  else:
   for si,ii in enumerate(inds):A[ii,6*g+si]+=wt
 for g in range(4):A[24+g,6*g:6*g+6]=1
 res=linprog(np.r_[np.zeros(24),-1],A_ub=np.c_[-np.eye(24),np.ones(24)],b_ub=np.zeros(24),A_eq=np.c_[A,np.zeros(28)],b_eq=b,bounds=[(0,None)]*25,method='highs')
 return res
if __name__=='__main__':
 ys=[[-1/sqrt(2),0,1/sqrt(2)]]*3
 r=lp(ys);print('symmetric',r.success,r.fun,flush=True)
 rng=np.random.default_rng(478839)
 tested=0;feasible=0
 for sample in range(2000):
  a=-1/sqrt(2)+rng.uniform(-.12,.12);b=rng.uniform(-.1,.1)
  ca=6*a*a-3*a*b-3*b*b;cb=9*a*a*b+9*a*b*b-6*a;cc=a*a-2*a*b-2*b*b+1
  dis=cb*cb-4*ca*cc
  if dis<0 or abs(ca)<1e-10 or abs(a+2*b)<1e-10:continue
  c=(-cb+sqrt(dis))/(2*ca);d=(1-(2*a+b)*c)/(a+2*b)
  det=(2*a+b)*(c+2*d)-(a+2*b)*(2*c+d)
  if abs(det)<1e-10:continue
  e=(c+2*d-a-2*b)/det;f=(2*a+b-2*c-d)/det
  ys=[[a,b,-a-b],[c,d,-c-d],[e,f,-e-f]]
  res=lp(ys)
  if res is None:continue
  tested+=1
  if res.success:
   feasible+=1
   print('FEASIBLE',tested,'margin',res.x[-1],'ys',ys,flush=True)
   if feasible>=3:break
  if tested%50==0:print('tested',tested,'feasible',feasible,flush=True)
 print('TOTAL',tested,feasible)
