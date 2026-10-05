"""Numerical exploration only: m=4 comparison functions on c=4 atoms.
This does not certify rational feasibility or nonexistence.
"""
import numpy as np
from scipy.optimize import least_squares
from itertools import combinations
from math import sqrt
H=np.array([[-1,-1,-1],[-1,1,1],[1,-1,1],[1,1,-1]],float)
subsets=[S for k in range(2,5) for S in combinations(range(4),k)]
target=np.array([0 if len(S)%2 else 1/(len(S)+1) for S in subsets])
def resid(x):
 y=H@x.reshape(4,3).T
 return np.array([np.mean(np.prod(y[:,S],axis=1)) for S in subsets])-target
u=sqrt((5-2*sqrt(5))/15);v=sqrt((5+2*sqrt(5))/15)
base=np.array([-v,-u,u,v]);coef=H.T@base/4
rng=np.random.default_rng(37032)
for trial in range(60):
 x=np.tile(coef,(4,1))+rng.normal(scale=.15,size=(4,3))
 res=least_squares(resid,x.ravel(),ftol=1e-13,xtol=1e-13,gtol=1e-13,max_nfev=5000)
 err=max(abs(res.fun));y=H@res.x.reshape(4,3).T
 mono=np.all(np.diff(y,axis=0)>-1e-7) and np.max(abs(y))<=1+1e-7
 if err>1e-8 or not mono:
  print(trial,'failed',err,'monotone',mono,flush=True);continue
 d=np.array([[max(abs(y[:,i]-y[:,j])) for j in range(4)] for i in range(4)])
 cluster=max(sum(d[i]<1e-5) for i in range(4))
 print(trial,'err',err,'max identical cluster',cluster,'d',np.round(d,5).tolist(),flush=True)
 if cluster<3:
  print('NONSYMMETRIC FOUND',y.tolist(),flush=True)
  break
