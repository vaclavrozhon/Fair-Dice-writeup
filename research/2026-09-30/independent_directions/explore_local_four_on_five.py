"""Heuristic exploration of m=5,c=5; output is not a proof."""
import numpy as np
from scipy.optimize import least_squares
from itertools import combinations
from math import sqrt
m=4;c=5
H=np.r_[np.eye(c-1),-np.ones((1,c-1))]
subsets=[S for k in range(2,m+1) for S in combinations(range(m),k)]
target=np.array([0 if len(S)%2 else 1/(len(S)+1) for S in subsets])
def resid(x):
 y=H@x.reshape(m,c-1).T
 return np.array([np.mean(np.prod(y[:,S],axis=1)) for S in subsets])-target
u=sqrt((5-sqrt(11))/12);v=sqrt((5+sqrt(11))/12)
base=np.array([-v,-u,0,u,v]);coef=base[:c-1]
rng=np.random.default_rng(37033)
for trial in range(12):
 x=np.tile(coef,(m,1))+rng.normal(scale=.09,size=(m,c-1))
 res=least_squares(resid,x.ravel(),ftol=1e-12,xtol=1e-12,gtol=1e-12,max_nfev=3000)
 err=max(abs(res.fun));y=H@res.x.reshape(m,c-1).T
 mono=np.all(np.diff(y,axis=0)>-1e-6) and np.max(abs(y))<=1+1e-6
 if err>1e-7 or not mono:
  print(trial,'failed',err,'monotone',mono,flush=True);continue
 d=np.array([[max(abs(y[:,i]-y[:,j])) for j in range(m)] for i in range(m)])
 cluster=max(sum(d[i]<1e-4) for i in range(m))
 print(trial,'err',err,'max identical cluster',cluster,'d',np.round(d,4).tolist(),flush=True)
 if cluster<2:
  print('NONSYMMETRIC FOUND',y.tolist(),flush=True)
  break
