"""Heuristic search for weakly monotone m=K=5 models with two flat columns.

Two prescribed plateaus are imposed exactly by the parametrization.
Other monotonicity and interval conditions enter as a numerical penalty.
No negative search result is a nonexistence proof.
"""
import json,time
from pathlib import Path
from itertools import combinations
from math import sqrt
import numpy as np
from scipy.optimize import least_squares

m=c=5
subsets=[S for k in range(2,m+1) for S in combinations(range(m),k)]
target=np.array([0 if len(S)%2 else 1/(len(S)+1) for S in subsets])
rng=np.random.default_rng(529403)
u=sqrt((5-sqrt(11))/12);v=sqrt((5+sqrt(11))/12)
base=np.array([-v,-u,0,u,v])

def basis(cut):
    labels=list(range(c))
    if cut is not None:labels[cut+1]=labels[cut]
    unique=sorted(set(labels));group=[unique.index(x) for x in labels]
    counts=np.bincount(group)
    H=np.zeros((c,len(unique)-1))
    for q,g in enumerate(group):
        if g<len(unique)-1:H[q,g]=1
        else:H[q,:]=-counts[:-1]/counts[-1]
    return H

for q1 in range(4):
 for q2 in range(q1,4):
    H=[basis(q1),basis(q2)]+[basis(None)]*3
    offsets=np.r_[0,np.cumsum([h.shape[1] for h in H])]
    def unpack(x):return np.stack([h@x[offsets[j]:offsets[j+1]] for j,h in enumerate(H)],axis=1)
    def fun(x):
        y=unpack(x)
        moments=np.array([np.mean(np.prod(y[:,S],axis=1)) for S in subsets])-target
        return np.r_[moments,10*np.minimum(np.diff(y,axis=0),0).ravel(),10*np.maximum(y-1,0).ravel(),10*np.minimum(y+1,0).ravel()]
    best=1e9
    for trial in range(15):
        x=np.concatenate([np.linalg.lstsq(h,base+rng.normal(0,.08,c),rcond=None)[0] for h in H])
        fit=least_squares(fun,x,ftol=1e-12,xtol=1e-12,gtol=1e-12,max_nfev=2000)
        y=unpack(fit.x);err=max(abs(fit.fun));best=min(best,err)
        if err<1e-8:
            dis=np.max(abs(y[:,:,None]-y[:,None,:]),axis=0)
            cluster=max(np.sum(dis<1e-5,axis=1))
            print('candidate',q1,q2,trial,'error',err,'cluster',cluster,y.tolist(),flush=True)
            Path('weak_five_numerical_candidate.json').write_text(json.dumps({'y':y.tolist(),'error':err,'cluster':int(cluster)},indent=2))
            raise SystemExit
    print('cuts',q1,q2,'best max residual',best,flush=True)
