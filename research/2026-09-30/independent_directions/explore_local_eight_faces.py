"""Heuristic m=c=8 test of scalar-Chebyshev reduction; not a proof.

Analytic Jacobian, complete squarefree centered moments, uniform atom weights.
"""
import json,time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares

m=c=8
masks=[s for s in range(1,1<<m) if s.bit_count()>=2]
targets=np.array([0 if s.bit_count()%2 else 1/(s.bit_count()+1) for s in masks])
involved=[[j for j in range(m) if s>>j&1] for s in masks]
H=np.r_[np.eye(c-1),-np.ones((1,c-1))]
last=None

def data(x):
    y=H@x.reshape(m,c-1).T
    prods=np.ones((1<<m,c))
    for s in range(1,1<<m):
        bit=s&-s;j=bit.bit_length()-1
        prods[s]=prods[s^bit]*y[:,j]
    return y,prods

def fun(x):
    y,p=data(x)
    return p[masks].mean(axis=1)-targets

def jac(x):
    y,p=data(x);J=np.zeros((len(masks),m*(c-1)))
    for row,(s,cols) in enumerate(zip(masks,involved)):
        for j in cols:J[row,j*(c-1):(j+1)*(c-1)]=p[s^(1<<j)]@H/c
    return J

rng=np.random.default_rng(804938)
def scalarfun(a):
    return np.array([np.mean(a**k)-1/(k+1) for k in (2,4,6)])
scalar=least_squares(scalarfun,np.linspace(.12,.89,4),bounds=(.001,.999),gtol=1e-14,ftol=1e-14,xtol=1e-14)
base=np.r_[-np.sort(scalar.x)[::-1],np.sort(scalar.x)]
print('degree7 scalar baseline',base.tolist(),'error8',np.mean(base**8)-1/9,flush=True)
for trial in range(40):
    scale=(.015,.05,.12,.25)[trial%4]
    y=np.tile(base[:,None],(1,m))+rng.normal(0,scale,(c,m))
    y.sort(axis=0);y-=y.mean(axis=0)
    x=y[:c-1,:].T.ravel();tic=time.time()
    fit=least_squares(fun,x,jac=jac,ftol=1e-12,xtol=1e-12,gtol=1e-12,max_nfev=2000)
    yy,_=data(fit.x);err=max(abs(fit.fun));gap=min(np.diff(yy,axis=0).min(),1-abs(yy).max())
    distances=np.max(abs(yy[:,:,None]-yy[:,None,:]),axis=0)
    cluster=max(np.sum(distances<1e-5,axis=1))
    print(trial,'err',err,'gap',gap,'cluster',cluster,'evals',fit.nfev,'seconds',time.time()-tic,flush=True)
    if err<1e-9 and gap>=-1e-7:
        Path('local_eight_numerical_candidate.json').write_text(json.dumps({'y':yy.tolist(),'residual':err,'gap':gap},indent=2))
        print('NUMERICAL CANDIDATE; NOT EXACT CERTIFICATE',flush=True);break
