"""Numerical diagnostic of a universal monotone-to-scalar moment conjecture."""
import itertools,json,numpy as np
from scipy.optimize import minimize
m=4; v=.2
subs={s:list(itertools.combinations(range(m),s)) for s in range(1,m+1)}
rng=np.random.default_rng(713)
records=[]
for K in [6,8,12,20]:
 def moments(x):
  a=x.reshape(K,m)
  return {s:np.array([np.prod(a[:,S],axis=1).mean() for S in subs[s]]) for s in subs}
 def eq(x):
  z=moments(x);return np.r_[z[1],z[2]-v,z[3]]
 def mon(x):return np.diff(x.reshape(K,m),axis=0).ravel()
 def obj(x):return float(moments(x)[4][0]-v*v)
 best=None
 for seed in range(20):
  base=np.linspace(-1,1,K);base*=np.sqrt(v/np.mean(base**2))
  a=np.sort(np.clip(base[:,None]+rng.normal(0,.15,(K,m)),-1,1),axis=0)
  r=minimize(obj,a.ravel(),method='SLSQP',bounds=[(-1,1)]*(K*m),constraints=[{'type':'eq','fun':eq},{'type':'ineq','fun':mon}],options={'maxiter':1500,'ftol':1e-11})
  err=float(max(abs(eq(r.x))));gap=float(min(mon(r.x)))
  if err<1e-7 and gap>-1e-7:
   rec={'K':K,'seed':seed,'objective':obj(r.x),'eq_error':err,'minimum_gap':gap,'success':bool(r.success),'matrix':r.x.reshape(K,m).tolist()}
   if best is None or rec['objective']<best['objective']:
    best=rec;print(json.dumps(best),flush=True)
   if rec['objective'] < -1e-5:break
 records.append(best)
 if best and best['objective'] < -1e-5:break
open('research/2026-09-30/independent_directions/probe_generic_transfer.json','w').write(json.dumps(records,indent=2)+'\n')
