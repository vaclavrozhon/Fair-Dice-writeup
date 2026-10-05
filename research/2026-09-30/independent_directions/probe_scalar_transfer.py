"""Diagnostic only for the general monotone-to-scalar transfer conjecture.
The dimension is small solely to test a proposed universal lemma, not to
search for small dice. A negative output needs an exact certificate.
"""
import itertools,json,numpy as np
from scipy.optimize import minimize
K,m=5,4
subs={s:list(itertools.combinations(range(m),s)) for s in range(1,m+1)}
def moments(x):
 a=x.reshape(K,m)
 return {s:np.array([np.prod(a[:,S],axis=1).mean() for S in subs[s]]) for s in subs}
def eq(x):
 z=moments(x)
 return np.r_[z[1],z[2][1:]-z[2][0],z[3]]
def mon(x):return np.diff(x.reshape(K,m),axis=0).ravel()
def obj(x):
 z=moments(x);v=z[2].mean()
 return float(z[4][0]-1.25*v*v)
rng=np.random.default_rng(167)
best=None
for seed in range(60):
 base=np.array([-1,-.4,0,.4,1])*.9
 a=np.sort(np.clip(base[:,None]+rng.normal(0,.06,(K,m)),-1,1),axis=0)
 r=minimize(obj,a.ravel(),method='SLSQP',bounds=[(-1,1)]*(K*m),constraints=[{'type':'eq','fun':eq},{'type':'ineq','fun':mon}],options={'maxiter':1200,'ftol':1e-12})
 err=float(max(abs(eq(r.x))));gap=float(min(mon(r.x)))
 if err<1e-7 and gap>-1e-7:
  rec={'seed':seed,'objective':obj(r.x),'eq_error':err,'minimum_gap':gap,'success':bool(r.success),'matrix':r.x.reshape(K,m).tolist()}
  if best is None or rec['objective']<best['objective']:
   best=rec;print(json.dumps(best),flush=True)
  if rec['objective'] < -1e-6:break
open('research/2026-09-30/independent_directions/probe_scalar_transfer.json','w').write(json.dumps(best,indent=2)+'\n')
