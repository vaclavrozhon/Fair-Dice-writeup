"""Test a universal scalar-transfer conjecture by exact moment completion geometry.
All outputs are numerical diagnostics, not certificates.
"""
import itertools,json,numpy as np
from scipy.optimize import minimize
K,m=5,4;v=.2
subs={s:list(itertools.combinations(range(m),s)) for s in range(1,m+1)}
def moments(x):
 a=x.reshape(K,m)
 return {s:np.array([np.prod(a[:,S],axis=1).mean() for S in subs[s]]) for s in subs}
def eq(x):
 z=moments(x);return np.r_[z[1],z[2]-v,z[3][1:]-z[3][0]]
def mon(x):return np.diff(x.reshape(K,m),axis=0).ravel()
def gap(x):
 z=moments(x);mu3=z[3].mean();mu4=z[4][0]
 p=np.array([1.,0.,-5*v/2,-5*mu3/3,25*v*v/8-5*mu4/4,0.])
 r=np.roots(np.polyder(p));r.sort();r=r.real
 vals=np.polyval(p,np.r_[-1.,r,1.])
 low=max(-vals[1],-vals[3],-vals[5]);up=min(-vals[0],-vals[2],-vals[4])
 return float(up-low)
rng=np.random.default_rng(913)
best=None
for seed in range(50):
 base=np.sort(rng.uniform(-1,1,K));base-=base.mean();base*=np.sqrt(v/np.mean(base**2))
 if max(abs(base))>.95:continue
 a=np.sort(np.clip(base[:,None]+rng.normal(0,.02,(K,m)),-1,1),axis=0)
 r=minimize(gap,a.ravel(),method='SLSQP',bounds=[(-1,1)]*(K*m),constraints=[{'type':'eq','fun':eq},{'type':'ineq','fun':mon}],options={'maxiter':1500,'ftol':1e-11})
 err=float(max(abs(eq(r.x))));mingap=float(min(mon(r.x)))
 if err<1e-7 and mingap>-1e-7:
  rec={'seed':seed,'completion_gap':gap(r.x),'eq_error':err,'minimum_gap':mingap,'success':bool(r.success),'matrix':r.x.reshape(K,m).tolist(),'moments':{s:z.mean() for s,z in moments(r.x).items()}}
  if best is None or rec['completion_gap']<best['completion_gap']:
   best=rec;print(json.dumps(best),flush=True)
  if rec['completion_gap'] < -1e-6:break
open('research/2026-09-30/independent_directions/probe_antiderivative_transfer.json','w').write(json.dumps(best,indent=2)+'\n')
