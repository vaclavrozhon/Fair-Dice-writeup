"""Generic scalar-transfer boundary diagnostic, not a fair-dice search or proof."""
import itertools,json,numpy as np
from scipy.optimize import minimize
K,m=6,4
subs={s:list(itertools.combinations(range(m),s)) for s in range(1,m+1)}
rng=np.random.default_rng(42421)
def moments(x):
 a=x.reshape(K,m)
 return {s:np.array([np.prod(a[:,S],axis=1).mean() for S in subs[s]]) for s in subs}
records=[]
for skew in [.2,.5,.8,1.1]:
 def seq(x):return np.array([np.mean(x),np.mean(x*x)-1,np.mean(x**3)-skew])
 scalar=None
 for rep in range(40):
  x=rng.normal(size=K);x-=x.mean();x/=np.sqrt(np.mean(x*x))
  r=minimize(lambda x:np.mean(x**4),x,method='SLSQP',constraints=[{'type':'eq','fun':seq}],options={'ftol':1e-12,'maxiter':500})
  if max(abs(seq(r.x)))<1e-7 and (scalar is None or r.fun<scalar.fun):scalar=r
 if scalar is None:continue
 scalar_value=float(scalar.fun)
 def eq(x):
  z=moments(x);return np.r_[z[1],z[2]-1,z[3]-skew]
 def mon(x):return np.diff(x.reshape(K,m),axis=0).ravel()
 def obj(x):return moments(x)[4][0]
 best=None
 for rep in range(35):
  base=np.sort(scalar.x)
  a=np.sort(base[:,None]+rng.normal(0,.1,(K,m)),axis=0)
  r=minimize(obj,a.ravel(),method='SLSQP',bounds=[(-5,5)]*(K*m),constraints=[{'type':'eq','fun':eq},{'type':'ineq','fun':mon}],options={'ftol':1e-11,'maxiter':1000})
  err=float(max(abs(eq(r.x))));mingap=float(min(mon(r.x)))
  if err<1e-7 and mingap>-1e-7:
   rec={'skew':skew,'scalar_min_numerical':scalar_value,'tensor_fourth':obj(r.x),'gap':obj(r.x)-scalar_value,'eq_error':err,'minimum_gap':mingap,'matrix':r.x.reshape(K,m).tolist(),'scalar_nodes':scalar.x.tolist()}
   if best is None or rec['gap']<best['gap']:best=rec;print(json.dumps(rec),flush=True)
   if rec['gap'] < -1e-5:break
 records.append(best)
 if best is not None and best['gap'] < -1e-5:break
open('research/2026-09-30/independent_directions/probe_transfer_skew.json','w').write(json.dumps(records,indent=2)+'\n')
