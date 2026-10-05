"""Exact rational baselines; numerical local tensor feasibility only."""
from fractions import Fraction as F
import numpy as np
from scipy.optimize import least_squares
from pathlib import Path
import json
base=list(map(lambda x:F(x,6),[-5,-3,1,3,4]))
big=np.sqrt((5+np.sqrt(11))/12);small=np.sqrt((5-np.sqrt(11))/12)
target=np.array([-big,-small,0,small,big])
def baseline(D):
 direction=[F(round(D*(target[i]-float(base[i]))),D) for i in range(4)]
 direction.append(-sum(direction))
 q=-2*sum(a*v for a,v in zip(base,direction))/sum(v*v for v in direction)
 return [a+q*v for a,v in zip(base,direction)]
def residual(z,a):
 u,v=z[:5],z[5:]
 b,c=a+u,a+v
 return np.array([u.mean(),np.mean(a*u),np.mean(a*a*b),
                  v.mean(),np.mean(a*v),np.mean(a*a*c),
                  np.mean(u*v),np.mean(a*b*c),np.mean(a*a*b*c)-.2])
def gap(z):return min(z[0]+1,1-z[-1],*np.diff(z))
rng=np.random.default_rng(532)
out=[]
for D in [10,20,50,100,200,500,1000,2000,5000]:
 aq=baseline(D);a=np.array(list(map(float,aq)));best=(float('inf'),None)
 for trial in range(30):
  z0=rng.normal(0,2/np.sqrt(D),10)
  fit=least_squares(residual,z0,args=(a,),max_nfev=2000,gtol=1e-13,ftol=1e-13,xtol=1e-13)
  err=np.linalg.norm(fit.fun)
  if err<best[0]:best=(err,fit.x)
  if err<1e-10 and min(gap(a+fit.x[:5]),gap(a+fit.x[5:]))>0:
   z=fit.x;record={'D':D,'a':list(map(str,aq)),'u':z[:5].tolist(),'v':z[5:].tolist(),'err':err,'gap':min(gap(a+z[:5]),gap(a+z[5:]))}
   out.append(record);print('FEASIBLE',record,flush=True);break
 else:print('no feasible',D,'best residual',best[0],flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
