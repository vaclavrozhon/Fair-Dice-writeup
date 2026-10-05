import numpy as np
from pathlib import Path
from scipy.optimize import linprog
A=np.array([-5,-3,1,3,4])/6
M3=np.mean(A**3);M4=np.mean(A**4)
def vecu(x,y):return np.array([-x-7*y/4+5/6,2*x+27*y/8-5/4,-2*x-21*y/8+5/12,x,y])
def evaluate(x,y):
 u=vecu(x,y);b=A+u
 mat=np.array([np.ones(5),A,u,A*A,A*u,A**3+A*A*u])
 rhs=np.array([0,0,0,-5*M3,5*M3,1-5*M4-np.dot(A**3,u)])
 v,res,rank,_=np.linalg.lstsq(mat,rhs,rcond=None)
 c=A+v
 gap=lambda z:min(z[0]+1,1-z[-1],*np.diff(z))
 return min(gap(b),gap(c)),b,c,np.linalg.norm(mat@v-rhs)
# Coefficient of y^3, y^2, y^1, y^0 at fixed x.
best=(-1e9,None)
real=[]
for x in np.linspace(-1,1,20001):
 coeff=[107163,303912*x-37422,205056*x*x-190848*x+12012,36864*x**3-87552*x*x+47264*x-3640]
 for y in np.roots(coeff):
  if abs(y.imag)>1e-8:continue
  y=float(y.real)
  score,b,c,err=evaluate(x,y)
  if err<1e-8 and score>best[0]:best=(score,(x,y,b.tolist(),c.tolist(),err))
  if score>0 and err<1e-8:real.append((x,y,score))
print('best',best,'positive_count',len(real),flush=True)
Path(__file__).with_suffix('.txt').write_text(repr(best)+'\npositive_count='+str(len(real))+'\n')
