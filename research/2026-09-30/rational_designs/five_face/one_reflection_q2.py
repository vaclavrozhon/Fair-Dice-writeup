"""Seek a 2-adic Hensel certificate in the one-reflection-pair family.
Coordinates are scaled by 2. A certificate proves local solubility only.
"""
import itertools,json,random,sys
from pathlib import Path
import sympy as sy
depth=int(sys.argv[1]) if len(sys.argv)>1 else 1
T=5*2**(2*depth-1);U=2**(4*depth-1)
v=sy.symbols('r s R S z t u w');r,s,R,S,z,t,u,w=v
F=[3*(r*R+s*S)-T,3*(r*z+s*t)-T,3*(R*z+S*t)-T,u*r*R+w*s*S,3*(z*z+t*t-3*u*u-4*u*w-3*w*w)-T,(z*z-u*u)*r*R+(t*t-w*w)*s*S-U]
J=sy.Matrix(F).jacobian(v)
ff=sy.lambdify([v],F,'math');jj=sy.lambdify([v],J.tolist(),'math')
def solve_mod2(mat,rhs):
 a=[[int(x)%2 for x in row]+[int(t)%2] for row,t in zip(mat,rhs)];rank=0;piv=[]
 for c in range(8):
  hit=next((i for i in range(rank,6) if a[i][c]),None)
  if hit is None:continue
  a[rank],a[hit]=a[hit],a[rank]
  for i in range(6):
   if i!=rank and a[i][c]:a[i]=[(x-y)%2 for x,y in zip(a[i],a[rank])]
  piv.append(c);rank+=1
  if rank==6:break
 if any(row[-1] for row in a[rank:]):return None
 part=[0]*8
 for i,c in enumerate(piv):part[c]=a[i][-1]
 ker=[]
 for c in range(8):
  if c in piv:continue
  k=[0]*8;k[c]=1
  for i,b in enumerate(piv):k[b]=a[i][c]
  ker.append(k)
 return part,ker
def pick(sol,rng):
 out=sol[0][:]
 for b in sol[1]:
  c=rng.randrange(2);out=[(x+c*y)%2 for x,y in zip(out,b)]
 return out
def val(n):
 if not n:return 999
 n=abs(int(n));a=0
 while n%2==0:n//=2;a+=1
 return a
rng=random.Random(630);seeds=[list(x) for x in itertools.product(range(2),repeat=8) if all(y%2==0 for y in ff(x)) and any(x)]
print('seeds',len(seeds),flush=True)
attempts=0
for seed in seeds:
 for trial in range(300):
  x=seed[:];levels=1
  while levels<10:
   vals=ff(x);jac=jj(x);sol=solve_mod2(jac,[-f//2**levels for f in vals])
   if sol is None:break
   y=pick(sol,rng);x=[a+2**levels*b for a,b in zip(x,y)];levels+=1
   assert all(f%2**levels==0 for f in ff(x))
   if levels<3:continue
   attempts+=1
   best=999;bestcols=None;bestdet=None
   for cols in itertools.combinations(range(8),6):
    det=int(sy.Matrix([[row[c] for c in cols] for row in jj(x)]).det())
    b=val(det)
    if b<best:best,bestcols,bestdet=b,cols,det
    if 2*b<levels:break
   if levels>2*best:
    result={'denominator_depth':depth,'scaled_coordinates':x,'residuals':ff(x),'minor_columns':bestcols,'minor_determinant':str(bestdet),'residual_min_v2':min(map(val,ff(x))),'determinant_v2':best,'attempts':attempts}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit
 print('seed',seed,'attempts',attempts,flush=True)
print('No certificate found')
