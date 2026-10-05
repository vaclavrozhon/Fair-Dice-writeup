"""Try to certify Q_3 solubility of the general five-row local tensor.

A certificate consists of an integer matrix Z with all scaled moment
residuals divisible by 27 and a Jacobian minor of valuation one.
Strong multivariate Hensel then gives an exact solution near Z/3.
This gives no rational point and no real monotonicity conclusion.
"""
import itertools,json,random
from pathlib import Path
import sympy as sy
base=Path(__file__).parent
subs=[s for k in range(1,5) for s in itertools.combinations(range(4),k)]
target=[15 if len(s)==2 else 81 if len(s)==4 else 0 for s in subs]
def values(z):return [sum(sy.prod(z[5*j+i] for j in s) for i in range(5)) for s in subs]
def jacobian(z):
 return [[sy.prod(z[5*k+(j%5)] for k in s if k!=j//5) if j//5 in s else 0 for j in range(20)] for s in subs]
def solve_mod3(mat,rhs):
 a=[[int(x)%3 for x in row]+[int(t)%3] for row,t in zip(mat,rhs)]
 r=0;piv=[]
 for c in range(20):
  hit=next((i for i in range(r,len(a)) if a[i][c]),None)
  if hit is None:continue
  a[r],a[hit]=a[hit],a[r]
  mul=pow(a[r][c],-1,3);a[r]=[x*mul%3 for x in a[r]]
  for i in range(len(a)):
   if i!=r and a[i][c]:
    mul=a[i][c];a[i]=[(x-mul*y)%3 for x,y in zip(a[i],a[r])]
  piv.append(c);r+=1
  if r==len(a):break
 if any(row[-1] for row in a[r:]):return None
 part=[0]*20
 for i,c in enumerate(piv):part[c]=a[i][-1]
 ker=[]
 for c in range(20):
  if c in piv:continue
  v=[0]*20;v[c]=1
  for i,b in enumerate(piv):v[b]=-a[i][c]%3
  ker.append(v)
 return part,ker,piv
def pick(sol,rng):
 p,k,_=sol;out=p[:]
 for v in k:
  c=rng.randrange(3);out=[(a+c*b)%3 for a,b in zip(out,v)]
 return out
def valuation(n):
 if n==0:return 999
 n=abs(int(n));a=0
 while n%3==0:n//=3;a+=1
 return a
rng=random.Random(20260930)
entries=json.loads((base/'local_mod_three.json').read_text())['lifts']
entries=[e for e in entries if e['depth']==1 and e['rank']==14]
rng.shuffle(entries)
attempt=0
for e in entries:
 z=sum(e['columns'],[]);j=jacobian(z);v=values(z)
 sol=solve_mod3(j,[(t-x)//3 for t,x in zip(target,v)])
 assert sol
 for trial in range(30):
  attempt+=1;y=pick(sol,rng);z9=[a+3*b for a,b in zip(z,y)]
  j9=jacobian(z9);v9=values(z9)
  assert all((t-x)%9==0 for t,x in zip(target,v9))
  s27=solve_mod3(j9,[(t-x)//9 for t,x in zip(target,v9)])
  if s27 is None:continue
  piv=s27[2]
  assert len(piv)==14
  minor=None
  for c in range(20):
   if c in piv:continue
   cols=piv+[c];det=sy.Matrix([[row[k] for k in cols] for row in j9]).det()
   if valuation(det)==1:minor=(cols,int(det));break
  if minor is None:continue
  y=pick(s27,rng);z27=[a+9*b for a,b in zip(z9,y)]
  residual=[int(x-t) for x,t in zip(values(z27),target)]
  assert min(map(valuation,residual))>=3
  cols=minor[0];det=int(sy.Matrix([[row[k] for k in cols] for row in jacobian(z27)]).det())
  assert valuation(det)==1
  result={'z':z27,'scaled_targets':target,'residuals':residual,'minor_columns':cols,'minor_determinant':str(det),'residual_min_v3':min(map(valuation,residual)),'determinant_v3':1,'attempts':attempt}
  (base/'general_q3_hensel_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps(result,indent=2));raise SystemExit
print('No certificate found; attempts',attempt)
