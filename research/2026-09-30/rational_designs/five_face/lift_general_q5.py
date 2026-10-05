"""Try to certify Q5 solubility without negative coordinate valuations."""
import itertools,json,random
from pathlib import Path
import sympy as sy
prime=5;base=Path(__file__).parent
subs=[s for k in range(1,5) for s in itertools.combinations(range(4),k)]
target=[5 if len(s)==2 else 3 if len(s)==4 else 0 for s in subs]
def values(z):return [3*sum(sy.prod(z[5*j+i] for j in s) for i in range(5))-t for s,t in zip(subs,target)]
def jacobian(z):return [[3*sy.prod(z[5*k+(j%5)] for k in s if k!=j//5) if j//5 in s else 0 for j in range(20)] for s in subs]
def solve(mat,rhs):
 a=[[int(x)%prime for x in row]+[int(t)%prime] for row,t in zip(mat,rhs)];r=0;piv=[]
 for c in range(20):
  hit=next((i for i in range(r,15) if a[i][c]),None)
  if hit is None:continue
  a[r],a[hit]=a[hit],a[r];mul=pow(a[r][c],-1,prime);a[r]=[x*mul%prime for x in a[r]]
  for i in range(15):
   if i!=r and a[i][c]:
    mul=a[i][c];a[i]=[(x-mul*y)%prime for x,y in zip(a[i],a[r])]
  piv.append(c);r+=1
  if r==15:break
 if any(row[-1] for row in a[r:]):return None
 part=[0]*20
 for i,c in enumerate(piv):part[c]=a[i][-1]
 ker=[]
 for c in range(20):
  if c in piv:continue
  v=[0]*20;v[c]=1
  for i,b in enumerate(piv):v[b]=-a[i][c]%prime
  ker.append(v)
 return part,ker,piv
def pick(sol,rng):
 p,k,_=sol;out=p[:]
 for v in k:
  c=rng.randrange(prime);out=[(a+c*b)%prime for a,b in zip(out,v)]
 return out
def valuation(n):
 n=sy.Rational(n)
 if n==0:return 999
 a,b=abs(int(n.p)),int(n.q);v=0
 while a%prime==0:a//=prime;v+=1
 while b%prime==0:b//=prime;v-=1
 return v
rng=random.Random(501)
counts=[0,0,0]
for attempt in range(10000):
 alpha=[rng.randrange(1,5) for _ in range(3)];alpha.append(-pow(sy.prod(alpha),-1,5)%5)
 beta=[rng.randrange(5) for _ in range(4)]
 z=[int((a*t+b)%5) for a,b in zip(alpha,beta) for t in range(5)]
 vals=values(z);assert all(x%5==0 for x in vals)
 s25=solve(jacobian(z),[-x//5 for x in vals]);counts[0]+=1
 if s25 is None:continue
 counts[1]+=1
 for trial in range(50):
  y=pick(s25,rng);z25=[a+5*b for a,b in zip(z,y)];vals=values(z25)
  s125=solve(jacobian(z25),[-x//25 for x in vals])
  if s125 is None:continue
  counts[2]+=1
  y=pick(s125,rng);z125=[a+25*b for a,b in zip(z25,y)]
  jac=jacobian(z125);piv=s125[2];free=[c for c in range(20) if c not in piv]
  for extra in itertools.combinations(free,15-len(piv)):
   cols=piv+list(extra);mat=sy.Matrix([[row[k] for k in cols] for row in jac]);det=mat.det()
   if not det:continue
   inv=mat.inv();inverse_min=min(valuation(x) for x in inv)
   if inverse_min>=-1:
    residual=list(map(int,values(z125)));assert min(map(valuation,residual))>=3
    result={'z':z125,'polynomial_multiplier':3,'targets':target,'residuals':residual,'minor_columns':cols,'minor_determinant':str(det),'inverse_min_v5':inverse_min,'residual_min_v5':min(map(valuation,residual)),'counts':counts}
    (base/'general_q5_hensel_certificate.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit
 if attempt%10==0:print('counts',counts,flush=True)
print('No certificate',counts)
