"""Search rational baseline parameter k with a rational infinity anchor.
Modular filters are only exclusions; every survivor is factored exactly.
"""
from pathlib import Path
import json,math
import sympy as s
k,x,y=s.symbols('k x y')
data=json.loads(Path(__file__).with_name('baseline_family.json').read_text())
F=s.Poly(s.sympify(data['numerator']),x,y)
cs=[s.Poly(F.coeff_monomial(x**(3-j)*y**j),k) for j in range(4)]
coef=[[int(c.nth(i)) for i in range(17)] for c in cs]
def evalpoly(a,t,p):
 v=0
 for z in reversed(a):v=(v*t+z)%p
 return v
filters=[]
for p in list(s.primerange(5,151)):
 good=[]
 for r in range(p):
  vals=[evalpoly(a,r,p) for a in coef]
  good.append(vals[0]==0 or any((vals[0]*t**3+vals[1]*t*t+vals[2]*t+vals[3])%p==0 for t in range(p)))
 inf=[a[16]%p for a in coef]
 goodinf=inf[0]==0 or any((inf[0]*t**3+inf[1]*t*t+inf[2]*t+inf[3])%p==0 for t in range(p))
 filters.append((p,good,goodinf))
filters.sort(key=lambda z:sum(z[1])/z[0])
print('filter densities',[(p,round(sum(g)/p,2)) for p,g,_ in filters[:10]],flush=True)
seen=0;survivors=[];anchors=[]
for q in range(1,5001):
 for pp in range(math.ceil(-.82*q),math.floor(-.70*q)+1):
  if math.gcd(pp,q)!=1:continue
  seen+=1
  okay=True
  for p,g,ginf in filters:
   if q%p:
    if not g[(pp*pow(q,-1,p))%p]:okay=False;break
   elif not ginf:okay=False;break
  if not okay:continue
  rat=s.Rational(pp,q);survivors.append(str(rat))
  cubic=sum(c.eval(rat)*x**(3-j) for j,c in enumerate(cs))
  fac=s.factor_list(cubic)[1]
  linear=[str(f) for f,e in fac if s.degree(f,x)==1]
  print('survivor',rat,'factor degrees',[s.degree(f,x) for f,e in fac],flush=True)
  if linear:anchors.append({'k':str(rat),'linear':linear});print('ANCHOR',anchors[-1],flush=True)
 if q%500==0:print('q',q,'seen',seen,'survivors',len(survivors),'anchors',len(anchors),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'seen':seen,'survivors':survivors,'anchors':anchors},indent=2)+'\n')
