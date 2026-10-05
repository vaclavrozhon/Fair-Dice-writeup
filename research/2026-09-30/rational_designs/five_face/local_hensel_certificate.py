"""Find sufficient p-adic nonsingular local-point certificates for the cubic."""
from pathlib import Path
import json
import sympy as s
x,y,z=s.symbols('x y z')
data=json.loads(Path(__file__).with_name('cubic_curve.json').read_text())
f=s.Poly(s.sympify(data['f']),x,y).homogenize(z)
terms=[(tuple(m),int(c)) for m,c in f.terms()]
def value(ts,t):return sum(c*t[0]**e[0]*t[1]**e[1]*t[2]**e[2] for e,c in ts)
def vp(v,p):
 if not v:return 10000
 k=0
 while v%p==0:v//=p;k+=1
 return k
derivs=[]
for j in range(3):
 row=[]
 for e,c in terms:
  if e[j]:
   ee=list(e);ee[j]-=1;row.append((tuple(ee),c*e[j]))
 derivs.append(row)
records=[]
for p in [2,3,5,7,11,13,19,31]:
 found=None
 for pivot in range(3):
  free=[j for j in range(3) if j!=pivot]
  nodes=[]
  for a in range(p):
   for b in range(p):
    t=[0]*3;t[pivot]=1;t[free[0]]=a;t[free[1]]=b
    if any(t[j]%p for j in range(pivot)):continue
    if value(terms,t)%p==0:nodes.append(tuple(t))
  mod=p
  for k in range(1,15):
   for pt in nodes:
    j=min(free,key=lambda jj:vp(value(derivs[jj],pt),p))
    v=vp(value(derivs[j],pt),p)
    if k>2*v:
     found={'p':p,'point':pt,'modulus_power':k,'free_coordinate':j,'derivative_valuation':v,'value_valuation':vp(value(terms,pt),p)};break
   if found or not nodes:break
   nxt=[]
   # Keeping a subset preserves validity of successful Hensel certificates.
   if len(nodes)>20000:nodes=nodes[:20000]
   for old in nodes:
    for a in range(p):
     for b in range(p):
      t=list(old);t[free[0]]+=mod*a;t[free[1]]+=mod*b
      if value(terms,t)%(mod*p)==0:nxt.append(tuple(t))
   nodes=nxt;mod*=p
  if found:break
 print(found or ('NO CERT',p),flush=True)
 if found:records.append(found)
Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2)+'\n')
