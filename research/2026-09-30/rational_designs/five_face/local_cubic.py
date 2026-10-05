"""Primitive projective residue lifting for the fixed-a cubic (exact integer)."""
from pathlib import Path
import json
import sympy as s
x,y,z=s.symbols('x y z')
data=json.loads(Path(__file__).with_name('cubic_curve.json').read_text())
f=s.Poly(s.sympify(data['f']),x,y).homogenize(z)
terms=[(tuple(m),int(c)) for m,c in f.terms()]
def val(t,mod):
 return sum(c*pow(t[0],e[0],mod)*pow(t[1],e[1],mod)*pow(t[2],e[2],mod) for e,c in terms)%mod
for p in (2,3,5,7,11,13,19,31):
 # Disjoint projective charts: x=1; x multiple p,y=1; x,y multiples p,z=1.
 total=0
 for pivot in range(3):
  free=[j for j in range(3) if j!=pivot]
  nodes=[]
  for a in range(p):
   for b in range(p):
    t=[0]*3;t[pivot]=1;t[free[0]]=a;t[free[1]]=b
    if any(t[j]%p for j in range(pivot)):continue
    if not val(t,p):nodes.append(tuple(t))
  mod=p
  stages=[len(nodes)]
  for k in range(2,9 if p<=3 else 5):
   if not nodes or len(nodes)*p*p>3_000_000:break
   nxt=[]
   for old in nodes:
    for a in range(p):
     for b in range(p):
      t=list(old);t[free[0]]+=mod*a;t[free[1]]+=mod*b
      if not val(t,mod*p):nxt.append(tuple(t))
   nodes=nxt;mod*=p;stages.append(len(nodes))
  print(p,pivot,stages,flush=True)
  total+=len(nodes)
 if not total:print('OBSTRUCTED',p,flush=True)
