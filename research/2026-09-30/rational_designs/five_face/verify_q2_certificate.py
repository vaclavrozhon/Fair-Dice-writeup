"""Exact symbolic and integer verification of the Q2 local certificate."""
import itertools,json
from pathlib import Path
import sympy as sy
C,lam=sy.symbols('C lam');r=sy.Rational(3,4);s=sy.Rational(1,4)
p=C/16;q=sy.Rational(5,6)-p;R=p/r;S=q/s
D=r*r*q-s*s*p;z1=sy.Rational(5,6)*r*(q-s*s)/D;z2=sy.Rational(5,6)*s*(r*r-p)/D
z=sy.Matrix([-z1,-z2,0,z2,z1]);u=sy.Matrix([q,-p,2*(p-q),-p,q])
cols=[z+lam*u,z-lam*u,sy.Matrix([-r,-s,0,s,r]),sy.Matrix([-R,-S,0,S,R])]
L=64*(C*C-24*C+148)/(3*(C-12)**2*(3*C*C-40*C+160))
f=36*C**5-1647*C**4+29612*C**3-264376*C**2+1193920*C-2229120
report=[]
for k in range(1,5):
 for subset in itertools.combinations(range(4),k):
  moment=sy.expand(sum(sy.prod(cols[j][i] for j in subset) for i in range(5))/5)
  diff=sy.factor(moment.subs(lam**2,L)-(0 if k%2 else sy.Rational(1,k+1)))
  if k<4:assert diff==0
  else:
   num,den=sy.fraction(diff);assert sy.rem(num,f,C)==0
  report.append({'subset':subset,'residual':str(diff)})
def val(q):
 q=sy.Rational(q)
 if not q:return 999
 a,b=abs(int(q.p)),int(q.q)
 return (a&-a).bit_length()-(b&-b).bit_length()
c=2179188;P,Q=sy.fraction(L);unit=sy.Rational(4*L.subs(C,c));unit_mod8=int(unit.p)*pow(int(unit.q),-1,8)%8
stats={'c0':c,'f_v2':val(f.subs(C,c)),'derivative_v2':val(sy.diff(f,C).subs(C,c)),'P_v2':val(P.subs(C,c)),'Q_v2':val(Q.subs(C,c)),'four_L_mod8':unit_mod8}
assert stats=={'c0':2179188,'f_v2':28,'derivative_v2':6,'P_v2':8,'Q_v2':10,'four_L_mod8':1}
Path(__file__).with_suffix('.json').write_text(json.dumps({'statistics':stats,'moment_checks':report},indent=2)+'\n')
print(json.dumps(stats));print('All fifteen symbolic moments verified modulo f(C).')
