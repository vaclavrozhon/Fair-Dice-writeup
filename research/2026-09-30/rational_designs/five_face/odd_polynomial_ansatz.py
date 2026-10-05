"""General local model with one linear and one odd-cubic column on five rows."""
import sympy as s
from pathlib import Path
S,V=s.symbols('S V',nonzero=True)
x=s.Matrix([-2,-1,0,1,2]);one=s.ones(5,1)
powv=lambda a,k:a.applyfunc(lambda z:z**k)
dot=lambda a,b:a.dot(b)/5
c=S*x;T=s.factor((s.Rational(1,3)/S-V*dot(x,powv(x,3)))/dot(x,x));d=T*x+V*powv(x,3)
AA,BB=s.symbols('AA BB');zo=AA*x+BB*powv(x,3)
sol=s.solve([dot(zo,c)-s.Rational(1,3),dot(zo,d)-s.Rational(1,3)],[AA,BB]);zo=zo.subs(sol).applyfunc(s.factor)
cd=s.matrix_multiply_elementwise(c,d)
null=s.Matrix.vstack(one.T,c.T,d.T,cd.T).nullspace()[0].applyfunc(s.factor)
L=s.factor((dot(powv(zo,2),one)-s.Rational(1,3))/dot(powv(null,2),one))
f=s.factor(dot(powv(zo,2)-L*powv(null,2),cd)-s.Rational(1,5))
print('c',list(c),'d',list(d),'zo',list(zo),'w',list(null),flush=True)
print('L',L,'fourth',f,flush=True)
Path(__file__).with_suffix('.txt').write_text(f'zo={list(zo)}\nw={list(null)}\nL={L}\nfourth={f}\n')
