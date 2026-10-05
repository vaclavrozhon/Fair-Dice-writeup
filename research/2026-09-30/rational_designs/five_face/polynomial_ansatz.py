"""New general four-column ansatz on five arithmetic row parameters."""
import sympy as s
from pathlib import Path
S,V,E,L=s.symbols('S V E L',nonzero=True)
x=s.Matrix([-2,-1,0,1,2]);one=s.ones(5,1)
powv=lambda a,k:a.applyfunc(lambda z:z**k)
dot=lambda a,b:a.dot(b)/5
h2=powv(x,2)-2*one
w=s.Matrix([1,-4,6,-4,1])
c=S*x;d=x/(6*S)+V*h2
M=s.Matrix.vstack(one.T,c.T,d.T,s.matrix_multiply_elementwise(c,d).T)
z0=M[:,:4].inv()*(s.Matrix([0,s.Rational(5,3),s.Rational(5,3),0])-M[:,4]*E)
z=s.Matrix(list(z0)+[E]).applyfunc(s.factor)
print('z',list(z),flush=True)
odd=s.factor(dot(powv(z,2),x))
e=s.solve(odd,E)[0]
print('E',s.factor(e),flush=True)
z=z.subs(E,e).applyfunc(s.factor)
lam=s.factor(dot(powv(z,2),h2)/dot(powv(w,2),h2))
f=s.factor(dot(powv(z,2),one)-lam*dot(powv(w,2),one)-s.Rational(1,3))
g=s.factor(dot(powv(z,2)-lam*powv(w,2),s.matrix_multiply_elementwise(c,d))-s.Rational(1,5))
print('lambda²',lam,'pair',f,'fourth',g,flush=True)
Path(__file__).with_suffix('.txt').write_text(f'z={list(z)}\nlambda²={lam}\npair={f}\nfourth={g}\n')
