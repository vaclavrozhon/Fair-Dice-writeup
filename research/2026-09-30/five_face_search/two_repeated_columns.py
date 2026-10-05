"""Exact local-tensor equations for four old dice and five distinguished faces.
Two old comparison columns agree. This is only a necessary local model,
not a finite-dice construction.
"""
import sympy as s
from pathlib import Path
x,y=s.symbols('x y')
a=s.Matrix([s.Rational(z,6) for z in [-5,-3,1,3,4]])
ones=s.ones(5,1)
powv=lambda v,k:v.applyfunc(lambda t:t**k)
dot=lambda u,v:(u.dot(v))/5
M3=dot(powv(a,2),a);M4=dot(powv(a,2),powv(a,2))
U=s.Matrix.vstack(ones.T,a.T,powv(a,2).T)
base=U.gauss_jordan_solve(s.Matrix([0,0,-5*M3]))[0]
params=sorted(set().union(*(t.free_symbols for t in base)),key=str)
u=base.subs(dict(zip(params,[x,y])))
rows=[ones,a,u,powv(a,2),s.matrix_multiply_elementwise(a,u),powv(a,3)+s.matrix_multiply_elementwise(powv(a,2),u)]
rhs=[0,0,0,-5*M3,5*M3,1-5*M4-5*dot(powv(a,3),u)]
A=s.Matrix.vstack(*(z.T for z in rows))
b=s.Matrix(rhs)
pol=s.factor(A.row_join(b).det())
print('a=',list(a),'u=',list(u),'M3=',M3,flush=True)
print('compatibility=',pol,flush=True)
Path(__file__).with_suffix('.txt').write_text(f'a={list(a)}\nu={list(u)}\nM3={M3}\ncompatibility={pol}\n')
