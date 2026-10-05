"""Build fixed-a elliptic compatibility curve and rational tangent point."""
from pathlib import Path
import sympy as s
import json
x,y,z=s.symbols('x y z')
a=s.Matrix([s.Rational(t) for t in ['-5/6','-19/50','1/150','19/50','62/75']])
powv=lambda v,k:v.applyfunc(lambda t:t**k)
M3=a.dot(powv(a,2))/5;M4=powv(a,2).dot(powv(a,2))/5
U=s.Matrix.vstack(s.ones(1,5),a.T,powv(a,2).T)
base=U.gauss_jordan_solve(s.Matrix([0,0,-5*M3]))[0]
params=sorted(set().union(*(t.free_symbols for t in base)),key=str)
u=base.subs(dict(zip(params,[x,y])))
rows=[s.ones(5,1),a,u,powv(a,2),s.matrix_multiply_elementwise(a,u),powv(a,3)+s.matrix_multiply_elementwise(powv(a,2),u)]
b=s.Matrix([0,0,0,-5*M3,5*M3,1-5*M4-powv(a,3).dot(u)])
A=s.Matrix.vstack(*(t.T for t in rows))
print('computing determinant',flush=True)
f=s.Poly(A.row_join(b).det(method='domain-ge'),x,y).clear_denoms()[1].primitive()[1].as_expr()
F=s.Poly(f,x,y).homogenize(z).as_expr()
print('u',list(u),'f',s.factor(f),'infinity',s.factor(F.subs(z,0)),flush=True)
out={'a':list(map(str,a)),'u':list(map(str,u)),'f':str(f),'infinity':str(s.factor(F.subs(z,0)))}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
