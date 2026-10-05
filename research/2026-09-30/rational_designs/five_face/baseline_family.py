"""New one-parameter baseline conic; infinity-point incidence curve."""
from pathlib import Path
import sympy as s
import json
k,x,y,c,d,z=s.symbols('k x y c d z')
b=s.Rational(2,3)-(k+s.Rational(1,2))/(k*k+1)
t=s.Rational(1,2)-k*(k+s.Rational(1,2))/(k*k+1)
a=s.Matrix([-s.Rational(5,6),-t,s.Rational(5,6)-b,t,b])
a=a.applyfunc(s.factor)
print('baseline',list(a),flush=True)
U=s.Matrix.vstack(s.ones(1,5),a.T,a.applyfunc(lambda v:v*v).T)
u=s.Matrix(list(U[:,:3].inv()*(s.Matrix([0,0,-sum(v**3 for v in a)])-U[:,3:]*s.Matrix([x,y])))+[x,y]).applyfunc(s.factor)
v=u.subs({x:c,y:d})
eq=[u.dot(v),sum(a[i]*u[i]*v[i] for i in range(5))-sum(w**3 for w in a),sum(a[i]**3*(u[i]+v[i])+a[i]**2*u[i]*v[i] for i in range(5))-(1-sum(w**4 for w in a))]
rows=[]
for e in eq:
 e=s.Poly(s.cancel(e),c,d)
 row=[e.coeff_monomial(c),e.coeff_monomial(d),e.coeff_monomial(1)]
 rows.append([s.factor(q) for q in row])
print('matrix formed',flush=True)
M=s.Matrix(rows)
# Leading cubic comes from taking the degree-one part of every matrix entry.
L=M.applyfunc(lambda q:s.Poly(q,x,y).coeff_monomial(x)*x+s.Poly(q,x,y).coeff_monomial(y)*y)
F=s.factor(L.det(method='domain-ge'))
print('infinity',F,flush=True)
P=s.Poly(s.fraction(F)[0],k,x,y).primitive()[1].as_expr()
Path(__file__).with_suffix('.json').write_text(json.dumps({'a':list(map(str,a)),'u':list(map(str,u)),'infinity':str(F),'numerator':str(P)},indent=2)+'\n')
