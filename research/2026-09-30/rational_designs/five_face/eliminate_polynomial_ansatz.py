import sympy as s
A,B=s.symbols('A B')
p=653184*A**3*B**3-23328*A**3*B**2+1296*A**3*B+3888*A**2*B**2-1944*A**2*B-180*A**2+288*A*B+60*A-5
q=7278336*A**4*B**3+3499200*A**4*B**2+427680*A**4*B+1399680*A**3*B**3-855360*A**3*B**2-259200*A**3*B-5400*A**3+45360*A**2*B**2+50760*A**2*B+2700*A**2-3240*A*B-450*A+25
r=s.factor(s.resultant(p,q,B));print(r,flush=True)
print('rational roots A',s.polys.polytools.ground_roots(r,A),flush=True)
