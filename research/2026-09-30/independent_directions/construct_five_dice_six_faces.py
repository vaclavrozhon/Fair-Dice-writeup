"""Exact LP construction: three uniform dice, one rational density, six-face D.

All twenty relative positions of D and the density die are checked as
rational integrals.  The other three dice are continuous uniform variables;
the standard cellwise finiteization converts the result to finite dice.
"""
import json
from math import factorial,sqrt
from pathlib import Path
import numpy as np
import sympy as S
from scipy.optimize import linprog

x=S.symbols('x');K=6
# A rational point on the unit sphere near a real six-node degree-five rule.
base=S.Matrix([S.Rational(2,7),S.Rational(3,7),S.Rational(6,7)])
disc=sqrt(401/1280)
real=[.25,sqrt((15/16-disc)/2),sqrt((15/16+disc)/2)]
den=10**7
delta=S.Matrix([S.Rational(round(float(base[i]-real[i])*den),den) for i in range(3)])
positive=base-2*base.dot(delta)/delta.dot(delta)*delta
assert positive.dot(positive)==1
nodes=sorted([(1+sgn*t)/2 for sgn in (-1,1) for t in positive])
print('nodes',list(map(float,nodes)),'fourth error',float(sum(t**4 for t in positive)/3-S.Rational(1,5)),flush=True)
comps=[(a,b,3-a-b) for a in range(4) for b in range(4-a)]
for refinement in (4,6):
    coarse=[S.Rational(0)]+nodes+[S.Rational(1)]
    endpoints=[l+(r-l)*j/refinement for l,r in zip(coarse,coarse[1:]) for j in range(refinement)]+[S.Rational(1)]
    rows=[]
    for side in ('D<E','E<D'):
      for a,b,c in comps:
        row=[]
        for l,r in zip(endpoints,endpoints[1:]):
            mid=(l+r)/2;terms=[]
            for t in nodes:
                if side=='D<E' and mid>t:terms.append(t**a*(x-t)**b*(1-x)**c)
                elif side=='E<D' and mid<t:terms.append(x**a*(t-x)**b*(1-t)**c)
            poly=S.Poly(sum(terms),x).integrate()
            row.append((poly.eval(r)-poly.eval(l))/(K*factorial(a)*factorial(b)*factorial(c)))
        rows.append(row)
    A=S.Matrix(rows);rhs=S.ones(20,1)/120
    piv=A.T.rref()[1];Ar=A[list(piv),:];br=rhs[list(piv),:]
    if A.row_join(rhs).rank()>len(piv):
        print('refinement',refinement,'inconsistent rank',len(piv),flush=True);continue
    print('refinement',refinement,'cells',A.cols,'rank',len(piv),flush=True)
    # First try the exact minimum Euclidean correction to constant density.
    one=S.ones(A.cols,1)
    gamma=one+Ar.T*(Ar*Ar.T).inv()*(br-Ar*one)
    print('minimum-norm density min',float(min(gamma)),flush=True)
    if min(gamma)<=0:
        # Positive LP with a common margin, followed by exact basis recovery.
        Af=np.array(Ar).astype(float);bf=np.array(br).astype(float).ravel()
        obj=np.zeros(A.cols+1);obj[-1]=-1
        eq=np.c_[Af,np.zeros(len(piv))]
        ub=np.c_[-np.eye(A.cols),np.ones(A.cols)]
        result=linprog(obj,A_ub=ub,b_ub=np.zeros(A.cols),A_eq=eq,b_eq=bf,bounds=[(0,None)]*A.cols+[(0,1)],method='highs')
        print('LP',result.message,'margin',None if not result.success else result.x[-1],flush=True)
        if not result.success or result.x[-1]<1e-6:continue
        # Fix a rational baseline strictly below the LP margin; solve on an
        # exact column basis using the LP values as rational approximants.
        cpiv=Ar.rref()[1];free=[i for i in range(A.cols) if i not in cpiv]
        gf=S.Matrix([S.Rational(float(result.x[i])).limit_denominator(10**7) for i in free])
        gp=Ar[:,list(cpiv)].inv()*(br-Ar[:,free]*gf)
        gamma=S.zeros(A.cols,1)
        for i,val in zip(free,gf):gamma[i]=val
        for i,val in zip(cpiv,gp):gamma[i]=val
    assert A*gamma==rhs
    if min(gamma)<=0:
        print('exact recovered density not positive',float(min(gamma)),flush=True);continue
    assert sum(gamma[i]*(endpoints[i+1]-endpoints[i]) for i in range(A.cols))==1
    obj={'distinguished_nodes':[str(t) for t in nodes],
         'interval_endpoints':[str(t) for t in endpoints],
         'density':[str(t) for t in gamma],
         'comparison_dice':'three independent uniform[0,1] variables and one die with the given density',
         'verified_order_types':20,'order_probability':'1/120'}
    Path('five_dice_six_face_density_certificate.json').write_text(json.dumps(obj,indent=2))
    print('CERTIFIED','min',float(min(gamma)),'max',float(max(gamma)),
          'max denominator bits',max(int(S.denom(v)).bit_length() for v in gamma),flush=True)
    break
