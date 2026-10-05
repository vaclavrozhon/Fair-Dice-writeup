#!/usr/bin/env python3
"""Build an exact rational local-comparison model from an approximate real rule.

Numerical calculations only propose a starting rule. The final moment
identities and strict inequalities are certified in fractions arithmetic.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import argparse
import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import legvander, legval, legder


def legendre_array(x,m):
    P=[mp.mpf(1),x]
    for k in range(1,m):P.append(((2*k+1)*x*P[-1]-k*P[-2])/(k+1))
    return P[:m+1]


def numeric_rule(m,K,dps):
    t=(np.arange(K)+.5)/K
    derivatives=[legder(np.eye(m+1)[k]) for k in range(1,m+1)]
    for iteration in range(40):
        z=2*t-1
        residual=legvander(z,m)[:,1:].mean(axis=0)
        if np.max(np.abs(residual))<3e-16:break
        J=np.array([2*legval(z,c)/K for c in derivatives])
        step=J.T@np.linalg.solve(J@J.T,-residual)
        alpha=1.
        while alpha>1e-10:
            candidate=t+alpha*step
            if (candidate[0]>0 and candidate[-1]<1 and np.min(np.diff(candidate))>0
                and np.linalg.norm(legvander(2*candidate-1,m)[:,1:].mean(axis=0))<np.linalg.norm(residual)):
                t=candidate;break
            alpha/=2
        else:raise RuntimeError('Double precision proposal did not converge.')
    print(f'Proposed real rule: {iteration+1} Newton iterations, residual={np.max(np.abs(residual)):.3g}',flush=True)
    mp.mp.dps=dps
    u=[mp.mpf(repr(x)) for x in t]
    targets=sorted((1+np.cos((2*np.arange(m)+1)*np.pi/(2*m)))/2)
    pivots=[int(np.argmin(abs(t-x))) for x in targets]
    assert len(set(pivots))==m
    fixed=[mp.mpf(0)]*m
    for q,x in enumerate(u):
        if q not in pivots:
            P=legendre_array(2*x-1,m)
            for k in range(m):fixed[k]+=P[k+1]
    def func(*v):
        out=fixed[:]
        for x in v:
            P=legendre_array(2*x-1,m)
            for k in range(m):out[k]+=P[k+1]
        return mp.matrix(out)
    def jac(*v):
        out=mp.matrix(m,m)
        for j,x in enumerate(v):
            z=2*x-1;P=legendre_array(z,m)
            for k in range(1,m+1):out[k-1,j]=2*k*(z*P[k]-P[k-1])/(z*z-1)
        return out
    refined=mp.findroot(func,tuple(u[q] for q in pivots),J=jac,tol=mp.mpf(10)**(-dps+10),maxsteps=20)
    for q,x in zip(pivots,refined):u[q]=x
    assert 0<u[0]<u[-1]<1 and all(u[q]<u[q+1] for q in range(K-1))
    return u


def poly_from_roots(roots):
    a=[1]
    for root in roots:
        b=[0]*(len(a)+1)
        for k,v in enumerate(a):b[k]-=root*v;b[k+1]+=v
        a=b
    return a


def construct(m,K,digits,output):
    u=numeric_rule(m,K,digits+30)
    D=10**digits
    T=[int(mp.nint(x*D)) for x in u]
    t=[Q(x,D) for x in T]
    mu=[sum(x**s for x in t)/K for s in range(1,m+1)]
    aa=[(Q(1,s+1)-mu[s-1])/s for s in range(1,m+1)]
    b=[K*D**k*aa[k] for k in range(m)]
    groups=[list(range(j,m*m,m)) for j in range(m)]
    corrections=[]
    for j,group in enumerate(groups):
        fj={}
        for q in group:
            coeff=poly_from_roots([T[v] for v in group if v!=q])
            denominator=1
            for v in group:
                if v!=q:denominator*=T[q]-T[v]
            fj[q]=sum(Q(coeff[k])*b[k] for k in range(m))/denominator
        # These linear identities imply all 2^m squarefree mixed moments.
        for s in range(1,m+1):
            assert sum(fj[q]*t[q]**(s-1) for q in group)/K==aa[s-1]
        column=[t[q]+fj.get(q,Q(0)) for q in range(K)]
        assert 0<column[0] and column[-1]<1
        assert all(column[q]<column[q+1] for q in range(K-1))
        corrections.append(fj)
        print(f'Column {j+1}/{m}: exact moment correction and strict order certified',flush=True)
    obj={'m':m,'K':K,'denominator':str(D),'baseline_numerators':[str(x) for x in T],
         'corrections':[{str(q):str(v) for q,v in fj.items()} for fj in corrections]}
    Path(output).write_text(json.dumps(obj,separators=(',',':'))+'\n')
    print(f'Exact certificate saved: {output}; scalar rational quadrature lower bound={max(2**(m//2),3**(m//3))}, local K={K}',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--m',type=int,default=20)
    parser.add_argument('--digits',type=int,default=80)
    parser.add_argument('--output',default=str(Path(__file__).with_name('local_model_m20.json')))
    args=parser.parse_args()
    construct(args.m,args.m**2,args.digits,args.output)
