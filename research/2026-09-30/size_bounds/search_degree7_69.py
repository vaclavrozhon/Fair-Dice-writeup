#!/usr/bin/env python3
"""CP-SAT search for a 69-node rational degree-seven interval rule.
Run using /tmp/fair-dice-cpsat-venv/bin/python. This is a bounded search,
not a claimed existence or infeasibility certificate unless status says so.
"""
from fractions import Fraction
from math import factorial
import json,sys,time
from ortools.sat.python import cp_model

D=int(sys.argv[1]) if len(sys.argv)>1 else 840
K=69
limit=float(sys.argv[2]) if len(sys.argv)>2 else 300
assert D%8==0
C=D//2


def choose_int(z,j):
    a=1
    for h in range(j):a*=z-h
    return a//factorial(j)


def christoffel(x):
    t=2*x-1
    leg=[Fraction(1),t]
    for j in range(2,4):leg.append(((2*j-1)*t*leg[-1]-(j-1)*leg[-2])/j)
    return sum((2*j+1)*p*p for j,p in enumerate(leg))

# The parity filter forces exactly64 odd normalized coordinates and5 even ones.
indices=list(range(D+1))
model=cp_model.CpModel()
counts=[]
upper_bounds=[]
for i in indices:
    ub=min(K,int(Fraction(K)/christoffel(Fraction(i,D))))
    if i%2==0:ub=min(ub,5)
    counts.append(model.new_int_var(0,ub,f'c{i}'))
    upper_bounds.append(ub)
model.add(sum(c for i,c in zip(indices,counts) if i%2)==64)
model.add(sum(c for i,c in zip(indices,counts) if i%2==0)==5)
# Reflection lets us choose the even-node centroid in the left half.
model.add(sum(i*c for i,c in zip(indices,counts) if i%2==0)<=5*C)
poly=[Fraction(1)]
targets=[]
for j in range(8):
    target=K*sum(c/Fraction(i+1) for i,c in enumerate(poly))
    assert target.denominator==1,(j,target)
    target=int(target)
    targets.append(target)
    coefs=[choose_int(i-C,j) for i in indices]
    assert sum(abs(a)*ub for a,ub in zip(coefs,upper_bounds))<2**62
    model.add(sum(a*c for a,c in zip(coefs,counts))==target)
    nxt=[Fraction(0)]*(len(poly)+1)
    for i,c in enumerate(poly):
        nxt[i]-=(C+j)*c/(j+1)
        nxt[i+1]+=D*c/(j+1)
    poly=nxt
solver=cp_model.CpSolver()
solver.parameters.max_time_in_seconds=limit
solver.parameters.num_search_workers=2
solver.parameters.log_search_progress=True
status=solver.solve(model)
out={'D':D,'K':K,'status':solver.status_name(status),'seconds':solver.wall_time,'targets':targets}
if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
    out['counts']={str(i):solver.value(c) for i,c in zip(indices,counts) if solver.value(c)}
    xs=[Fraction(i,D) for i,c in zip(indices,counts) for _ in range(solver.value(c))]
    assert len(xs)==K
    out['moments']=[str(sum(x**j for x in xs)/K) for j in range(8)]
    assert out['moments']==[str(Fraction(1,j+1)) for j in range(8)]
with open(f'degree7_69_grid{D}_search.json','w') as f:json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
