#!/usr/bin/env python3
"""Symmetric rational degree-seven equal-weight quadrature search.
Nodes are (D+-s)/(2D), with integer multiplicities, and one centre for odd K.
Every found rule is checked using exact Fractions for all degrees 0..7.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from pathlib import Path
import json,sys
from ortools.sat.python import cp_model
K=int(sys.argv[1]) if len(sys.argv)>1 else 69
D=int(sys.argv[2]) if len(sys.argv)>2 else 420
limit=float(sys.argv[3]) if len(sys.argv)>3 else 600
assert K%2 and D%8==4

def christoffel(x):
 t=2*x-1
 leg=[F(1),t]
 for j in range(2,4):leg.append(((2*j-1)*t*leg[-1]-(j-1)*leg[-2])/j)
 return sum((2*j+1)*p*p for j,p in enumerate(leg))
model=cp_model.CpModel()
xs=[]
ubs=[]
for s in range(D+1):
 ub=min((K-1)//2,int(F(K)/christoffel(F(D+s,2*D))))
 if s==0:ub=(ub-1)//2
 if s%2==0:ub=min(ub,(K-65)//2)
 ubs.append(ub)
 xs.append(model.new_int_var(0,ub,f'c{s}'))
model.add(sum(xs)==(K-1)//2)
model.add(sum(xs[s] for s in range(1,D+1,2))==32)
targets=[]
for j in range(1,4):
 target=F(K*D**(2*j),2*(2*j+1))
 assert target.denominator==1,(j,target)
 target=int(target)
 coefs=[s**(2*j) for s in range(D+1)]
 g=reduce(gcd,coefs+[target]);target//=g;coefs=[c//g for c in coefs]
 assert sum(c*u for c,u in zip(coefs,ubs))<2**62
 model.add(sum(c*x for c,x in zip(coefs,xs))==target)
 targets.append(target)
solver=cp_model.CpSolver()
solver.parameters.max_time_in_seconds=limit
solver.parameters.num_search_workers=2
solver.parameters.log_search_progress=True
status=solver.solve(model)
out={'K':K,'D':D,'status':solver.status_name(status),'seconds':solver.wall_time,'targets':targets}
if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
 counts={s:solver.value(x) for s,x in enumerate(xs) if solver.value(x)}
 out['magnitude_counts']=counts
 nodes=[F(1,2)]
 for s,c in counts.items():nodes.extend([F(D+s,2*D),F(D-s,2*D)]*c)
 assert len(nodes)==K
 moments=[sum(x**j for x in nodes)/K for j in range(8)]
 assert moments==[F(1,j+1) for j in range(8)]
 out['moments']=[str(v) for v in moments]
Path(f'degree7_symmetric_K{K}_D{D}.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2),flush=True)
