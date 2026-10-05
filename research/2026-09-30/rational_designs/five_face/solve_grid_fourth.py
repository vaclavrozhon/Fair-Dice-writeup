"""Finish modularly screened three-column grid candidates over Q."""
from pathlib import Path
import itertools,json
import numpy as np
import sympy as sy
from scipy.optimize import linprog
base=Path(__file__).parent
count=consistent=0;results=[]
for path in sorted(base.glob('general_grid_three_D*.jsonl')):
 for line in path.read_text().splitlines():
  data=json.loads(line);D=data['D'];a,b,c=[sy.Matrix(v) for v in data['columns']]
  rows=[[1]*5,list(a),list(b),list(c),[a[i]*b[i] for i in range(5)],[a[i]*c[i] for i in range(5)],[b[i]*c[i] for i in range(5)],[a[i]*b[i]*c[i] for i in range(5)]]
  mat=sy.Matrix(rows);target=sy.Matrix([0,5*D//3,5*D//3,5*D//3,0,0,0,D**3]);count+=1
  sols=sy.linsolve((mat,target))
  if sols==sy.EmptySet:continue
  consistent+=1;v=next(iter(sols));free=sorted(set().union(*(x.free_symbols for x in v)),key=str)
  if free:
   # Maximize the common monotonicity and interval gap in the affine family.
   gap=sy.Symbol('gap');exprs=[v[i+1]-v[i]-gap for i in range(4)]+[v[0]+1-gap,1-v[4]-gap]
   pars=free+[gap];AA=[];bb=[]
   for ex in exprs:
    AA.append([-float(ex.coeff(q)) for q in pars]);bb.append(float(ex.subs({q:0 for q in pars})))
   opt=linprog([0]*len(free)+[-1],A_ub=AA,b_ub=bb,bounds=[(None,None)]*len(pars),method='highs')
   if not opt.success or opt.x[-1]<-1e-9:continue
   sub={q:sy.Rational(float(x)).limit_denominator(10**7) for q,x in zip(free,opt.x)}
   v=tuple(sy.factor(x.subs(sub)) for x in v)
  monotone=all(v[i]<=v[i+1] for i in range(4)) and v[0]>=-1 and v[4]<=1
  entry={'D':D,'first_three':data['columns'],'fourth':list(map(str,v)),'monotone':monotone,'rank':mat.rank()};results.append(entry)
  print(json.dumps(entry),flush=True)
  if monotone:
   cols=[a/D,b/D,c/D,sy.Matrix(v)]
   for k in range(1,5):
    for ss in itertools.combinations(range(4),k):assert sum(sy.prod(cols[j][i] for j in ss) for i in range(5))/5==(0 if k%2 else sy.Rational(1,k+1))
out={'modular_survivors':count,'rationally_consistent':consistent,'results':results}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('COUNTS',count,consistent,len(results))
