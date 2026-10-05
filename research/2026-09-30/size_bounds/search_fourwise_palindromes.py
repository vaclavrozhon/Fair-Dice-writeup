#!/usr/bin/env python3
"""Exact CP-SAT search for four-wise fair five-die palindrome block words."""
import itertools,math,json,sys
from fractions import Fraction as F
from pathlib import Path
from ortools.sat.python import cp_model

def count(word,pattern):
 d=[1]+[0]*len(pattern)
 for x in word:
  for j in range(len(pattern)-1,-1,-1):
   if pattern[j]==x:d[j+1]+=d[j]
 return d[-1]

m=int(sys.argv[1]) if len(sys.argv)>1 else 9
seconds=float(sys.argv[2]) if len(sys.argv)>2 else 300
perms=list(itertools.permutations(range(5)))
blocks=[p+p[::-1] for p in perms]
pats={k:list(itertools.permutations(range(5),k)) for k in (3,4)}
delta=[{p:F(count(w,p))-F(2**k,math.factorial(k)) for k in (3,4) for p in pats[k]} for w in blocks]
model=cp_model.CpModel()
x=[[model.new_bool_var(f'x{i}_{j}') for j in range(120)] for i in range(m)]
for row in x:model.add_exactly_one(row)
model.add(x[0][0]==1)
for p in pats[4]:
 terms=[]
 for i in range(m):
  for j,d in enumerate(delta):
   value=3*(d[p]+2*i*d[p[1:]]+2*(m-1-i)*d[p[:-1]])
   assert value.denominator==1
   if value:terms.append(int(value)*x[i][j])
 model.add(sum(terms)==0)
for t in itertools.combinations(range(5),3):
 for winner in t:
  model.add(sum(x[i][j] for i in range(m) for j,p in enumerate(perms) if next(z for z in p if z in t)==winner)==m//3)
solver=cp_model.CpSolver()
solver.parameters.max_time_in_seconds=seconds
solver.parameters.num_search_workers=2
solver.parameters.log_search_progress=True
status=solver.solve(model)
out={'blocks':m,'sides':2*m,'status':solver.status_name(status),'seconds':solver.wall_time}
if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
 ids=[next(j for j in range(120) if solver.value(x[i][j])) for i in range(m)]
 w=sum((blocks[j] for j in ids),())
 out.update(indices=ids,word=''.join(map(str,w)))
 for k in range(1,5):
  target=F((2*m)**k,math.factorial(k))
  assert all(count(w,p)==target for p in itertools.permutations(range(5),k))
 out['four_order_count']=str(F((2*m)**4,24))
Path(f'fourwise_palindrome_{m}_search.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2),flush=True)
