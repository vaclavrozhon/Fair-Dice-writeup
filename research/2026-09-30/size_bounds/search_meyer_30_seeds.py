#!/usr/bin/env python3
"""Generate exact four-die M30 words and seek a fifth comparison distribution."""
from fractions import Fraction as F
from pathlib import Path
import itertools,json,sys,random
import numpy as np
from scipy.optimize import linprog
from ortools.sat.python import cp_model
from insert_fifth_into_30 import system
m=15;n=4
perms=list(itertools.permutations(range(n)))
blocks=[p+p[::-1] for p in perms]
def count(w,p):
 d=[1]+[0]*len(p)
 for x in w:
  for j in range(len(p)-1,-1,-1):
   if p[j]==x:d[j+1]+=d[j]
 return d[-1]
ds=[{p:3*count(w,p)-(4 if k==3 else 2) for k in (3,4) for p in itertools.permutations(range(n),k)} for w in blocks]
model=cp_model.CpModel()
x=[[model.new_bool_var(f'x{i}_{j}') for j in range(24)] for i in range(m)]
for row in x:model.add_exactly_one(row)
model.add(x[0][0]==1)
for p in perms:
 model.add(sum((d[p]+2*i*d[p[1:]]+2*(m-1-i)*d[p[:-1]])*x[i][j] for i in range(m) for j,d in enumerate(ds))==0)
for t in itertools.combinations(range(n),3):
 for winner in t:model.add(sum(x[i][j] for i in range(m) for j,p in enumerate(perms) if next(z for z in p if z in t)==winner)==5)
known=json.loads(Path('../equal_size/meyer_2023_five_dice_sixty.json').read_text())['word']
known=tuple(ord(a)-98 for a in known if a!='a')
targets=[]
for start in (0,120):
 half=known[start:start+120];inv={v:i for i,v in enumerate(half[:4])}
 targets.append([perms.index(tuple(inv[v] for v in half[8*i:8*i+4])) for i in range(15)])
logpath=Path('meyer_30_seeds_search.jsonl')
for seed in range(int(sys.argv[1]) if len(sys.argv)>1 else 100):
 rng=random.Random(seed)
 target=targets[seed%2]
 model.minimize(sum((10000*(j!=target[i])+rng.randint(-1000,1000))*v for i,row in enumerate(x) for j,v in enumerate(row)))
 solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=3;solver.parameters.num_search_workers=1;solver.parameters.random_seed=seed
 status=solver.solve(model)
 out={'seed':seed,'cp_status':solver.status_name(status)}
 if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
  ids=[next(j for j in range(24) if solver.value(x[i][j])) for i in range(m)]
  w=sum((blocks[j] for j in ids),())
  assert all(count(w,p)==33750 for p in perms)
  A=system(w)
  r=linprog(np.zeros(len(w)+1),A_eq=A.astype(float)/810000,b_eq=np.ones(120)/120,bounds=(0,None),method='highs')
  out.update(indices=ids,word=''.join(map(str,w)),insertion_lp_status=r.message,changed_blocks=sum(a!=b for a,b in zip(ids,target)))
  model.add(sum(x[i][j] for i,j in enumerate(ids))<=m-1)
  if r.success:
   out['weights']=r.x.tolist()
   Path('meyer_30_seed_feasible.json').write_text(json.dumps(out,indent=2)+'\n')
   print('FOUND LP FEASIBLE',json.dumps(out),flush=True)
   break
  else:
   # Keep a compact exact integral Farkas certificate.
   dual=linprog(np.ones(120),A_ub=-A.T.astype(float)/810000,b_ub=np.zeros(121),bounds=[(-1,1)]*120,method='highs')
   assert dual.success and dual.fun<0
   scale=100
   while True:
    y=[int(np.ceil(scale*v))+1 for v in dual.x]
    products=[sum(a*int(b) for a,b in zip(y,col)) for col in A.T]
    if min(products)>=0 and sum(y)<0:break
    scale*=10
   out.update(farkas=y,minimum_column=min(products),target_pairing=sum(y))
 with logpath.open('a') as f:f.write(json.dumps(out)+'\n')
 print(seed,out['cp_status'],out.get('insertion_lp_status',''),flush=True)
