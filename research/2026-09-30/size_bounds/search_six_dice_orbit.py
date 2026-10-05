#!/usr/bin/env python3
"""Exact orbit cancellation of the degree-five defect of a four-wise fair seed."""
import itertools,json,sys,math
from pathlib import Path
from collections import Counter
import numpy as np
from ortools.sat.python import cp_model
source=Path('../partial_fairness/triple_winner_half_n6_M6_seed0.json')
w=tuple(json.loads(source.read_text())['word'])
assert len(w)==72 and Counter(w)=={i:12 for i in range(6)} and w==w[::-1]
def count(w,p):
 d=[1]+[0]*len(p)
 for x in w:
  for j in range(len(p)-1,-1,-1):
   if p[j]==x:d[j+1]+=d[j]
 return d[-1]
assert all(count(w,p)==864 for p in itertools.permutations(range(6),4))
perms=list(itertools.permutations(range(6)));pats=list(itertools.permutations(range(6),5));idx={p:i for i,p in enumerate(pats)}
e=np.array([5*count(w,p)-10368 for p in pats],dtype=np.int64)
cols=[]
for sig in perms:
 inv=[0]*6
 for i,v in enumerate(sig):inv[v]=i
 cols.append(np.array([e[idx[tuple(inv[i] for i in p)]] for p in pats],dtype=np.int64))
cols=np.array(cols)
lookup={a.tobytes():i for i,a in enumerate(cols)}
print('seed defect range',int(min(e)),int(max(e)),'distinct orbit',len(lookup),flush=True)

def finish(ids,palindrome):
 word=sum((tuple(perms[i][x] for x in w) for i in ids),())
 M=12*len(ids)
 assert all(count(word,p)==M**5//120 for p in pats)
 if not palindrome:word=word[::-1]+word;M*=2
 assert word==word[::-1]
 vals=[count(word,p)for p in perms];assert len(set(vals))==1 and vals[0]==M**6//720
 out={'source':str(source),'relabeling_indices':ids,'relabelings':[perms[i]for i in ids],'seed_faces':12,'faces':M,'full_fair':True,'full_order_count':vals[0],'word':list(word)}
 Path(f'six_dice_fair_M{M}.json').write_text(json.dumps(out,indent=2)+'\n');print('FOUND',json.dumps({k:v for k,v in out.items()if k!='word'}),flush=True)

for i,a in enumerate(cols):
 j=lookup.get((-2*(e+a)).tobytes())
 if j is not None:
  finish([0,i,j,i,0],True);sys.exit()
print('No 2+2+1 orbit relation',flush=True)
# A positive five-term sum; relabeling permits one selected seed to be identity.
model=cp_model.CpModel();x=[model.new_int_var(0,5,f'x{i}')for i in range(len(perms))]
model.add(sum(x)==5);model.add(x[0]>=1)
for row in cols.T:model.add(sum(int(a)*b for a,b in zip(row,x))==0)
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=float(sys.argv[1])if len(sys.argv)>1 else 600;solver.parameters.num_search_workers=2;solver.parameters.log_search_progress=True
status=solver.solve(model)
out={'status':solver.status_name(status),'seconds':solver.wall_time,'source':str(source)}
if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
 ids=[i for i,v in enumerate(x)for _ in range(solver.value(v))]
 assert np.all(sum((cols[i]for i in ids),np.zeros_like(e))==0)
 out['indices']=ids;finish(ids,False)
Path('six_dice_orbit_search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
