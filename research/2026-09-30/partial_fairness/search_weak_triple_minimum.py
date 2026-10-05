"""Search q permutations whose minimum on every triple is uniform."""
import argparse,itertools,json,time
from pathlib import Path
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=7);ap.add_argument('--q',type=int,default=6);ap.add_argument('--seconds',type=int,default=120);args=ap.parse_args();n,q=args.n,args.q
assert q%3==0
model=cp_model.CpModel();r=[[model.new_int_var(0,n-1,f'r{k}_{i}') for i in range(n)] for k in range(q)]
for row in r:model.add_all_different(row)
for i in range(n):model.add(r[0][i]==i)
b={}
for k in range(q):
 for i,j in itertools.combinations(range(n),2):
  v=model.new_bool_var(f'b{k}_{i}_{j}');model.add(r[k][i]<r[k][j]).only_enforce_if(v);model.add(r[k][i]>r[k][j]).only_enforce_if(v.Not());b[k,i,j]=v;b[k,j,i]=v.Not()
for T in itertools.combinations(range(n),3):
 for i in T:
  wins=[];j,z=[x for x in T if x!=i]
  for k in range(q):
   w=model.new_bool_var(f'w{k}_{i}_{j}_{z}');model.add_bool_and([b[k,i,j],b[k,i,z]]).only_enforce_if(w);model.add_bool_or([b[k,i,j].Not(),b[k,i,z].Not()]).only_enforce_if(w.Not());wins.append(w)
  model.add(sum(wins)==q//3)
# Sort remaining permutations by their base-n integer encoding.
codes=[model.new_int_var(0,n**n,f'code{k}') for k in range(1,q)]
for k,code in enumerate(codes,1):model.add(code==sum(n**i*r[k][i] for i in range(n)))
for a,bv in zip(codes,codes[1:]):model.add(a<=bv)
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=args.seconds;solver.parameters.num_search_workers=4
start=time.monotonic();status=solver.solve(model);data={'n':n,'q':q,'status':solver.status_name(status),'elapsed':time.monotonic()-start,'permutations':None}
if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
 ps=[sorted(range(n),key=lambda i:solver.value(row[i])) for row in r]
 assert all(sum(next(a for a in p if a in T)==i for p in ps)==q//3 for T in itertools.combinations(range(n),3) for i in T)
 data['permutations']=ps
print(json.dumps(data),flush=True);Path(__file__).with_name(f'weak_triple_n{n}_q{q}.json').write_text(json.dumps(data,indent=2)+'\n')
