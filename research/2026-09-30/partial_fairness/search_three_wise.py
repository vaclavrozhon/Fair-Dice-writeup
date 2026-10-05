"""CP-SAT search for equal-count, three-wise fair words.
A returned word is verified separately by integer scattered-subword DP.
Timeout/UNKNOWN is not an infeasibility certificate.
"""
import argparse,itertools,json,time
from pathlib import Path
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=5);ap.add_argument('--faces',type=int,default=6);ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--seed',type=int,default=0);args=ap.parse_args()
n,M=args.n,args.faces;L=n*M
assert M*M%2==0 and M**3%3==0
model=cp_model.CpModel()
p=[[model.new_int_var(0,L-1,f'p{i}_{r}') for r in range(M)] for i in range(n)]
model.add_all_different([v for row in p for v in row])
for row in p:
 for a,b in zip(row,row[1:]):model.add(a<b)
for i in range(n-1):model.add(p[i][0]<p[i+1][0])
model.add(p[0][0]==0)
rank={}
for i in range(n):
 for j in range(i+1,n):
  cmp=[[model.new_bool_var(f'b{i}_{r}_{j}_{s}') for s in range(M)] for r in range(M)]
  for r,s in itertools.product(range(M),repeat=2):
   model.add(p[j][s]<p[i][r]).only_enforce_if(cmp[r][s])
   model.add(p[j][s]>p[i][r]).only_enforce_if(cmp[r][s].Not())
  for r in range(M):
   v=model.new_int_var(0,M,f'rank{i}_{r}_{j}');model.add(v==sum(cmp[r]));rank[i,r,j]=v
  for s in range(M):
   v=model.new_int_var(0,M,f'rank{j}_{s}_{i}');model.add(v==M-sum(cmp[r][s] for r in range(M)));rank[j,s,i]=v
  model.add(sum(rank[i,r,j] for r in range(M))==M*M//2)
for i in range(n):
 for j,k in itertools.combinations([v for v in range(n) if v!=i],2):
  terms=[]
  for r in range(M):
   v=model.new_int_var(0,M*M,f'prod{i}_{r}_{j}_{k}');model.add_multiplication_equality(v,[rank[i,r,j],rank[i,r,k]]);terms.append(v)
  model.add(sum(terms)==M**3//3)
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=args.seconds;solver.parameters.num_search_workers=4;solver.parameters.random_seed=args.seed
print(f'start n={n}, M={M}, seed={args.seed}',flush=True)
start=time.monotonic();status=solver.solve(model)
data={'n':n,'faces':M,'seed':args.seed,'status':solver.status_name(status),'elapsed':time.monotonic()-start,'word':None}
if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
 w=[None]*L
 for i in range(n):
  for r in range(M):w[solver.value(p[i][r])]=i
 d={():1}
 for a in w:
  for pat,c in list(d.items()):
   if len(pat)<3 and a not in pat:d[pat+(a,)]=d.get(pat+(a,),0)+c
 counts={k:sorted({d[t] for t in itertools.permutations(range(n),k)}) for k in [1,2,3]}
 assert counts=={1:[M],2:[M*M//2],3:[M**3//6]},counts
 data.update(word=w,verified_counts=counts)
print(json.dumps(data),flush=True)
Path(__file__).with_name(f'three_wise_n{n}_M{M}_seed{args.seed}.json').write_text(json.dumps(data,indent=2)+'\n')
