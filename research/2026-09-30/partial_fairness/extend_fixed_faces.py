"""Sequential exact three-wise insertion search; failure is seed-specific."""
import argparse,itertools,json,time
from pathlib import Path
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--max-n',type=int,default=10);args=ap.parse_args()
root=Path(__file__).parent
start=json.loads((root/'five_dice_twelve_three_wise.json').read_text());w=list(map(int,start['word']));n=5;M=12
while n<args.max_n:
 L=len(w);c=[0]*n;p=[[0]*n for _ in range(n)];cols=[]
 for g in range(L+1):
  cols.append([*c,*[p[i][j] for i in range(n) for j in range(n) if i!=j]])
  if g<L:
   j=w[g]
   for i in range(n):
    if i!=j:p[i][j]+=c[i]
   c[j]+=1
 target=[M*M//2]*n+[M**3//6]*(n*(n-1))
 model=cp_model.CpModel();h=[model.new_int_var(0,M,f'h{g}') for g in range(L+1)];model.add(sum(h)==M)
 for r,t in enumerate(target):model.add(sum(cols[g][r]*h[g] for g in range(L+1))==t)
 solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=args.seconds;solver.parameters.num_search_workers=4
 print('start extending to',n+1,flush=True);t0=time.monotonic();status=solver.solve(model)
 data={'n':n+1,'faces':M,'status':solver.status_name(status),'elapsed':time.monotonic()-t0,'word':None,'scope':'extension of one fixed previous word only'}
 if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
  gaps=[solver.value(x) for x in h];v=[]
  for g in range(L+1):
   v += [n]*gaps[g]
   if g<L:v.append(w[g])
  n+=1;w=v;dp={():1}
  for a in w:
   for pat,z in list(dp.items()):
    if len(pat)<3 and a not in pat:dp[pat+(a,)]=dp.get(pat+(a,),0)+z
  for k in [1,2,3]:assert all(dp[t]==M**k//[1,1,2,6][k] for t in itertools.permutations(range(n),k))
  data.update(word=w,gaps=gaps,verified=True)
 print(json.dumps(data),flush=True);(root/f'twelve_face_extension_n{data["n"]}.json').write_text(json.dumps(data,indent=2)+'\n')
 if data['word'] is None:break
