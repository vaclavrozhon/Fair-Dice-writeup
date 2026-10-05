"""Replace the twelve copies of a clonable letter by arbitrary permutations.

This strictly extends the six-palindrome cloning family. CP-SAT finds
candidates; a separate integer subsequence DP certifies any output.
"""
from ortools.sat.python import cp_model
from pathlib import Path
import argparse,itertools,json,time

ap=argparse.ArgumentParser();ap.add_argument('--clones',type=int,default=7)
ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--seed',type=int,default=0)
args=ap.parse_args();k=args.clones;M=12
base=[int(x) for x in '012332103102201321033012' for _ in range(2)]
old=[0,2,3];pref={d:0 for d in old};weights={d:[] for d in old}
for x in base:
    if x==1:
        for d in old:weights[d].append(M-pref[d])
    else:pref[x]+=1
model=cp_model.CpModel()
rank=[[model.new_int_var(0,k-1,f'r{r}_{a}') for a in range(k)]for r in range(M)]
for row in rank:model.add_all_different(row)
for a in range(k):model.add(rank[0][a]==a)
b={}
for r in range(M):
    for a,c in itertools.combinations(range(k),2):
        z=model.new_bool_var(f'b{r}_{a}_{c}')
        model.add(rank[r][a]<rank[r][c]).only_enforce_if(z)
        model.add(rank[r][a]>rank[r][c]).only_enforce_if(z.Not())
        b[r,a,c]=z;b[r,c,a]=z.Not()
for a,c in itertools.combinations(range(k),2):
    model.add(sum(b[r,a,c]for r in range(M))==6)
    for d in old:model.add(sum(weights[d][r]*b[r,a,c]for r in range(M))==36)
for a,c,d in itertools.permutations(range(k),3):
    terms=[]
    for r in range(M):
        z=model.new_bool_var(f't{r}_{a}_{c}_{d}')
        model.add(z<=b[r,a,c]);model.add(z<=b[r,c,d])
        model.add(z>=b[r,a,c]+b[r,c,d]-1)
        terms += [(11-r)*b[r,a,c],r*b[r,c,d],z]
    model.add(sum(terms)==68)
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=args.seconds
solver.parameters.num_search_workers=8;solver.parameters.random_seed=args.seed
solver.parameters.log_search_progress=True
t=time.time();status=solver.solve(model)
out={'clones':k,'faces':M,'n':k+3,'status':solver.status_name(status),'seconds':time.time()-t,'weights':weights}
if status in(cp_model.OPTIMAL,cp_model.FEASIBLE):
    permutations=[sorted(range(k),key=lambda a:solver.value(rank[r][a]))for r in range(M)]
    word=[];r=0
    for x in base:
        if x==1:word+=permutations[r];r+=1
        else:word.append(k+old.index(x))
    dp={():1}
    for x in word:
        for p,v in list(dp.items()):
            if len(p)<3 and x not in p:dp[p+(x,)]=dp.get(p+(x,),0)+v
    for s in (1,2,3):
        expected=M**s//(1 if s==1 else 2 if s==2 else 6)
        assert all(dp[p]==expected for p in itertools.permutations(range(k+3),s))
    out.update(permutations=permutations,word=word,verified_three_wise=True)
path=Path(__file__).with_name(f'permutation_clones_k{k}_seed{args.seed}.json')
path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
