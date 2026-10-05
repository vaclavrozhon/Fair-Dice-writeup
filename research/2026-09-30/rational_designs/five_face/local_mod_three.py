"""Enumerate the homogeneous five-row, four-column moment system mod 3.

Column permutations are quotiented by sorted vector indices.  These are
necessary reductions for a common positive 3-adic denominator depth;
singularity is not by itself a Q_3 obstruction.
"""
import itertools,json
from pathlib import Path
import numpy as np
p=3
vec=np.array([v for v in itertools.product(range(p),repeat=5) if sum(v)%p==0],dtype=np.int64)
dot=vec@vec.T%p
subsets=[s for k in range(1,5) for s in itertools.combinations(range(4),k)]
def rank_mod(matrix):
    a=matrix.copy()%p;r=0
    for c in range(a.shape[1]):
        hits=np.flatnonzero(a[r:,c])
        if len(hits)==0:continue
        pivot=r+hits[0];a[[r,pivot]]=a[[pivot,r]]
        a[r]=a[r]*int(pow(int(a[r,c]),-1,p))%p
        for j in range(a.shape[0]):
            if j!=r and a[j,c]:a[j]=(a[j]-a[j,c]*a[r])%p
        r+=1
        if r==a.shape[0]:break
    return r
counts={};examples={};n=0;lift_counts={1:0,2:0};lift_examples={};lifts=[]
for i in range(len(vec)):
 for j in range(i,len(vec)):
  if dot[i,j]:continue
  ij=vec[i]*vec[j]%p
  for k in range(j,len(vec)):
   if dot[i,k] or dot[j,k] or int(ij@vec[k])%p:continue
   ik=vec[i]*vec[k]%p;jk=vec[j]*vec[k]%p;ijk=ij*vec[k]%p
   for l in range(k,len(vec)):
    if dot[i,l] or dot[j,l] or dot[k,l] or int(ij@vec[l])%p or int(ik@vec[l])%p or int(jk@vec[l])%p or int(ijk@vec[l])%p:continue
    n+=1;cols=vec[[i,j,k,l]]
    jac=np.zeros((15,20),dtype=np.int64)
    for a,subset in enumerate(subsets):
      for c in subset:
        jac[a,5*c:5*c+5]=np.prod(cols[[b for b in subset if b!=c]],axis=0) if len(subset)>1 else 1
    rank=rank_mod(jac)
    key=str(rank);counts[key]=counts.get(key,0)+1
    examples.setdefault(key,cols.tolist())
    vals=np.array([sum(np.prod(cols[list(subset)],axis=0)) for subset in subsets],dtype=np.int64)
    for depth in [1,2]:
      target=np.array([5*3**(2*depth-1) if len(subset)==2 else 3**(4*depth) if len(subset)==4 else 0 for subset in subsets],dtype=np.int64)
      rhs=(target-vals)//3%3
      if rank_mod(np.column_stack([jac,rhs]))==rank:
        lift_counts[depth]+=1
        lift_examples.setdefault(str(depth),cols.tolist())
        lifts.append({'depth':depth,'columns':cols.tolist(),'rank':rank})
 print('i',i,'count',n,'ranks',counts,flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'count':n,'rank_counts':counts,'examples':examples,'lift_counts':lift_counts,'lift_examples':lift_examples,'lifts':lifts},indent=2)+'\n')
