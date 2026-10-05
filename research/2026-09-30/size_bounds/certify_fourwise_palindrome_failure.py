#!/usr/bin/env python3
"""Search then exactly check a degree-four separating linear functional."""
import itertools,sys,json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
m=int(sys.argv[1]) if len(sys.argv)>1 else 9
perms=list(itertools.permutations(range(5)))
pats=list(itertools.permutations(range(5),4))
def count(w,p):
 d=[1]+[0]*len(p)
 for x in w:
  for j in range(len(p)-1,-1,-1):
   if p[j]==x:d[j+1]+=d[j]
 return d[-1]
ds=[]
for rho in perms:
 w=rho+rho[::-1]
 ds.append({p:3*count(w,p)-(4 if len(p)==3 else 2) for k in (3,4) for p in itertools.permutations(range(5),k)})
A=np.array([[[d[p]+2*i*d[p[1:]]+2*(m-1-i)*d[p[:-1]] for p in pats] for d in ds] for i in range(m)],dtype=np.int64)
# With first block fixed, maximize lambda.C0 + sum_i min_r lambda.Cir.
C=np.zeros((120*(m-1),120+m-1))
for i in range(1,m):
 C[(i-1)*120:i*120,:120]=-A[i]
 C[(i-1)*120:i*120,119+i]=1
obj=np.r_[-A[0,0],-np.ones(m-1)]
r=linprog(obj,A_ub=C,b_ub=np.zeros(len(C)),bounds=[(-1,1)]*120+[(None,None)]*(m-1),method='highs')
out={'blocks':m,'lp_status':r.message,'strict_separator':bool(r.success and r.fun<-1e-7)}
if out['strict_separator']:
 scale=1
 while True:
  coeff=np.rint(scale*r.x[:120]).astype(np.int64)
  scores=A@coeff
  margin=int(scores[0,0]+sum(min(row) for row in scores[1:]))
  if margin>0:break
  scale*=10
 out.update(coefficients=coeff.tolist(),margin=margin,slot_minima=[int(v) for v in np.min(scores[1:],axis=1)],first_score=int(scores[0,0]))
 assert sum(a*int(b) for a,b in zip(out['coefficients'],A[0,0]))+sum(min(sum(a*int(b) for a,b in zip(out['coefficients'],c)) for c in slot) for slot in A[1:])==margin>0
Path(f'fourwise_palindrome_{m}_separator.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
