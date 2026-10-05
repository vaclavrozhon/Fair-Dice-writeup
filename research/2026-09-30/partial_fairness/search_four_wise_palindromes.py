"""Four-wise fair concatenations of labelled palindrome blocks; exact checks."""
import argparse,itertools,json,math,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import csc_matrix,vstack

def count(w,p):
 d=[1]+[0]*len(p)
 for x in w:
  for j in range(len(p)-1,-1,-1):
   if x==p[j]:d[j+1]+=d[j]
 return d[-1]
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=5);ap.add_argument('--blocks',type=int,default=6);ap.add_argument('--seconds',type=float,default=300);ap.add_argument('--seed',type=int,default=0);ap.add_argument('--relax',action='store_true');args=ap.parse_args();n,m=args.n,args.blocks
 perms=list(itertools.permutations(range(n)));P=len(perms);blocks=[p+p[::-1] for p in perms];patterns=list(itertools.permutations(range(n),4))
 defects=[{p:F(count(w,p))-F(2**k,math.factorial(k)) for k in [3,4] for p in itertools.permutations(range(n),k)} for w in blocks]
 A=np.zeros((len(patterns),m*P),dtype=np.int64)
 for i in range(m):
  for j,delta in enumerate(defects):
   for row,p in enumerate(patterns):
    v=3*(delta[p]+2*i*delta[p[1:]]+2*(m-1-i)*delta[p[:-1]])
    assert v.denominator==1;A[row,i*P+j]=int(v)
 slot=np.zeros((m,m*P),dtype=np.int64)
 for i in range(m):slot[i,i*P:(i+1)*P]=1
 triples=list(itertools.combinations(range(n),3));mins=np.zeros((3*len(triples),m*P),dtype=np.int64)
 for ti,t in enumerate(triples):
  for j,p in enumerate(perms):mins[3*ti+t.index(next(x for x in p if x in t)),j::P]=1
 matrix=vstack([csc_matrix(A),csc_matrix(slot),csc_matrix(mins)],format='csc');rhs=np.array([0]*len(patterns)+[1]*m+[m/3]*len(mins))
 lo=np.zeros(m*P);hi=np.ones(m*P);lo[0]=1;hi[1:P]=0
 print(f'start n{n} blocks{m}',flush=True);start=time.monotonic()
 res=milp(np.zeros(m*P),integrality=np.zeros(m*P) if args.relax else np.ones(m*P),bounds=Bounds(lo,hi),constraints=LinearConstraint(matrix,rhs,rhs),options={'time_limit':args.seconds,'disp':False})
 out={'n':n,'blocks':m,'faces':2*m,'status':int(res.status),'message':res.message,'elapsed':time.monotonic()-start,'solution':None}
 if res.x is not None and not args.relax:
  x=np.rint(res.x).astype(np.int64);assert np.array_equal(matrix@x,rhs)
  ids=[int(np.flatnonzero(x[i*P:(i+1)*P])[0]) for i in range(m)];w=sum((blocks[j] for j in ids),())
  for k in [1,2,3,4]:assert all(count(w,p)==F((2*m)**k,math.factorial(k)) for p in itertools.permutations(range(n),k))
  out['solution']={'indices':ids,'word':''.join(map(str,w)),'count4':str(F((2*m)**4,24))}
 path=Path(__file__).with_name(f'four_wise_n{n}_M{2*m}_seed{args.seed}'+('_lp' if args.relax else '')+'.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
