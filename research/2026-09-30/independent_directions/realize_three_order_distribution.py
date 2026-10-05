"""Construct rational three-die distributions near a supplied target on S3.
A known fair 3x6 word is relabelled; one die is tilted to set the marginal
between the other two, and weights on the variable die are solved by LP.
"""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json
import numpy as np
import sympy as s
from scipy.optimize import linprog
P=list(permutations(range(3)))
BASE=[ord(ch)-97 for ch in 'abccbabcaacbcabbac']

def realize(q):
 for rel in P:
  word=[rel[i] for i in BASE]
  # variable die 0, tilted die 1, fixed die 2. Rel changes spatial order.
  pos={j:[i for i,x in enumerate(word) if x==j] for j in range(3)}
  target=sum(q[k] for k,pi in enumerate(P) if pi.index(1)<pi.index(2))
  z=[sum(F(1,6) for y in pos[2] if x<y)-F(1,2) for x in pos[1]]
  var=sum(v*v for v in z)/6
  lam=(target-F(1,2))/var
  weights1=[(1+lam*v)/6 for v in z]
  if min(weights1)<0:continue
  fixed=sorted([(x,1,w) for x,w in zip(pos[1],weights1)]+[(x,2,F(1,6)) for x in pos[2]])
  # Put variable die in every gap, including exterior gaps, for maximal flexibility.
  gaps=[fixed[0][0]-F(1,2)]+[(fixed[i][0]+fixed[i+1][0])/F(2) for i in range(len(fixed)-1)]+[fixed[-1][0]+F(1,2)]
  mat=[[F(0) for _ in gaps] for _ in P]
  for k,gap in enumerate(gaps):
   for x,w1 in zip(pos[1],weights1):
    for y in pos[2]:
     pi=tuple(i for _,i in sorted([(gap,0),(x,1),(y,2)]))
     mat[P.index(pi)][k]+=w1/6
  AA=np.array(mat,dtype=float);bb=np.array(q,dtype=float)
  ng=len(gaps)
  res=linprog(np.r_[np.zeros(ng),-1],A_ub=np.c_[-np.eye(ng),np.ones(ng)],b_ub=np.zeros(ng),A_eq=np.c_[AA,np.zeros(6)],b_eq=bb,bounds=[(0,None)]*(ng+1),method='highs')
  if not res.success:continue
  M=s.Matrix(mat);rhs=s.Matrix(q)
  aug,piv=M.row_join(rhs).rref();free=[j for j in range(ng) if j not in piv]
  vals={j:s.Rational(str(res.x[j])).limit_denominator(100000) for j in free}
  for row,j in enumerate(piv):vals[j]=aug[row,-1]-sum(aug[row,k]*vals[k] for k in free)
  if any(v<0 for v in vals.values()):continue
  x=s.Matrix([vals[j] for j in range(ng)])
  assert M*x==rhs
  faces=sorted([(str(gap),0,str(x[j])) for j,gap in enumerate(gaps) if x[j]>0]+[(str(a),b,str(w)) for a,b,w in fixed],key=lambda z:F(z[0]))
  return {'faces':faces,'variable_die_min_weight':str(min(x)),'relabel':rel,'tilt':str(lam)}
 return None

if __name__=='__main__':
 here=Path(__file__).parent
 src=here/'three_face_near_uniform_cell_lp_solution.json'
 if not src.exists():src=here/'three_face_feasible_cell_lp_solution.json'
 obj=json.loads(src.read_text())
 out=[]
 for g,row in enumerate(obj['cell_order_probabilities']):
  q=[F(v) for v in row]
  r=realize(q)
  print('cell',g,'success',r is not None, 'minweight',r and r['variable_die_min_weight'])
  out.append(r)
 if all(out):
  obj['cell_realizations']=out
  (here/'four_dice_three_face_weighted_certificate.json').write_text(json.dumps(obj,indent=2)+'\n')
  print('ALL CELLS REALIZED')
