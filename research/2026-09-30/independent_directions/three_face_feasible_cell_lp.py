"""Exact coefficient LP relaxation for n=4, a three-face distinguished die.
Each of four intervals supplies an arbitrary distribution on the orders of
three other dice. Pair-order marginals come from that distribution.
"""
from fractions import Fraction as F
from itertools import permutations,product
import numpy as np
from scipy.optimize import linprog
import sympy as s
import json
from pathlib import Path
out=Path(__file__).parent
ys=[[F(z) for z in col] for col in json.loads((out/'three_face_feasible_tensor.json').read_text())['centered_columns']]
p=[[F(1,2)*(1+y) for y in col] for col in ys]
w=[[col[0],col[1]-col[0],col[2]-col[1],1-col[2]] for col in p]
perms=list(permutations(range(4))); oldperms=list(permutations(range(3)))
A=[[F(0)]*24 for _ in perms];b=[F(1,24)]*24
for qi in range(3):
 for cells in product(range(4),repeat=3):
  weight=F(1,3)
  for i in range(3):weight*=w[i][cells[i]]
  occup=[[i for i in range(3) if cells[i]==g] for g in range(4)]
  together=next((g for g,inds in enumerate(occup) if len(inds)>1),None)
  if together is None:
   pi=tuple(sorted(range(4),key=lambda i:2*qi+1 if i==3 else 2*cells[i]))
   b[perms.index(pi)]-=weight
  else:
   for si,sigma in enumerate(oldperms):
    pi=tuple(sorted(range(4),key=lambda i:(2*qi+1,0) if i==3 else (2*cells[i],sigma.index(i))))
    A[perms.index(pi)][6*together+si]+=weight
for g in range(4):
 A.append([F(int(k//6==g)) for k in range(24)]);b.append(F(1))
AA=np.array(A,dtype=float);bb=np.array(b,dtype=float)
# Maximize smallest cell probability.
cc=np.r_[np.zeros(24),-1]
res=linprog(cc,A_ub=np.c_[-np.eye(24),np.ones(24)],b_ub=np.zeros(24),A_eq=np.c_[AA,np.zeros(len(A))],b_eq=bb,bounds=[(0,None)]*25,method='highs')
print('cell masses',w)
print(res.message)
M=s.Matrix(A);rhs=s.Matrix(b)
print('exact rank',M.rank(),'aug rank',M.row_join(rhs).rank())
if not res.success:
 dual=linprog(bb,A_ub=-AA.T,b_ub=np.zeros(24),bounds=[(-1,1)]*len(b),method='highs')
 print('dual',dual.fun)
 for i,z in enumerate(dual.x):
  if abs(z)>1e-8: print('dualcoeff',perms[i] if i<24 else ('cell',i-24),F(str(z)).limit_denominator(100000))
if res.success:
 print('min cell probability',res.x[-1])
 for g in range(4):print(g,res.x[g*6:(g+1)*6])
 # RREF expression x in terms of free coordinates; approximate free coordinates rationally,
 # then solve pivot entries exactly and verify strict nonnegativity.
 aug,piv=M.row_join(rhs).rref();free=[i for i in range(24) if i not in piv]
 vals={j:s.Rational(str(res.x[j])).limit_denominator(1000000) for j in free}
 for row,j in enumerate(piv):
  vals[j]=aug[row,-1]-sum(aug[row,k]*vals[k] for k in free)
 x=[vals[j] for j in range(24)]
 assert M*s.Matrix(x)==rhs
 assert all(v>=0 for v in x)
 print('exact min',min(x))
 for g in range(4):print('exact',g,x[g*6:(g+1)*6])
 obj={'old_permutations':oldperms,'cell_masses':[[str(v) for v in col] for col in w],'cell_order_probabilities':[[str(v) for v in x[g*6:(g+1)*6]] for g in range(4)],'min_probability':str(min(x))}
 (out/'three_face_feasible_cell_lp_solution.json').write_text(json.dumps(obj,indent=2)+'\n')
