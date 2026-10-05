"""Direct rational global LP with two simple free cell tilts."""
from fractions import Fraction as F
from itertools import permutations,product
from pathlib import Path
import json
import numpy as np
import sympy as s
from scipy.optimize import linprog
from math import lcm
here=Path(__file__).parent
orig=json.loads((here/'four_dice_three_face_weighted_certificate.json').read_text())
w=[[F(z) for z in row] for row in orig['cell_masses']]
BASE=[ord(ch)-97 for ch in 'abccbabcaacbcabbac']
P=list(permutations(range(4)));P3=list(permutations([1,2,3]))
fixed=[];gaps=[]
for g,cell in enumerate(orig['cell_realizations']):
 word=[cell['relabel'][j] for j in BASE]
 pos={j:[i for i,x in enumerate(word) if x==j] for j in [1,2]}
 z=[sum(F(1,6) for y in pos[2] if x<y)-F(1,2) for x in pos[1]]
 for x,v in zip(pos[1],z):fixed.append((F(20*g+x),1,w[1][g]/6,g,v))
 for x in pos[2]:fixed.append((F(20*g+x),2,w[2][g]/6,None,F(0)))
 ff=sorted(pos[1]+pos[2])
 loc=[F(ff[0])-F(1,2)]+[(F(a)+b)/2 for a,b in zip(ff[:-1],ff[1:])]+[F(ff[-1])+F(1,2)]
 gaps.extend((20*g+x,g) for x in loc)
 if g<3:fixed.append((F(20*g+19),3,F(1,3),None,F(0)))
f1=[r for r in fixed if r[1]==1];f2=[r for r in fixed if r[1]==2];f3=[r for r in fixed if r[1]==3]
# All coefficients are affine functions of lambda[0:4].
T0=[F(0)]*6;TC=[[F(0)]*4 for _ in range(6)]
A0=[[F(0)]*len(gaps) for _ in P];AC=[[[F(0)]*len(gaps) for _ in P] for _ in range(4)]
for r1,r2,r3 in product(f1,f2,f3):
 prob=r1[2]*r2[2]*r3[2];g=r1[3];tilt=prob*r1[4]
 idx=P3.index(tuple(r[1] for r in sorted([r1,r2,r3])))
 T0[idx]+=prob;TC[idx][g]+=tilt
 for k,(position,cell) in enumerate(gaps):
  pi=tuple(i for _,i in sorted([(r1[0],1),(r2[0],2),(r3[0],3),(position,0)]))
  j=P.index(pi);A0[j][k]+=prob;AC[g][j][k]+=tilt
# Weighted prefix-pair-area constraint is forced by full four-die fairness,
# because the variable die has its prescribed cumulative masses at each cut.
extra0=F(0);extra=[F(0)]*4
for q in range(3):
 cut=20*q+19;p0=sum(w[0][:q+1])
 for r1,r2 in product(f1,f2):
  if r1[0]<cut and r2[0]<cut:
   sign=1 if r1[0]<r2[0] else -1
   value=p0*sign*r1[2]*r2[2]
   extra0+=value;extra[r1[3]]+=value*r1[4]
L=s.Matrix(TC+[extra]);lb=s.Matrix([F(1,6)-v for v in T0]+[-extra0])
aug,piv=L.row_join(lb).rref();free=[i for i in range(4) if i not in piv]
print('tilt rank',len(piv),'free',free,flush=True)
oldlam=[float(F(cell['tilt'])) for cell in orig['cell_realizations']]
for denominator in [10,100,1000]:
 lam={j:s.Rational(round(oldlam[j]*denominator),denominator) for j in free}
 for row,j in enumerate(piv):lam[j]=aug[row,-1]-sum(aug[row,k]*lam[k] for k in free)
 lambdas=[F(lam[j]) for j in range(4)]
 if any(1+lambdas[r[3]]*r[4]<=0 for r in f1):continue
 A=[[A0[j][k]+sum(lambdas[g]*AC[g][j][k] for g in range(4)) for k in range(len(gaps))] for j in range(24)]
 b=[F(1,24)]*24
 for g in range(4):
  A.append([F(int(cell==g)) for pos,cell in gaps]);b.append(w[0][g])
 AA=np.array(A,dtype=float);bb=np.array(b,dtype=float);ng=len(gaps)
 res=linprog(np.r_[np.zeros(ng),-1],A_ub=np.c_[-np.eye(ng),np.ones(ng)],b_ub=np.zeros(ng),A_eq=np.c_[AA,np.zeros(len(A))],b_eq=bb,bounds=[(0,None)]*(ng+1),method='highs')
 print('tilt grid',denominator,'feasible',res.success,'lambdas',lambdas,flush=True)
 if not res.success:continue
 print('margin',res.x[-1],flush=True)
 M=s.Matrix(A);rhs=s.Matrix(b);aug,piv=M.row_join(rhs).rref();free=[j for j in range(ng) if j not in piv]
 print('global exact rank',len(piv),'free',len(free),flush=True)
 for grid in [1000,10000,100000]:
  vals={j:s.Rational(round(res.x[j]*grid),grid) for j in free}
  for row,j in enumerate(piv):vals[j]=aug[row,-1]-sum(aug[row,k]*vals[k] for k in free)
  if min(vals.values())<=0:continue
  xx=s.Matrix([vals[j] for j in range(ng)]);assert M*xx==rhs
  rows=[(pos,0,F(xx[k])) for k,(pos,cell) in enumerate(gaps)]
  for pos,j,wt,g,z in fixed:rows.append((pos,j,wt*(1+lambdas[g]*z) if j==1 else wt))
  rows.sort()
  cert={'description':'Rational weighted faces in label order. Each row (die, probability); die3 has three equal faces.','tilts':[str(v) for v in lambdas],'weighted_rows':[[j,str(v)] for pos,j,v in rows]}
  (here/'four_dice_three_face_simple_weighted.json').write_text(json.dumps(cert,indent=2)+'\n')
  c=[lcm(*(v.denominator for pos,j,v in rows if j==i)) for i in range(4)]
  print('counts decimal digits',[len(str(z)) for z in c]);print('counts',c,flush=True)
  raise SystemExit
