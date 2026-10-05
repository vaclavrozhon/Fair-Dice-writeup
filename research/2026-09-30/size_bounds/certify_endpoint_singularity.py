#!/usr/bin/env python3
import json,time
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix
from diagnostic_endpoint_rank import jacobian
w=json.loads(Path('../equal_size/meyer_2023_five_dice_sixty.json').read_text())['word']
pats,cols=jacobian(w);pr=1000000007;basis={};selected=[]
for q,cc in enumerate(cols):
 c=[v%pr for v in cc]
 while any(c):
  j=next(i for i,v in enumerate(c)if v)
  if j not in basis:
   inv=pow(c[j],-1,pr);basis[j]=[(v*inv)%pr for v in c];selected.append(q);break
  b=basis[j];v=c[j];c=[(x-v*y)%pr for x,y in zip(c,b)]
rows=list(basis);r=len(rows);print('modular rank',r,flush=True)
A=s.Matrix(cols).T
B=A.extract(rows,selected);start=time.time()
BD=DomainMatrix.from_Matrix(B).convert_to(s.ZZ)
inv,den=BD.inv_den(method='rref');print('inverse done',time.time()-start,'den bits',int(den).bit_length(),flush=True)
AD=DomainMatrix.from_Matrix(A).convert_to(s.ZZ)
left=DomainMatrix.from_Matrix(A[:,selected]).convert_to(s.ZZ)
right=DomainMatrix.from_Matrix(A[rows,:]).convert_to(s.ZZ)
res=left*inv*right-AD*den
assert res.is_zero_matrix
out={'source':'../equal_size/meyer_2023_five_dice_sixty.json','rank':r,'ambient_lie_dimension':89,'pivot_rows':rows,'pivot_faces':selected,'inverse_denominator':str(den),'exact_factorization_verified':True}
Path('endpoint_singularity_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
