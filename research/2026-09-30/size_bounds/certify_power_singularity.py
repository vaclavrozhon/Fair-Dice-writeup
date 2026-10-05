#!/usr/bin/env python3
"""Exact ad_H-stability certificate: all powers of the fair word stay singular."""
import json,math
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix
from diagnostic_endpoint_rank import jacobian
w=json.loads(Path('../equal_size/meyer_2023_five_dice_sixty.json').read_text())['word']
pats,cols=jacobian(w);idx={p:i for i,p in enumerate(pats)};n=5;F=60
cert=json.loads(Path('endpoint_singularity_certificate.json').read_text());selected=cert['pivot_faces']
V=[];AV=[]
for c in cols:
 v=[]
 for p in pats:
  v.append(sum(c[idx[p[:j]]]*((-F)**(len(p)-j)//math.factorial(len(p)-j)) for j in range(1,len(p)+1)))
 V.append(v)
 AV.append([(v[idx[p[1:]]]-v[idx[p[:-1]]])if len(p)>1 else 0 for p in pats])
A=s.Matrix(V).T;C=s.Matrix(AV).T;basis={};pr=1000000007
for q in selected:
 c=[v%pr for v in V[q]]
 while any(c):
  j=next(i for i,v in enumerate(c)if v)
  if j not in basis:
   inv=pow(c[j],-1,pr);basis[j]=[(v*inv)%pr for v in c];break
  b=basis[j];v=c[j];c=[(x-v*y)%pr for x,y in zip(c,b)]
rows=list(basis);r=len(rows);assert r==78
B=DomainMatrix.from_Matrix(A.extract(rows,selected)).convert_to(s.ZZ)
inv,den=B.inv_den(method='rref')
left=DomainMatrix.from_Matrix(A[:,selected]).convert_to(s.ZZ)
for name,T in [('self',A),('ad_H',C)]:
 TD=DomainMatrix.from_Matrix(T).convert_to(s.ZZ);right=DomainMatrix.from_Matrix(T[rows,:]).convert_to(s.ZZ)
 assert (left*inv*right-TD*den).is_zero_matrix,name
out={'source':'../equal_size/meyer_2023_five_dice_sixty.json','rank':r,'ambient_lie_dimension':89,'right_trivialized':True,'ad_H_invariant_exact':True,'all_positive_integer_powers_have_rank':r,'pivot_rows':rows,'pivot_faces':selected,'inverse_denominator':str(den)}
Path('endpoint_power_singularity_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
