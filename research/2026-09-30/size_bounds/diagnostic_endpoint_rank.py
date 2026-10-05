#!/usr/bin/env python3
"""Diagnostic for the universal endpoint-regularity conjecture, not a small-n optimization search."""
import itertools,math,json
from pathlib import Path

def jacobian(word):
 letters=sorted(set(word)); n=len(letters)
 pats=[p for k in range(1,n+1) for p in itertools.permutations(letters,k)]
 def prefixes(w):
  d={():1};out=[]
  for a in w:
   out.append(d.copy())
   for t,v in list(d.items()):
    if len(t)<n-1 and a not in t:d[t+(a,)]=d.get(t+(a,),0)+v
  return out
 pre=prefixes(word);suf=prefixes(word[::-1])[::-1]
 cols=[]
 for q,a in enumerate(word):
  c=[]
  for p in pats:
   if a not in p:c.append(0);continue
   j=p.index(a);c.append(pre[q].get(p[:j],0)*suf[q].get(p[j+1:][::-1],0))
  cols.append(c)
 return pats,cols

def rankmod(cols,p):
 basis={}
 for cc in cols:
  c=[v%p for v in cc]
  while any(c):
   j=next(i for i,v in enumerate(c) if v)
   if j not in basis:
    inv=pow(c[j],-1,p);basis[j]=[(v*inv)%p for v in c];break
   b=basis[j];v=c[j];c=[(x-v*y)%p for x,y in zip(c,b)]
 return len(basis)

if __name__=='__main__':
 words=[('three','abccbabcaacbcabbac'),('four18','120330213201102302133120021331201203302132011023320110230213312012033021'),('meyer5',json.loads(Path('../equal_size/meyer_2023_five_dice_sixty.json').read_text())['word'])]
 out=[]
 for name,w in words:
  n=len(set(w));dim=sum(math.comb(n,k)*math.factorial(k-1) for k in range(1,n+1));pats,cols=jacobian(w)
  ranks={p:rankmod(cols,p) for p in [1000000007,1000000009]}
  row={'name':name,'n':n,'faces':len(w)//n,'lie_dimension':dim,'runs':1+sum(a!=b for a,b in zip(w,w[1:])),'ranks_mod_prime':ranks};print(row,flush=True);out.append(row)
 Path('diagnostic_endpoint_rank.json').write_text(json.dumps(out,indent=2)+'\n')
