#!/usr/bin/env python3
"""Pure-integer verification of a universal short-palindrome obstruction."""
from itertools import permutations
from pathlib import Path
import json
cert=json.loads(Path(__file__).with_name('fourwise_palindrome_9_separator.json').read_text())
lam=cert['coefficients'];pats=list(permutations(range(5),4))
def count(w,p):
 d=[1]+[0]*len(p)
 for x in w:
  for j in range(len(p)-1,-1,-1):
   if p[j]==x:d[j+1]+=d[j]
 return d[-1]
left=[];right=[];degree4=[]
for rho in permutations(range(5)):
 w=rho+rho[::-1]
 left.append(sum(a*(3*count(w,p[1:])-4) for a,p in zip(lam,pats)))
 right.append(sum(a*(3*count(w,p[:-1])-4) for a,p in zip(lam,pats)))
 degree4.append(sum(a*(3*count(w,p)-2) for a,p in zip(lam,pats)))
assert left==[0]*120
assert right==degree4
assert min(right)==-18 and right[0]==84
for q in range(1,11):
 margin=84*(2*q-1)-18*(q-1)**2
 assert margin>0
print(json.dumps({'verified':True,'suffix_projection':0,'minimum_prefix_projection':min(right),'identity_prefix_projection':right[0],'excluded_block_counts':list(range(1,11)),'formula':'84*(2*q-1)-18*(q-1)^2'},indent=2))
