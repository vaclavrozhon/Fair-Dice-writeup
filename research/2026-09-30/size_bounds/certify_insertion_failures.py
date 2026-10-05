#!/usr/bin/env python3
"""Produce and independently check short integral Farkas certificates."""
import itertools,json
import numpy as np
from scipy.optimize import linprog
from insert_fifth_into_30 import W12,W18,system
out=[]
for reverse in (False,True):
    for perm in itertools.permutations(range(4)):
        word=tuple(map(int,W12))+tuple(perm[int(a)] for a in (W18[::-1] if reverse else W18))
        mat=system(word)
        result=linprog(np.ones(120),A_ub=-mat.T/(30**4),b_ub=np.zeros(121),bounds=[(-1,1)]*120,method='highs')
        assert result.success and result.fun<0
        scale=100
        while True:
            y=[int(np.ceil(scale*x))+1 for x in result.x]
            prods=[sum(a*int(b) for a,b in zip(y,col)) for col in mat.T]
            if min(prods)>=0 and sum(y)<0:break
            scale*=10
        out.append({'reverse':reverse,'relative_relabeling':perm,'word':''.join(map(str,word)),
                    'certificate':y,'minimum_gap_pairing':min(prods),'uniform_target_pairing':sum(y),
                    'max_coefficient':max(map(abs,y))})
with open('insert_fifth_30_farkas.json','w') as f:json.dump(out,f,indent=2)
# Regenerate every coefficient matrix from the words, use only integers.
for row in json.load(open('insert_fifth_30_farkas.json')):
    mat=system(tuple(map(int,row['word'])))
    y=row['certificate']
    assert sum(y)<0
    assert all(sum(a*int(b) for a,b in zip(y,col))>=0 for col in mat.T)
print('Exact Farkas certificates checked:',len(out),'largest coefficient',max(r['max_coefficient'] for r in out))
