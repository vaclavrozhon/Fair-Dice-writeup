#!/usr/bin/env python3
"""Search arbitrary gaps of concatenated 4-fair words; LP reconnaissance."""
import itertools,json
import numpy as np
from scipy.optimize import linprog
from math import factorial
A='12033021';B='32011023';C='02133120'
W12=A+B+C+C+B+A
W18=A+B+C+C+A+B+B+C+A
perms=list(itertools.permutations(range(5)))
patterns=[()]+[p for k in range(1,5) for p in itertools.permutations(range(4),k)]
idx={p:j for j,p in enumerate(patterns)}


def table(word):
    out=np.zeros((len(word)+1,len(patterns)),dtype=np.int64)
    out[0,0]=1
    for k,a in enumerate(word):
        out[k+1]=out[k]
        for p in patterns[1:]:
            if p[-1]==a:out[k+1,idx[p]]+=out[k,idx[p[:-1]]]
    return out


def system(word):
    pre=table(word); rev=table(word[::-1]); cols=len(word)+1
    mat=np.empty((120,cols),dtype=np.int64)
    for row,p in enumerate(perms):
        k=p.index(4); left=p[:k];right=p[k+1:]
        mat[row]=pre[:,idx[left]]*rev[::-1,idx[right[::-1]]]
    assert np.all(mat.sum(axis=0)==30**4)
    return mat


if __name__=='__main__':
    out=[]
    for reverse in (False,True):
        for perm in itertools.permutations(range(4)):
            w18=W18[::-1] if reverse else W18
            word=tuple(map(int,W12))+tuple(perm[int(a)] for a in w18)
            mat=system(word)
            result=linprog(np.zeros(len(word)+1),A_eq=mat/(30**4),b_eq=np.full(120,30/120),bounds=(0,None),method='highs')
            row={'reverse':reverse,'relative_relabeling':perm,'feasible':bool(result.success),'status':result.message}
            if result.success:
                row['word']=''.join(map(str,word));row['lp_gaps']={str(i):float(x) for i,x in enumerate(result.x) if x>1e-8}
                np.savez('insert_fifth_30_feasible_matrix.npz',matrix=mat,word=word,lp=result.x)
            out.append(row)
            print(reverse,perm,result.success,flush=True)
    with open('insert_fifth_30_lp.json','w') as f:json.dump(out,f,indent=2)
    print('Feasible',sum(r['feasible'] for r in out),'of',len(out))
