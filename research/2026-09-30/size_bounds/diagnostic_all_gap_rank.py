#!/usr/bin/env python3
"""Diagnostic of a universal asymptotic regularity conjecture; no size search."""
import itertools,json,math
from pathlib import Path
from diagnostic_endpoint_rank import rankmod

def all_gap_jacobian(word):
    letters=sorted(set(word));n=len(letters)
    pats=[p for k in range(1,n+1) for p in itertools.permutations(letters,k)]
    def prefix(w):
        d={():1};out=[d.copy()]
        for a in w:
            for t,v in list(d.items()):
                if len(t)<n-1 and a not in t:d[t+(a,)]=d.get(t+(a,),0)+v
            out.append(d.copy())
        return out
    pre=prefix(word);suf=prefix(word[::-1])[::-1];cols=[]
    for q in range(len(word)+1):
        for a in letters:
            c=[]
            for p in pats:
                if a not in p:c.append(0);continue
                j=p.index(a);c.append(pre[q].get(p[:j],0)*suf[q].get(p[j+1:][::-1],0))
            cols.append(c)
    return pats,cols

if __name__=='__main__':
    w=json.loads(Path('../equal_size/meyer_2023_five_dice_sixty.json').read_text())['word']
    pats,cols=all_gap_jacobian(w)
    out={'n':len(set(w)), 'columns':len(cols),'ranks_mod_prime':{p:rankmod(cols,p) for p in [1000000007,1000000009]}}
    print(out)
    Path('diagnostic_all_gap_rank.json').write_text(json.dumps(out,indent=2)+'\n')
