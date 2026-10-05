"""Exact bounded-grid search for four rational monotone comparison columns.

Five latent atoms, centered grid {−d,...,d}/d, all squarefree moments
through degree four.  An exhausted finite grid is not a nonexistence proof.
"""
import json
from itertools import combinations_with_replacement
from pathlib import Path
import sys,time
import numpy as np

def candidates(d):
    out=[]
    for a in range(-d,1):
      for b in range(a,d+1):
       for c in range(b,d+1):
        for e in range(c,d+1):
         f=-a-b-c-e
         if e<=f<=d:out.append((a,b,c,e,f))
    return np.array(out,dtype=np.int64)

for d in ([int(x) for x in sys.argv[1:]] or [3,6,9,12,15,18,21,24,27,30]):
    start=time.time();V=candidates(d);N=len(V);target=5*d*d//3
    print('denominator',d,'nodes',N,flush=True)
    adj=[]
    for i in range(N):
        inds=np.flatnonzero(V[i:]@V[i]==target)+i
        adj.append(set(map(int,inds)))
    print('edges',sum(map(len,adj)),'seconds',time.time()-start,flush=True)
    triples=0
    for i in range(N):
      for j in sorted(adj[i]):
        common=adj[i]&adj[j]
        if not common:continue
        ijs=V[i]*V[j]
        tr=[k for k in common if int(ijs@V[k])==0]
        for k in tr:
            triples+=1
            ds=sorted(common&adj[k])
            if not ds:continue
            vv=V[ds]
            good=(vv@ijs==0)&(vv@(V[i]*V[k])==0)&(vv@(V[j]*V[k])==0)&(vv@(ijs*V[k])==d**4)
            if not good.any():continue
            ell=ds[int(np.flatnonzero(good)[0])]
            cols=V[[i,j,k,ell]].T.tolist()
            obj={'denominator':d,'centered_integer_rows':cols}
            print('EXACT CERTIFICATE',obj,flush=True)
            Path('local_four_on_five_grid_certificate.json').write_text(json.dumps(obj,indent=2))
            raise SystemExit
    print('triples',triples,'seconds',time.time()-start,flush=True)
