"""Construct an exact obstruction to linear extraction of the triple projection."""
from pathlib import Path
import importlib.util
import json
import sympy as s
spec=importlib.util.spec_from_file_location('mat','research/2026-09-30/approximate_random/check_linear_extraction.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
A,B,slots=mod.matrices(3)
C=s.Matrix(__import__('numpy').concatenate([A,slots]))
print('matrix built',flush=True)
R,piv=C.rref(normalize_last=True)
print('rank',len(piv),flush=True)
b=s.Matrix(1,B.shape[1],list(map(int,B[0])))
res=b.copy()
for row,p in enumerate(piv):res-=res[p]*R[row,:]
k=next(j for j in range(C.cols) if res[j])
v=s.zeros(C.cols,1);v[k]=1
for row,p in enumerate(piv):v[p]=-R[row,k]
D=s.ilcm(*[x.q for x in v]);v*=D
vals=[int(x) for x in v]
assert C*v==s.zeros(C.rows,1)
y=s.Matrix(B)*v
assert any(y)
out={'blocks':3,'labels':5,'indices_weights':[[j,int(z)] for j,z in enumerate(v) if z],
     'triple_output':[int(z) for z in y],'max_weight':max(map(abs,vals)),
     'full_defect_zero':True,'slot_sums_zero':True}
Path('research/2026-09-30/approximate_random/linear_extraction_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
print('support',len(out['indices_weights']),'max',out['max_weight'],'Bv0',y[0],flush=True)
