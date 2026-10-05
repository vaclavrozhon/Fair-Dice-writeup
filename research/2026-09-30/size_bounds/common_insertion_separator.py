#!/usr/bin/env python3
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from insert_fifth_into_30 import system
words=[]
for fn in ('other_30_seeds_search.jsonl','meyer_30_seeds_search.jsonl'):
 for line in open(fn):
  row=json.loads(line)
  if 'word'in row:words.append(tuple(map(int,row['word'])))
words=list(dict.fromkeys(words))
cols=np.concatenate([system(w).T for w in words])
r=linprog(np.ones(120),A_ub=-cols.astype(float)/810000,b_ub=np.zeros(len(cols)),bounds=[(-1,1)]*120,method='highs')
out={'words':len(words),'columns':len(cols),'status':r.message,'objective':r.fun,'common_separator':bool(r.success and r.fun<-1e-7)}
if out['common_separator']:
 scale=100
 while True:
  y=[int(np.ceil(scale*x))+1 for x in r.x]
  products=[sum(a*int(b) for a,b in zip(y,col)) for col in cols]
  if min(products)>=0 and sum(y)<0:break
  scale*=10
 out.update(coefficients=y,minimum_column=min(products),target_pairing=sum(y))
Path('common_insertion_separator.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
