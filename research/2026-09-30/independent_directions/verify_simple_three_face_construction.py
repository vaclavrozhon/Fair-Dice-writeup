"""Exact standalone verification of the simplified 4-die construction."""
import json
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from math import lcm
here=Path(__file__).parent
obj=json.loads((here/'four_dice_three_face_simple_weighted.json').read_text())
rows=[(j,F(w)) for j,w in obj['weighted_rows']]
assert [sum(w for j,w in rows if j==i) for i in range(4)]==[1]*4
assert all(w>0 for j,w in rows)
assert [w for j,w in rows if j==3]==[F(1,3)]*3
prob={():F(1)}
for j,w in rows:
 for pi,v in list(prob.items()):
  if j not in pi:prob[pi+(j,)]=prob.get(pi+(j,),F(0))+v*w
assert [prob[pi] for pi in permutations(range(4))]==[F(1,24)]*24
counts=[lcm(*(w.denominator for j,w in rows if j==i)) for i in range(4)]
runs=[]
for j,w in rows:
 num=w*counts[j];assert num.denominator==1
 if runs and runs[-1][0]==j:runs[-1][1]+=num.numerator
 else:runs.append([j,num.numerator])
assert [sum(k for j,k in runs if j==i) for i in range(4)]==counts
common=counts[0]*counts[1]*counts[2]*counts[3]//24
assert common*24==counts[0]*counts[1]*counts[2]*counts[3]
# Second, independent integer subsequence DP directly on run lengths.
cnt={():1}
for j,k in runs:
 for pi,v in list(cnt.items()):
  if j not in pi:cnt[pi+(j,)]=cnt.get(pi+(j,),0)+v*k
assert [cnt[pi] for pi in permutations(range(4))]==[common]*24
cert={'description':'Rows (die,run length), ordered by increasing label; dice indexed 0,1,2,3.','face_counts':[str(z) for z in counts],'runs':[[j,str(k)] for j,k in runs],'common_permutation_count':str(common)}
(here/'four_dice_three_face_simple_integer.json').write_text(json.dumps(cert,indent=2)+'\n')
print('Both rational and integer DP verify all24 orders. Counts=',counts,'runs=',len(runs))
