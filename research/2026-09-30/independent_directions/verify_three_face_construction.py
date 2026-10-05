"""Exact independent DP verification and run-length uniform-die export."""
import json
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from math import lcm,gcd
here=Path(__file__).parent
obj=json.loads((here/'four_dice_three_face_weighted_certificate.json').read_text())
rows=[]
for g,cell in enumerate(obj['cell_realizations']):
 faces=sorted(cell['faces'],key=lambda row:F(row[0]))
 assert len(set(F(row[0]) for row in faces))==len(faces)
 for pos,die,weight in faces:
  rows.append((die,F(weight)*F(obj['cell_masses'][die][g])))
 if g<3:rows.append((3,F(1,3)))
sums=[sum(w for j,w in rows if j==i) for i in range(4)]
assert sums==[1]*4,sums
assert all(w>0 for j,w in rows)
prob={():F(1)}
for die,weight in rows:
 for word,value in list(prob.items()):
  if die not in word:
   new=word+(die,)
   prob[new]=prob.get(new,F(0))+weight*value
for pi in permutations(range(4)):
 assert prob[pi]==F(1,24),(pi,prob[pi])
print('VERIFIED:',len(rows),'weighted faces; all 24 probabilities exactly 1/24.')
counts=[lcm(*(w.denominator for j,w in rows if j==i)) for i in range(4)]
runs=[(die,int(w*counts[die])) for die,w in rows]
assert all(n>0 for die,n in runs)
assert [sum(n for j,n in runs if j==i) for i in range(4)]==counts
assert counts[3]==3
# Merge adjacent equal letters; safe and useful for a compact certificate.
merged=[]
for die,n in runs:
 if merged and merged[-1][0]==die:merged[-1]=(die,merged[-1][1]+n)
 else:merged.append((die,n))
cert={'description':'Each row is a run (die,number_of_consecutive_uniform_faces), in label order. Dice indexed 0,1,2,3.','face_counts':[str(c) for c in counts],'runs':[[j,str(n)] for j,n in merged],'all_full_pattern_count':str(counts[0]*counts[1]*counts[2]*counts[3]//24)}
(here/'four_dice_three_face_integer_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
print('face-count decimal digits:',[len(str(c)) for c in counts])
print('face counts:',counts)
print('runs:',len(merged))
