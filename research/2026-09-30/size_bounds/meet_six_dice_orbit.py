#!/usr/bin/env python3
"""Exhaustive five-term orbit search using two exact modular projections.
Every unordered pair is stored, including projection collisions. Thus failure
is conclusive within this orbit; a hit is checked in all720 coordinates.
"""
from pathlib import Path
prefix=Path('search_six_dice_orbit.py').read_text().split('for i,a in enumerate(cols):')[0]
exec(compile(prefix,'search_six_dice_orbit.py','exec'))
import time
start=time.monotonic();rng=np.random.default_rng(8675309)
hashes=[]
for _ in range(2):
 r=rng.integers(0,2**64,size=len(e),dtype=np.uint64)
 hashes.append([int(a)for a in cols.astype(np.uint64)@r])
mask=2**64-1;pairmap={};total=0
for a in range(720):
 for b in range(a,720):
  key=((hashes[0][a]+hashes[0][b])&mask,(hashes[1][a]+hashes[1][b])&mask)
  pairmap.setdefault(key,[]).append((a,b));total+=1
print('Stored pairs',total,'keys',len(pairmap),'seconds',time.monotonic()-start,flush=True)
hit=None;projection_matches=0
for key,pairs in pairmap.items():
 other=((-hashes[0][0]-key[0])&mask,(-hashes[1][0]-key[1])&mask)
 for a,b in pairs:
  for c,d in pairmap.get(other,[]):
   projection_matches+=1
   if np.all(e+cols[a]+cols[b]+cols[c]+cols[d]==0):hit=[0,a,b,c,d];break
  if hit:break
 if hit:break
out={'source':str(source),'pairs':total,'projection_keys':len(pairmap),'projection_matches':projection_matches,'solution':hit,'seconds':time.monotonic()-start,'exhaustive':True}
Path('six_dice_orbit_meet.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
if hit:finish(hit,False)
