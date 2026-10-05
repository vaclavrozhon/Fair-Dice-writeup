#!/usr/bin/env python3
"""Independent exact review of independent_directions' 4-dice certificate."""
from fractions import Fraction as Q
from itertools import permutations
from math import lcm
from pathlib import Path
import json

certificate=Path(__file__).parents[1]/'independent_directions/four_dice_three_face_weighted_certificate.json'
a=json.loads(certificate.read_text())
weights=[]
for cell in range(4):
    local=[]
    for position,die,weight in a['cell_realizations'][cell]['faces']:
        p,w=Q(position),Q(weight)
        assert w>0
        local.append((p,die,w))
    local.sort()
    assert len({x[0] for x in local})==len(local),'tied positions'
    for j in range(3):
        assert sum(w for _,die,w in local if die==j)==1
    for _,j,w in local:
        weights.append((j,w*Q(a['cell_masses'][j][cell])))
    if cell<3:weights.append((3,Q(1,3)))
for j in range(4):
    assert sum(w for die,w in weights if die==j)==1
    denominator=lcm(*(w.denominator for die,w in weights if die==j))
    counts=[int(w*denominator) for die,w in weights if die==j]
    assert sum(counts)==denominator
    print(f'die {j}: {len(counts)} weighted faces; equal-face count denominator has {denominator.bit_length()} bits')
for pi in permutations(range(4)):
    dp=[Q(1)]+[Q(0)]*4
    index={j:k+1 for k,j in enumerate(pi)}
    for j,w in weights:
        k=index[j]
        dp[k]+=w*dp[k-1]
    assert dp[4]==Q(1,24),(pi,dp[4])
print('All 24 full rankings have exactly probability 1/24. All weights positive and normalized. The fourth die has exactly three equiprobable faces.')
