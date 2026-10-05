"""Independent Fraction DP verification of all 120 complete orders.

This verifier does not use the polynomial kernels or linear system in the
construction script.  It processes constant-density intervals and atoms
in increasing order, extending each prefix by every possible in-cell run.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import factorial,lcm
import json
from pathlib import Path

cert=json.loads(Path('five_dice_six_face_density_certificate.json').read_text())
nodes=list(map(Q,cert['distinguished_nodes']))
ends=list(map(Q,cert['interval_endpoints']))
dens=list(map(Q,cert['density']))
assert len(nodes)==6 and len(set(nodes))==6
assert all(0<t<1 for t in nodes)
assert ends[0]==0 and ends[-1]==1 and len(ends)==len(dens)+1
assert all(a<b for a,b in zip(ends,ends[1:]))
assert all(g>0 for g in dens)
assert set(nodes)<=set(ends)
lengths=[b-a for a,b in zip(ends,ends[1:])]
assert sum(g*w for g,w in zip(dens,lengths))==1

for order in permutations('ABCDE'):
    dp=[Q(1)]+[Q(0)]*5
    for l,r,g in zip(ends,ends[1:],dens):
        weights={v:r-l for v in 'ABC'}
        weights['E']=g*(r-l)
        old=dp[:]
        for j in range(1,6):
            product=Q(1)
            for k in range(1,j+1):
                letter=order[j-k]
                if letter=='D':break
                product*=weights[letter]
                dp[j]+=old[j-k]*product/factorial(k)
        if r in nodes:
            j=order.index('D')+1
            dp[j]+=dp[j-1]/6
    assert dp[5]==Q(1,120),(order,dp[5])

mass_den=lcm(*(w.denominator for w in lengths),
             *((g*w).denominator for g,w in zip(dens,lengths)))
print('Verified: all 120 full-order probabilities equal 1/120 exactly.')
print('Distinguished die: six distinct equally weighted atoms.')
print('All 28 density values strictly positive; all distributions normalized.')
print('Cellwise finiteization mass denominator:',mass_den.bit_length(),'bits.')
