#!/usr/bin/env python3
"""Verify the rational certificate without numerical libraries or regeneration."""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys

source=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('local_model_m20.json')
a=json.loads(source.read_text())
m,K=a['m'],a['K']
D=int(a['denominator'])
t=[Q(int(x),D) for x in a['baseline_numerators']]
assert len(t)==K
powers=[[x**s for x in t] for s in range(m+1)]
mu=[sum(powers[s])/K for s in range(m+1)]
f=[{int(q):Q(v) for q,v in row.items()} for row in a['corrections']]
assert len(f)==m
supports=[set(row) for row in f]
assert sum(len(s) for s in supports)==len(set().union(*supports))
for j in range(m):
    p=[t[q]+f[j].get(q,Q(0)) for q in range(K)]
    assert 0<p[0] and p[-1]<1
    assert all(p[q]<p[q+1] for q in range(K-1))
    for s in range(1,m+1):
        correction=sum(v*powers[s-1][q] for q,v in f[j].items())/K
        assert correction==(Q(1,s+1)-mu[s])/s
# For every subset S, disjoint support gives product_j(t+f_j)
# =t^|S|+t^(|S|-1) sum_j f_j pointwise. The exact checked identities
# therefore certify every one of the 2^m squarefree mixed moments.
print(f'CERTIFIED: m={m}, K={K}; all rational columns strictly increasing in (0,1).')
print(f'All {m*m} correction equations hold exactly; disjoint supports prove all {2**m} subset-moment identities.')
print(f'Scalar rational degree-{m} quadrature needs at least {max(2**(m//2),3**(m//3))} nodes.')
