#!/usr/bin/env python3
"""Standalone exact certificate for a rational symmetric 70-node degree-seven rule."""
from fractions import Fraction
from collections import Counter
magnitudes={1:3,3:3,4:1,5:3,7:9,10:1,11:2,12:1,13:4,15:4,17:4}
assert sum(magnitudes.values())==35
nodes=[Fraction(18+sign*s,36) for s,c in magnitudes.items() for _ in range(c) for sign in (-1,1)]
assert len(nodes)==70 and Counter(nodes)==Counter(1-x for x in nodes)
assert all(0<x<1 for x in nodes)
for j in range(8):
 value=sum(x**j for x in nodes)/70
 assert value==Fraction(1,j+1)
 print(j,str(value))
