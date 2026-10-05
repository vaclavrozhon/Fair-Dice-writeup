#!/usr/bin/env python3
"""Exact symbolic integration of the full three-variable valley component."""
from itertools import permutations
import sympy as s
L,X,R=s.symbols('L X R', real=True)
variables=(L,X,R)
half=s.Rational(1,2);threehalf=s.Rational(3,2)
def g(t):return s.Rational(3,4)*(1-t)**2-s.Rational(1,4)
variance=0
mean=0
for order in permutations(variables):
 rank={v:i for i,v in enumerate(order)}
 delta=half-threehalf*int(rank[X]<rank[L] and rank[X]<rank[R])
 exl=half-threehalf*int(rank[X]<rank[L])*(1-X)
 exr=half-threehalf*int(rank[X]<rank[R])*(1-X)
 elr=half-threehalf*(L if rank[L]<rank[R] else R)
 u=s.expand(delta-exl-exr-elr+g(L)-2*g(X)+g(R))
 for power in [1,2]:
  value=u**power
  for a,b in zip(order,order[1:]+(1,)):
   value=s.integrate(value,(a,0,b))
  if power==1:mean+=value
  else:variance+=value
assert s.simplify(mean)==0
assert s.simplify(variance)==s.Rational(1,20),variance
assert s.integrate(g(X)**2,(X,0,1))==s.Rational(1,20)
print('Exact simplex integration: canonical triple mean0, variance1/20; one-variable g variance1/20.')
