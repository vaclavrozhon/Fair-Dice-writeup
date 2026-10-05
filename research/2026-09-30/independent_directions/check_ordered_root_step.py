"""Exact Sturm checks of the root-step lemma on rational examples."""
from fractions import Fraction as Q
from pathlib import Path
import json
import random
import sympy as sp

rng=random.Random(430971)
x=sp.Symbol("x")
checks=0
for m in range(2,13):
    for trial in range(10):
        nodes=[Q(t,101) for t in sorted(rng.sample(range(1,101),m))]
        deriv=[sp.prod(a-b for j,b in enumerate(nodes) if i!=j)
               for i,a in enumerate(nodes)]
        slopes=[Q(m)/Q(v) for v in deriv]
        constraints=[(slopes[0],nodes[0]),(-slopes[-1],1-nodes[-1])]
        constraints += [(slopes[i+1]-slopes[i],nodes[i+1]-nodes[i])
                        for i in range(m-1)]
        low=max(-b/a for a,b in constraints if a>0)
        high=min(-b/a for a,b in constraints if a<0)
        assert low<0<high
        for delta in (low/2,high/2):
            moved=[a+delta*s for a,s in zip(nodes,slopes)]
            assert 0<=moved[0]<=moved[-1]<=1
            assert all(u<=v for u,v in zip(moved,moved[1:]))
            poly=sp.Poly(sp.prod(x-sp.Rational(a.numerator,a.denominator)
                                 for a in nodes)-sp.Rational(delta.numerator,delta.denominator),x)
            assert poly.count_roots(0,1)==m
            checks+=1
record={"status":"passed","checks":checks,"degrees":"2..12",
        "method":"exact Fraction step bounds and exact rational Sturm root counts"}
Path(__file__).with_suffix(".json").write_text(json.dumps(record,indent=2))
print(record)
