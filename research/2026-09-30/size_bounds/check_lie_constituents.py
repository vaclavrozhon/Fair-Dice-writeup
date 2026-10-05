#!/usr/bin/env python3
"""Exact major-index multiplicities; corroborates the cited Lie classification.

No floating-point arithmetic or character table package is used.
A tableau is built by placing its largest entry at a removable corner.
"""
from collections import Counter
from functools import lru_cache
from fractions import Fraction
from math import factorial
import json


def partitions(n, cap=None):
    if not n:
        yield ()
        return
    for a in range(min(n, cap if cap is not None else n), 0, -1):
        for tail in partitions(n-a, a):
            yield (a,)+tail


@lru_cache(None)
def tableaux(shape):
    """Return {(row of maximum, major index): exact count}."""
    n=sum(shape)
    if n==1:
        return {(0,0):1}
    ans=Counter()
    for row,a in enumerate(shape):
        if row+1<len(shape) and a==shape[row+1]:
            continue
        smaller=list(shape)
        smaller[row]-=1
        smaller=tuple(a for a in smaller if a)
        for (prev,maj),cnt in tableaux(smaller).items():
            ans[row,maj+(n-1 if row>prev else 0)]+=cnt
    return dict(ans)


def hook_dimension(shape):
    n=sum(shape)
    den=1
    for i,a in enumerate(shape):
        for j in range(a):
            den*=a-j+sum(b>j for b in shape[i+1:])
    return factorial(n)//den


def check(n):
    records=[]
    missing=[]
    ratio=[]
    total=0
    for shape in partitions(n):
        dist=tableaux(shape)
        d=sum(dist.values())
        assert d==hook_dimension(shape)
        mult=sum(c for (_,maj),c in dist.items() if maj%n==1)
        total+=d*mult
        if not mult:
            missing.append(shape)
        else:
            ratio.append((Fraction(n*mult,d),shape))
        records.append({'partition':shape,'dimension':d,'multiplicity':mult})
    expected=[(n,)]
    if n>2:
        expected.append((1,)*n)
    if n==4:
        expected.append((2,2))
    if n==6:
        expected.append((2,2,2))
    assert set(missing)==set(expected),(n,missing)
    assert total==factorial(n-1),(n,total)
    minratio,shape=min(ratio)
    return {'n':n,'missing':missing,'dimension_check':total,
            'minimum_n_times_multiplicity_over_dimension':str(minratio),
            'minimum_partition':shape,'irreducibles':records}

if __name__=='__main__':
    out=[check(n) for n in range(2,21)]
    with open('lie_constituent_checks.json','w') as f:
        json.dump(out,f,indent=2)
    for row in out:
        print(row['n'],row['missing'],row['minimum_n_times_multiplicity_over_dimension'],row['minimum_partition'])
