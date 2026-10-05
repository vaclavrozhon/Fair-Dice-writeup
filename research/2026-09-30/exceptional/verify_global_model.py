"""Exact certificate for the global disjoint-density construction.

Uses an existing rational local-model certificate.  The global theorem
requires additional signed density kernels; this verifies them, positivity,
and every linear moment identity.  Optional --enumerate computes ALL full
order probabilities by independent piecewise-density dynamic programming.
No floating point is used in the verifier.
"""
from fractions import Fraction as Q
from math import comb, factorial
from itertools import permutations
from pathlib import Path
import argparse
import json


def load_model(path):
    obj = json.loads(Path(path).read_text())
    m, K, D = obj["m"], obj["K"], int(obj["denominator"])
    t = [Q(int(x), D) for x in obj["baseline_numerators"]]
    corrections = [{int(q): Q(v) for q, v in group.items()}
                   for group in obj["corrections"]]
    return m, K, t, corrections


def endpoint_kernel(m):
    c = sum((Q(1, j) for j in range(1, m + 1)), Q(0))
    out = [c]
    for j in range(1, m):
        c += Q((-1)**j * comb(m, j), j)
        out.append(c)
    for r in range(m):
        moment = sum((a * Q((-j)**(r+1) - (-j-1)**(r+1), r+1)
                      for j, a in enumerate(out)), Q(0))
        assert moment == (1 if r == 0 else 0)
    return out


def construct_cells(m, K, t, corrections):
    assert len(t) == K and len(corrections) == m
    assert 0 < t[0] < t[-1] < 1
    assert all(a < b for a, b in zip(t, t[1:]))
    radius = min(Q(1, 10*K*K), t[0]/3, (1-t[-1])/3,
                 min(b-a for a, b in zip(t, t[1:]))/3)
    c = endpoint_kernel(m)
    assigned = {}
    for j, group in enumerate(corrections):
        for q, delta in group.items():
            assert q not in assigned
            assigned[q] = (j, delta)
        for s in range(1, m+1):
            mu = sum(x**s for x in t)/K
            actual = sum(delta*t[q]**(s-1) for q, delta in group.items())/K
            assert actual == (Q(1,s+1)-mu)/s
    events = []
    previous = Q(0)
    max_density_change = Q(0)
    for q, center in enumerate(t):
        left, right = center-radius, center+radius
        assert previous < left
        events.append(("cell", [left-previous]*m))
        j, delta = assigned.get(q, (-1, Q(0)))
        # Traverse the left half from its outer edge toward the cut.
        for ell in reversed(range(m)):
            masses = [radius/m]*m
            if j >= 0:
                change = delta*m/radius*c[ell]
                max_density_change = max(max_density_change, abs(change))
                assert 1+change > 0
                masses[j] *= 1+change
            events.append(("cell", masses))
        events.append(("atom", q))
        # Right half is minus the reflection of the left half.
        for ell in range(m):
            masses = [radius/m]*m
            if j >= 0:
                change = -delta*m/radius*c[ell]
                max_density_change = max(max_density_change, abs(change))
                assert 1+change > 0
                masses[j] *= 1+change
            events.append(("cell", masses))
        previous = right
    events.append(("cell", [1-previous]*m))
    assert all(sum(data[j] for kind,data in events if kind=="cell")==1
               for j in range(m))
    return events, radius, max_density_change


def full_probability(events, pattern, m, K):
    n=m+1
    counts=[Q(1)]+[Q(0)]*n
    for kind, data in events:
        if kind=="atom":
            k=pattern.index(m)+1
            counts[k] += counts[k-1]/K
        else:
            old=counts
            counts=old[:]
            for k in range(1,n+1):
                factor=Q(1)
                for r in range(1,k+1):
                    letter=pattern[k-r]
                    if letter==m:break
                    factor *= data[letter]/r
                    counts[k] += old[k-r]*factor
    return counts[n]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("--enumerate", action="store_true")
    parser.add_argument("--summary")
    args=parser.parse_args()
    m,K,t,corrections=load_model(args.certificate)
    events,radius,max_change=construct_cells(m,K,t,corrections)
    assert max_change < Q(1,2)
    print(f"Exact global density certificate: n={m+1}, distinguished faces={K}", flush=True)
    print(f"Verified {m*m} correction identities, {m} kernel moments, disjoint supports, normalized positive densities", flush=True)
    print(f"Density deviations < 1/2; {sum(kind=='cell' for kind,_ in events)} rational constant-density intervals",flush=True)
    checked=0
    if args.enumerate:
        target=Q(1,factorial(m+1))
        for pattern in permutations(range(m+1)):
            assert full_probability(events,pattern,m,K)==target, pattern
            checked+=1
        print(f"Independent exact integration: all {checked} orders equal {target}",flush=True)
    if args.summary:
        result={"m":m,"n":m+1,"K":K,"radius":str(radius),
                "correction_identities":m*m,"kernel_moments":m,
                "positive_density_lower_bound":"1/2",
                "constant_density_intervals":sum(kind=='cell' for kind,_ in events),
                "orders_enumerated":checked,
                "source_certificate":str(Path(args.certificate)),
                "scope":"Remaining orders follow from the proved disjoint-density response lemma, not enumeration."}
        Path(args.summary).write_text(json.dumps(result,indent=2)+"\n")


if __name__=="__main__":
    main()
