#!/usr/bin/env python3
"""Build/verify a compact, exact finite-word certificate for the small die.

No word with its enormous number of faces is expanded. The outer word is
the event sequence returned by construct_cells. At a cell with masses
alpha_j, substitute the base fair word with each letter j repeated D*alpha_j
times. At an atom insert the distinguished letter once. Consecutive word
positions are the distinct numerical face labels.

The verifier checks all integer insertion moments of the base word and all
rational density/correction identities. The full-order conclusion uses the
proved insertion and disjoint-density lemmas; it is not an enumeration of n!.
"""
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial, lcm
from pathlib import Path
import argparse
import json
import sys

from verify_global_model import load_model, construct_cells

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "size_bounds"))


def make_base(m):
    from integer_quadrature import construct
    constant = 2**25
    steps = []
    for r in range(1, m):
        row = construct(r, constant, include_weights=True)
        steps.append({"old_letters": r, "copies": row["N"],
                      "new_letter_gap_lengths": row["gaps"]})
    return {"initial_letter": 0, "initial_repetitions": constant,
            "steps": steps}


def verify_base(base, m):
    assert base["initial_letter"] == 0
    faces = int(base["initial_repetitions"])
    assert faces > 0 and len(base["steps"]) == m-1
    verified = 0
    for r, step in enumerate(base["steps"], 1):
        assert step["old_letters"] == r
        copies = int(step["copies"])
        gaps = [int(x) for x in step["new_letter_gap_lengths"]]
        assert copies > 0 and len(gaps) == copies+1 and min(gaps) >= 0
        new_faces = sum(gaps)
        assert new_faces == copies*faces
        for j in range(r+1):
            # Independent monomial-basis check; no Hahn weights are needed.
            assert (j+1)*sum(g*i**j for i, g in enumerate(gaps)) == new_faces*copies**j
            verified += 1
        faces = new_faces
    return faces, verified


def check_finite_masses(events, denominator, m):
    assert denominator > 0
    # Only the distinct rational masses need integrality checks; normalization
    # has already been checked independently by construct_cells.
    masses = {a for kind, data in events if kind == "cell" for a in data}
    assert all(a > 0 and denominator % a.denominator == 0 for a in masses)
    return len(masses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["build", "verify"])
    parser.add_argument("model")
    parser.add_argument("finite_certificate")
    args = parser.parse_args()
    model_path = Path(args.model)
    digest = sha256(model_path.read_bytes()).hexdigest()
    m, K, t, corrections = load_model(model_path)
    events, radius, max_change = construct_cells(m, K, t, corrections)
    assert max_change < Q(1, 2)
    destination = Path(args.finite_certificate)
    if args.mode == "build":
        denominators = {a.denominator for kind, data in events if kind == "cell" for a in data}
        denominator = 1
        for value in sorted(denominators):
            denominator = lcm(denominator, value)
        base = make_base(m)
        faces, moments = verify_base(base, m)
        obj = {
            "format": "fair-dice-disjoint-density-lift-v1",
            "n": m+1,
            "distinguished_letter": m,
            "distinguished_faces": K,
            "source_model_sha256": digest,
            "source_model_path": str(model_path),
            "mass_denominator_hex": hex(denominator),
            "old_die_faces_hex": hex(faces*denominator),
            "base_word": base,
            "outer_recipe": {
                "event_order": "construct_cells from verify_global_model.py",
                "cell": "base word, with each letter j repeated mass_denominator * cell_mass[j] times",
                "atom": "one occurrence of distinguished_letter",
                "face_labels": "successive positive integers in the resulting word"
            },
            "scope": "Exact finite grammar and moment certificate; fairness follows from the proved insertion and disjoint-density lemmas. Full n! orders are not enumerated."
        }
        destination.write_text(json.dumps(obj, indent=2)+"\n")
    else:
        obj = json.loads(destination.read_text())
        assert obj["format"] == "fair-dice-disjoint-density-lift-v1"
        assert obj["source_model_sha256"] == digest
        assert obj["n"] == m+1 and obj["distinguished_letter"] == m
        assert obj["distinguished_faces"] == K
        denominator = int(obj["mass_denominator_hex"], 16)
        faces, moments = verify_base(obj["base_word"], m)
        assert int(obj["old_die_faces_hex"], 16) == faces*denominator
    mass_count = check_finite_masses(events, denominator, m)
    # Printing metadata only avoids dumping an enormous exact face count.
    print(json.dumps({
        "mode": args.mode, "n": m+1, "distinguished_faces": K,
        "other_dice_equal": True, "old_die_face_count_bits": (faces*denominator).bit_length(),
        "mass_denominator_bits": denominator.bit_length(),
        "base_insertion_moments_verified": moments,
        "density_correction_moments_verified": m*m,
        "distinct_positive_rational_masses_checked": mass_count,
        "finite_certificate": str(destination), "certificate_bytes": destination.stat().st_size,
        "full_orders_enumerated": 0
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
