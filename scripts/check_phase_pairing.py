#!/usr/bin/env python3
"""Independent controls for unbounded phase balance and the fast dual search."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import attack_phase_rigidity as attack
import paley_spinor_scan as oracle


def check():
    rng = random.Random(20261101)
    synthetic = 0
    maximum_weight_ratio = 0
    for p in (5, 7, 11, 13, 17, 31):
        for trial in range(40):
            phases = Counter()
            for _ in range(30):
                a = rng.randrange(2 * p)
                multiplicity = rng.randrange(1, 1000)
                # Enforce a -> p-a, the actual twisted antipodal law.
                phases[3 * a] += multiplicity
                phases[3 * ((p - a) % (2 * p))] += multiplicity
                if trial % 2 == 0:
                    phases[3 * ((a + p) % (2 * p))] += multiplicity
                    phases[3 * ((-a) % (2 * p))] += multiplicity
            assert all(phases[e] == phases[(3 * p - e) % (6 * p)] for e in phases)
            exact_zero = oracle.six_p_cyclotomic_sum_is_zero(p, phases)
            assert exact_zero == attack.balanced(p, phases)
            synthetic += 1
            maximum_weight_ratio = max(maximum_weight_ratio, sum(phases.values()) // (2 * p))
        # Two p-gons have even weight 2p and cancel without opposite pairs.
        # They violate the twisted antipodal hypothesis.
        polygons = Counter({6 * j: 2 for j in range(p)})
        assert oracle.six_p_cyclotomic_sum_is_zero(p, polygons)
        assert not attack.balanced(p, polygons)
        assert any(polygons[e] != polygons[(3 * p - e) % (6 * p)] for e in polygons)

    # Antipodal balance and a perfect generating set alone do not imply a
    # common linear symmetry. These phases are deliberately NOT Watson phases.
    p = 11
    phase = {}
    def negative(v):
        return tuple(-x for x in v)
    def assign_pair(u, v, a):
        phase[u] = 3 * a
        phase[v] = 3 * (a + p)
        phase[negative(u)] = 3 * (p - a) % (6 * p)
        phase[negative(v)] = -3 * a % (6 * p)
    e1, e2, e3 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    assign_pair(e1, e2, 1)
    phase[e3], phase[negative(e3)] = 0, 3 * p
    assign_pair((1, 1, 0), (1, -1, 0), 2)
    assign_pair((1, 0, 1), (1, 0, -1), 3)
    assign_pair((0, 1, 1), (0, 1, -1), 4)
    assert all(phase[negative(v)] == (3 * p - e) % (6 * p)
               for v, e in phase.items())
    partners = {}
    tensor_basis = {}
    for n in (1, 2):
        vectors = [v for v in phase if attack.norm(v) == n]
        counts = Counter(phase[v] for v in vectors)
        assert oracle.six_p_cyclotomic_sum_is_zero(p, counts)
        for v in vectors:
            candidates = [w for w in vectors if (phase[w] - phase[v]) % (6 * p) == 3 * p]
            assert len(candidates) == 1
            partners[v] = candidates[0]
            oracle.add_to_rational_row_basis(tensor_basis, oracle.symmetric_square_coordinates(v))
    assert len(tensor_basis) == 6
    assert oracle.phase_partner_linear_map(partners) is None

    comparisons = []
    for p, normal in ((7, (1, 2, 3)), (13, (1, 3, 4)), (31, (1, 5, 6)),
                      (71, (1, 4, 14)), (71, (1, 11, 34)),
                      (1439, (1, 63, 391)), (1523, (1, 147, 468))):
        shells, span, roots, certificate = attack.shells_exact(p, normal)
        lattice = oracle.restricted_lattice(p, normal)
        old_shells, omitted = oracle.first_dual_character_shells(lattice, len(shells), 2)
        assert len(old_shells) == len(shells) and old_shells[-1][0] < omitted
        assert shells == old_shells
        assert {r.vector for r in roots} == {
            r.vector for r in oracle.short_projective_roots(p, normal)}
        for prefix in (shells[:span], shells):
            fast, _ = attack.zeros(lattice, prefix)
            exhaustive = oracle.dual_shell_common_zero_residues(lattice, prefix)
            assert fast == exhaustive
        comparisons.append({"prime": p, "normal": normal,
                            "span_shells": span, "perfect_shells": len(shells),
                            "complete_enumerations_agree": True,
                            "all_residue_zero_sets_agree": True})
    return {"date": "2026-11-01", "synthetic_cases": synthetic,
            "largest_weight_over_2p_floor": maximum_weight_ratio,
            "negative_controls": 6,
            "nonlinear_pairing_control": {"prime": 11, "vectors": len(phase),
                "perfect_tensor_rank": 6, "contains_integer_basis": True,
                "unique_opposite_partners": True, "common_linear_map": False,
                "uses_actual_Watson_phases": False},
            "oracle_comparisons": comparisons,
            "all_checks_passed": True,
            "sha256": {Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "attack_phase_rigidity.py": hashlib.sha256(Path(attack.__file__).read_bytes()).hexdigest(),
                       "paley_spinor_scan.py": hashlib.sha256(Path(oracle.__file__).read_bytes()).hexdigest()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = check()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
