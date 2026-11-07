#!/usr/bin/env python3
"""Attack finite phase rigidity using complete short-vector enumeration.

Samples canonical, distinct isotropic triples, including random large primes,
triples perpendicular to small fixed normals, and known reflective classes.
LLL only supplies a basis: its exact determinant and congruences are checked.
Cauchy bounds from the rational inverse basis certify every enumerated shell.
Candidate residues are obtained from necessary opposite-phase equalities;
each is then checked with the independent cyclotomic zero test.

This is a sampled search, not an exhaustive census or a universal proof.
The 500,000-point box cap is reported explicitly for every skipped case.
"""
import argparse, hashlib, json, random, math, time
from pathlib import Path
from itertools import product
import paley_spinor_scan as s
from flint import fmpz_mat
import sympy

def norm(v):
    return sum((x * x for x in v))

def balanced(p, ph):
    return all((n == ph[(e + 3 * p) % (6 * p)] for (e, n) in ph.items()))

def shells_exact(p, v):
    """Enumerate complete shells using inverse-basis Cauchy bounds."""
    assert v[0] == 1 and norm(v) % p == 0
    B = [list(map(int, row)) for row in fmpz_mat([[1, v[1], v[2]], [0, p, 0], [0, 0, p]]).lll().tolist()]
    assert abs(s.determinant(B)) == p * p
    assert all(((b[1] - b[0] * v[1]) % p == 0 and (b[2] - b[0] * v[2]) % p == 0 for b in B))
    inv = s.inverse_matrix(s.transpose(B))
    ds = [sum((x * x for x in row)) for row in inv]
    bound = 2 * max(map(norm, B))
    for attempt in range(6):
        ranges = [math.isqrt((bound * d).numerator // (bound * d).denominator) for d in ds]
        volume = math.prod((2 * r + 1 for r in ranges))
        if volume > 500000:
            return None
        shells = {}
        roots = []
        for x in product(*(range(-r, r + 1) for r in ranges)):
            w = tuple((sum((x[j] * B[j][i] for j in range(3))) for i in range(3)))
            n = norm(w)
            if not 0 < n <= bound:
                continue
            assert n % p == 0
            if n in (p, 2 * p):
                roots.append(s.ShortProjectiveRoot(w[0] % p, w, n // p))
            if all((y % 3 for y in w)):
                shells.setdefault(n, []).append(w)
        shells = [(n, tuple(sorted(vs))) for (n, vs) in sorted(shells.items())]
        rb = {}
        qb = {}
        span = None
        perfect = None
        for (k, (n, vs)) in enumerate(shells, 1):
            for w in vs:
                s.add_to_rational_row_basis(rb, w)
                s.add_to_rational_row_basis(qb, s.symmetric_square_coordinates(w))
            if len(rb) == 3 and span is None:
                span = k
            if len(qb) == 6:
                perfect = k
                break
        if perfect:
            return (shells[:perfect], span, roots, {'bound': bound, 'coordinate_bounds': ranges, 'box_size': volume, 'basis': B})
        bound *= 2
    raise AssertionError('no perfect cutoff')

def candidate_residues(lattice, shells):
    """Any cancelling residue must give each vector an opposite partner."""
    p = lattice.p
    best = None
    for (n, vs) in shells:
        phases = {w: (s.dual_character_compressed_phase(lattice, 0, w), s.dual_residue_phase_step(lattice, w)) for w in vs}
        for (w, (a, b)) in phases.items():
            candidates = set()
            universal = False
            for (z, (c, d)) in phases.items():
                delta = 3 * p - c + a
                if delta % 6:
                    continue
                coef = (d - b) // 6 % p
                rhs = delta // 6 % p
                if coef:
                    candidates.add(rhs * pow(coef, -1, p) % p)
                elif rhs == 0:
                    universal = True
                    break
            if not universal and (best is None or len(candidates) < len(best)):
                best = candidates
        if best is not None:
            break
    if best is None:
        return set(range(p))
    return best

def zeros(lattice, shells):
    p = lattice.p
    out = set()
    tests = 0
    for r in candidate_residues(lattice, shells):
        ok = True
        for (n, vs) in shells:
            ph = s.compressed_dual_shell_phase_counter(lattice, r, vs)
            assert all((ph[e] == ph[(3 * p - e) % (6 * p)] for e in ph))
            a = balanced(p, ph)
            b = s.six_p_cyclotomic_sum_is_zero(p, ph)
            assert a == b
            tests += 1
            if not a:
                ok = False
                break
        if ok:
            out.add(r)
    return (out, tests)

def run(p, v):
    v = tuple(sorted((min(x % p, p - x % p) for x in v)))
    assert sympy.isprime(p) and p >= 5 and (0 < v[0] < v[1] < v[2]) and (2 * v[2] < p)
    data = shells_exact(p, v)
    if data is None:
        return {'p': p, 'v': v, 'skipped': 'box cap'}
    (shells, span, roots, certificate) = data
    lattice = s.restricted_lattice(p, v)
    expected = {s.projective_root_target(root, lattice)[1] for root in roots}
    (z1, t1) = zeros(lattice, shells[:span])
    (z2, t2) = zeros(lattice, shells)
    result = {'p': p, 'v': v, 'span_shells': span, 'perfect_shells': len(shells), 'expected': sorted(expected), 'span_zeros': sorted(z1), 'perfect_zeros': sorted(z2), 'phase_tests': t1 + t2, 'span_norm': shells[span - 1][0], 'perfect_norm': shells[-1][0], 'certificate': certificate}
    checks = []
    for residue in sorted(z2):
        partners = s.unique_phase_reversing_partners(lattice, residue, shells)
        linear = s.phase_partner_linear_map(partners) if partners else None
        checks.append({'residue': residue, 'unique_partners': partners is not None, 'linear_map': linear is not None, 'structure': s.phase_partner_map_structure(lattice, linear) if linear else None})
    result['coherence_checks'] = checks
    if z1 != expected or z2 != expected:
        result['shells'] = shells
        result['mismatch'] = True
    return result
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=20261101)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    cases = []
    for (p, v) in [(71, (1, 4, 14)), (1439, (1, 63, 391)), (1523, (1, 147, 468))]:
        if norm(v) % p == 0:
            cases.append((p, v))
    for lo in [3000, 10000, 100000, 1000000, 100000000]:
        for trial in range(40):
            p = int(sympy.nextprime(rng.randrange(lo, 2 * lo)))
            while True:
                j = rng.randrange(2, p - 1)
                ks = sympy.sqrt_mod(-1 - j * j, p, all_roots=True)
                if ks:
                    k = int(ks[0])
                    if k and len({1, min(j, p - j), min(k, p - k)}) == 3:
                        break
            cases.append((p, (1, j, k)))
    for axis in [(1, 1, 2), (1, 2, 2), (1, 2, 3), (1, 1, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]:
        (a, b, c) = axis
        for trial in range(15):
            p = int(sympy.nextprime(rng.randrange(3000, 30000)))
            roots = sympy.sqrt_mod(-norm(axis), p, all_roots=True)
            if not roots:
                continue
            j = (-a * b + c * int(roots[0])) * pow(b * b + c * c, -1, p) % p
            k = -(a + b * j) * pow(c, -1, p) % p
            if j and k and (len({1, min(j, p - j), min(k, p - k)}) == 3):
                cases.append((p, (1, j, k)))
    for scale in [30, 300, 3000]:
        for trial in range(30):
            while True:
                a = rng.randrange(1, scale)
                b = rng.randrange(a + 1, 2 * scale)
                p = a * a + a * b + b * b
                if sympy.isprime(p):
                    break
            raw = (a, b, a + b)
            inverse = pow(a, -1, p)
            cases.append((p, tuple((x * inverse % p for x in raw))))
    results = []
    started = time.time()
    for (i, (p, v)) in enumerate(cases):
        r = run(p, v)
        results.append(r)
        if i % 25 == 0 or r.get('mismatch'):
            print(f'checked {i + 1}/{len(cases)} cases; p={p}', flush=True)
        if r.get('mismatch'):
            print(json.dumps(r), flush=True)
            break
    completed = [r for r in results if not r.get('skipped')]
    report = {'date': '2026-11-01', 'seed': args.seed, 'attempted': len(results), 'completed': len(completed), 'skipped': len(results) - len(completed), 'largest_completed_prime': max((r['p'] for r in completed)), 'mismatches': sum((bool(r.get('mismatch')) for r in completed)), 'coherence_checks': sum((len(r['coherence_checks']) for r in completed)), 'coherence_failures': sum((not (c['unique_partners'] and c['linear_map'] and all(c['structure'])) for r in completed for c in r['coherence_checks'])), 'phase_tests': sum((r['phase_tests'] for r in completed)), 'sample_not_census': True, 'results': results, 'elapsed_seconds': time.time() - started, 'sha256': {Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'paley_spinor_scan.py': hashlib.sha256(Path(__file__).with_name('paley_spinor_scan.py').read_bytes()).hexdigest()}}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print({k: v for (k, v) in report.items() if k not in ('results', 'sha256')})
