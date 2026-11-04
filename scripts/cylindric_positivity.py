#!/usr/bin/env python3
"""Exact bounded cylindric series and Warnaar polynomials (coprime profiles).

Uses conjugate-row heights, not the conjectured positivity or the HJO identity.
The outgoing convention is lambda[i][j] >= lambda[i+1][j+c[i]].

Every height slice h satisfies h[i+1] <= h[i]+c[i]. Its slack vector
s[i]=h[i]+c[i]-h[i+1] is a weak composition of sum(c). Each slack has a
unique height vector u with min(u)=0, and h=u+k*(1,...,1), k>=0.
For successive slices u,v, their offsets satisfy k-l >= D(u,v), where
D(u,v)=max_i(v[i]-u[i]) >= 0. Summing the offsets geometrically gives

 C_{c,<=N}(q) = B_N(q) / product_{j=1}^N (1-q^(r*j)),
 B_N = sum_{u_1,...,u_N} q^(sum |u_t| + r*sum_{t<N} t*D(u_t,u_{t+1})).

This finite transfer computes the entire numerator. Polynomiality is checked
by exact division, never inferred from a zero tail in a truncated series.
Then F_N=(q;q)_N*C_{c,<=N} and Q_N is obtained by Gaussian inversion.
These are computations, not Lean proofs. Requires python-flint.
"""

import argparse
import hashlib
import json
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
from time import perf_counter

from flint import fmpz_poly


def compositions(total, length):
    if total < 0 or length < 1:
        raise ValueError('weak compositions require total>=0 and length>=1')
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def canonical(profile):
    return min(profile[i:] + profile[:i] for i in range(len(profile)))


def slices(profile):
    """All admissible normalized slices, one per slack composition."""
    rank = len(profile)
    result = []
    for slack in compositions(sum(profile), rank):
        heights = [0]
        for i in range(rank - 1):
            heights.append(heights[-1] + profile[i] - slack[i])
        floor = min(heights)
        u = tuple(h - floor for h in heights)
        assert all(u[(i + 1) % rank] <= u[i] + profile[i] for i in range(rank))
        result.append(u)
    assert len(set(result)) == len(result)
    return result


@lru_cache(None)
def monomial(degree):
    return fmpz_poly([0] * degree + [1])


@lru_cache(None)
def gaussian(n, k):
    if k < 0 or k > n:
        return fmpz_poly([])
    if k == 0 or k == n:
        return fmpz_poly([1])
    return gaussian(n - 1, k) + gaussian(n - 1, k - 1) * monomial(n - k)


def exact_polynomials(profile, maximum):
    """Return complete B_N, F_N, Q_N; reject any failed exact division."""
    if not profile or min(profile) < 0 or sum(profile) == 0:
        raise ValueError('profile must be nonnegative, nonempty, with positive level')
    rank, level = len(profile), sum(profile)
    if gcd(rank, level) != 1:
        raise ValueError('this normalization requires coprime rank and level')
    if maximum < 0:
        raise ValueError('maximum must be nonnegative')
    states = slices(profile)
    weights = [sum(u) for u in states]
    jumps = [[max(v[i] - u[i] for i in range(rank)) for u in states] for v in states]
    one = fmpz_poly([1])
    b_values, f_values, q_values = [one], [one], [one]
    vector = [monomial(w) for w in weights]
    divisor = one
    for n in range(1, maximum + 1):
        if n > 1:
            vector = [sum((p * monomial(rank * (n - 1) * jump + weight)
                           for p, jump in zip(vector, row)), fmpz_poly([]))
                      for row, weight in zip(jumps, weights)]
        b = sum(vector, fmpz_poly([]))
        divisor *= sum((monomial(n * j) for j in range(rank)), fmpz_poly([]))
        f, remainder = divmod(b, divisor)
        if remainder:
            raise ArithmeticError(f'F_{n} is not polynomial for {profile}: {remainder}')
        q = f - sum((gaussian(n, k) * q_values[k] for k in range(n)), fmpz_poly([]))
        b_values.append(b)
        f_values.append(f)
        q_values.append(q)
    return b_values, f_values, q_values


def summary(p):
    coeff = [int(x) for x in p.coeffs()]
    support = [i for i, x in enumerate(coeff) if x]
    return {'degree': int(p.degree()), 'valuation': min(support) if support else None,
            'coefficient_sum': sum(coeff), 'negative_coefficients': [[i, x] for i, x in enumerate(coeff) if x < 0],
            'coefficient_sha256': hashlib.sha256(json.dumps(coeff, separators=(',', ':')).encode()).hexdigest(),
            'initial_coefficients': coeff[:20]}


def bounded_prefix(profile, maximum, degree):
    """Independent exhaustive enumeration of actual row partitions by volume.

    The degree cap bounds every row length, so no omitted row can contribute.
    Used only for small validation cases; does not use slices or transfer.
    """
    @lru_cache(None)
    def partitions(size, largest):
        if size == 0:
            return ((),)
        return tuple((first,) + tail for first in range(1, min(size, largest) + 1)
                     for tail in partitions(size - first, first))

    rows = {size: partitions(size, maximum) for size in range(degree + 1)}
    counts = [0] * (degree + 1)
    rank = len(profile)
    for total in range(degree + 1):
        for sizes in compositions(total, rank):
            for row_tuple in product(*(rows[size] for size in sizes)):
                valid = True
                for i, shift in enumerate(profile):
                    left, right = row_tuple[i], row_tuple[(i + 1) % rank]
                    if any((left[j] if j < len(left) else 0) < right[j + shift]
                           for j in range(max(0, len(right) - shift))):
                        valid = False
                        break
                counts[total] += valid
    return counts


def numerator_to_prefix(b, rank, maximum, degree):
    coeff = [int(b[i]) for i in range(degree + 1)]
    for j in range(1, maximum + 1):
        step = rank * j
        for k in range(step, degree + 1):
            coeff[k] += coeff[k - step]
    return coeff


def validate():
    checks = []
    # HJO Section 1.2: trefoil finite Gaussian sum for every tested N.
    b, f, q = exact_polynomials((1, 2), 8)
    for n in range(9):
        assert f[n] == sum((gaussian(n, m) * monomial(m * m) for m in range(n + 1)), fmpz_poly([]))
        assert q[n] == monomial(n * n)
    checks.append('trefoil F_N Gaussian identity and Q_N=q^(N^2), N=0..8')
    # HJO Section 10 and Warnaar Section 8: independent published benchmarks.
    _, _, q = exact_polynomials((2, 2, 2, 1), 1)
    assert q[1] == fmpz_poly([0, 3, 5, 5, 5, 4, 3, 2, 1, 1])
    checks.append('Warnaar profile (2,2,2,1), full Q_1 polynomial')
    for profile in [(1, 2), (0, 3), (0, 1, 3), (0, 0, 1, 4), (1, 1, 1, 2)]:
        b, _, _ = exact_polynomials(profile, 3)
        for n in range(1, 4):
            assert numerator_to_prefix(b[n], len(profile), n, 10) == bounded_prefix(profile, n, 10)
        checks.append(f'actual row enumeration through volume 10, N=1..3, profile {profile}')
    return checks


def scan(rank, level, maximum):
    if rank < 1 or level < 1 or maximum < 0 or gcd(rank, level) != 1:
        raise ValueError('require positive coprime rank and level, and maximum>=0')
    records = []
    all_f = {}
    profiles = sorted({canonical(c) for c in compositions(level, rank)})
    balanced = canonical(tuple((i + 1) * level // rank - i * level // rank for i in range(rank)))
    expected_base = comb(rank + level, rank) // (rank + level) - 1
    for profile in profiles:
        started = perf_counter()
        _, fs, qs = exact_polynomials(profile, maximum)
        all_f[profile] = fs
        values = [summary(p) for p in qs]
        assert all(v['coefficient_sum'] == expected_base ** n for n, v in enumerate(values))
        records.append({'profile': profile, 'balanced_rotation': profile == balanced, 'Q': values})
        print(f'{profile}: N<={maximum}, degrees={[v["degree"] for v in values]}, '
              f'negative={sum(len(v["negative_coefficients"]) for v in values)}, '
              f'{perf_counter()-started:.2f}s', flush=True)
    # Independent exact identity from the Corteel-Welsh inclusion-exclusion
    # recurrence: F_N(c)=(1-q^N)F_{N-1}(c)+sum_J (-1)^(|J|-1)q^(N|J|)F_N(c(J)).
    recurrence_checks = 0
    for c in profiles:
        positive = [i for i in range(rank) if c[i] > 0]
        targets = []
        for mask in range(1, 1 << len(positive)):
            selected = {positive[j] for j in range(len(positive)) if mask & (1 << j)}
            target = canonical(tuple(c[i] - (i in selected) + ((i - 1) % rank in selected)
                                     for i in range(rank)))
            targets.append((target, len(selected)))
        for n in range(1, maximum + 1):
            rhs = (fmpz_poly([1]) - monomial(n)) * all_f[c][n - 1]
            for target, size in targets:
                rhs += (-1) ** (size - 1) * monomial(n * size) * all_f[target][n]
            assert all_f[c][n] == rhs, (c, n, 'Corteel-Welsh recurrence failed')
            recurrence_checks += 1
    return {'rank': rank, 'level': level, 'maximum_N': maximum,
            'cyclic_profiles': len(profiles), 'Q_at_one_base': expected_base,
            'exact_Corteel_Welsh_recurrence_checks': recurrence_checks,
            'records': records}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, default=4)
    parser.add_argument('--level', type=int, default=5)
    parser.add_argument('--maximum', type=int, default=6)
    parser.add_argument('--validate', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    checks = validate() if args.validate else []
    result = scan(args.rank, args.level, args.maximum)
    result.update({'status': 'Exact finite polynomial computations; no all-N positivity theorem',
                   'method': 'normalized conjugate slices; complete rational numerator; exact division',
                   'validation': checks,
                   'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
