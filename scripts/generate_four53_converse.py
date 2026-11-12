#!/usr/bin/env python3
"""Generate exact witnesses for the fixed modulus-53 four-factor converse.

The generated Lean file checks every coefficient in the kernel; the Python
search is not trusted by Lean. The zero direction uses the plane theorem.
"""
import argparse
from pathlib import Path
import re
from quintuple_vanishing_scan import product_coefficients

ROOT = Path(__file__).resolve().parents[1]


def generate():
    p, indices, zeros = 53, (5, 2, 7, 9), {29, 31, 36, 38}
    coefficients = product_coefficients(p, indices, 448)
    witnesses = {}
    for r in range(p):
        if r in zeros:
            continue
        for n in range(9):
            if p*n+r > 448:
                break
            if coefficients.get(p*n+r, 0):
                witnesses[r] = (n, p*n+r, coefficients[p*n+r])
                break
        else:
            raise AssertionError(f"missing witness in residue {r}")
    assert len(witnesses) == 49
    # Reuse the already established short-box proof pattern, replacing every
    # modulus-dependent bound and index. Lean independently checks this proof.
    template = (ROOT/'RamanujanTau/MultiQuintupleFourFortyOneConverse.lean').read_text()
    prefix = template[:template.index('set_option maxHeartbeats 0 in')]
    prefix = prefix.replace('MultiQuintupleFourFortyOne', 'MultiQuintupleFourPlane')
    prefix = prefix.replace('41', '53').replace('430', '896').replace('215', '448')
    prefix = prefix.replace('53 1 4 5 9', '53 5 2 7 9')
    prefix = prefix.replace('quintupleSpecialized 53 1', 'quintupleSpecialized 53 5')
    prefix = prefix.replace('quintupleSpecialized 53 4', 'quintupleSpecialized 53 2')
    # The third factor was formerly 5; replace it separately after the second.
    prefix = prefix.replace('quintupleSpecialized 53 2 *\n      quintupleSpecialized 53 5',
                            'quintupleSpecialized 53 2 *\n      quintupleSpecialized 53 7')
    for idx, old, new in ((1, 1, 5), (2, 4, 2), (3, 5, 7)):
        prefix = prefix.replace(f'nonneg b{idx} 53 {old} n{idx}',
                                f'nonneg b{idx} 53 {new} n{idx}')
        prefix = prefix.replace(f'short_index53 b{idx} {old} n{idx}',
                                f'short_index53 b{idx} {new} n{idx}')
    out = [prefix]
    for r, (n, k, value) in witnesses.items():
        out.append(f'''set_option maxHeartbeats 0 in
private theorem coefficient53_{r} : four53ShortCoeff {k} = ({value} : ℤ) := by
  decide +kernel

''')
    product = '''(quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9)'''
    out.append(f'''/-- Every other residue has a nonzero coefficient within eight progression steps. -/
theorem four53_residue_or_witness (R : ℕ) (hR : R < 53) :
    (R=29 ∨ R=31 ∨ R=36 ∨ R=38) ∨
    ∃ N : ℕ, N ≤ 8 ∧ coeff (53*N+R) {product} ≠ 0 := by
  interval_cases R
''')
    for r in range(p):
        if r in zeros:
            out.append('  · left; norm_num\n')
        else:
            n, k, value = witnesses[r]
            out.append(f'''  · right
    refine ⟨{n}, by norm_num, ?_⟩
    rw [coeff_four53_eq_short _ (by norm_num)]
    exact ne_of_eq_of_ne coefficient53_{r} (by norm_num)
''')
    out.append(f'''
/-- Full persistent-vanishing classification for this fixed product at 53. -/
theorem four53_persistent_vanishing_iff (R : ℕ) (hR : R < 53) :
    (∀ N : ℕ, coeff (53*N+R) {product} = 0) ↔
    R=29 ∨ R=31 ∨ R=36 ∨ R=38 := by
  constructor
  · intro hz
    rcases four53_residue_or_witness R hR with hr | ⟨N,_,hn⟩
    · exact hr
    · exact False.elim (hn (hz N))
  · intro hr N
    exact coeff_fourPlane_53 R N hr

/-- Checking the first nine terms is an exact test for this fixed product. -/
theorem four53_finite_test_iff (R : ℕ) (hR : R < 53) :
    (∀ N : ℕ, coeff (53*N+R) {product} = 0) ↔
    (∀ N : ℕ, N ≤ 8 → coeff (53*N+R) {product} = 0) := by
  constructor
  · exact fun h N _ => h N
  · intro h
    apply (four53_persistent_vanishing_iff R hR).mpr
    rcases four53_residue_or_witness R hR with hr | ⟨N,hle,hn⟩
    · exact hr
    · exact False.elim (hn (h N hle))

end Ramanujan.MultiQuintuple
''')
    source = ''.join(out)
    start = source.index('private lemma short_index53')
    end = source.index('\n\nset_option maxHeartbeats 0 in')
    fast = source[start:end]
    for old, new in [('short_index53', 'short_index53_one'),
                     ('mem_short_box53', 'mem_short_box53_one'),
                     ('four53ShortCoeff', 'four53SmallCoeff'),
                     ('coeff_four53_eq_short', 'coeff_four53_eq_small'),
                     ('noncomputable def ', 'private noncomputable def '),
                     ('\nlemma coeff_four53', '\nprivate lemma coeff_four53'),
                     ('≤ 896', '≤ 438'), ('≤ 448', '≤ 219'),
                     ('natAbs ≤ 2', 'natAbs ≤ 1'),
                     ('-2 ≤ n ∧ n ≤ 2', '-1 ≤ n ∧ n ≤ 1'),
                     ('n ≤ -3 ∨ 3 ≤ n', 'n ≤ -2 ∨ 2 ≤ n'),
                     ('(n+3)', '(n+2)'), ('(n-3)', '(n-2)'),
                     ('quadBox 1', 'quadBox 0'),
                     ('mem_quintBranchBox_of_natAbs_le 1', 'mem_quintBranchBox_of_natAbs_le 0')]:
        fast = fast.replace(old, new)
    def accelerate(hit):
        residue, degree = int(hit[2]), int(hit[3])
        if residue == 0 or degree > 219:
            return hit[0]
        return (hit[1] + f'  rw [← coeff_four53_eq_short {degree} (by norm_num),'
                f'coeff_four53_eq_small {degree} (by norm_num)]\n  decide +kernel')
    source = re.sub(r'(private theorem coefficient53_(\d+) : four53ShortCoeff (\d+) = [^\n]+ := by\n)  decide \+kernel',
                    accelerate, source)
    marker = re.search(r'private theorem coefficient53_0 :[^\n]+\n  decide \+kernel\n', source)
    assert marker
    index = marker.end()
    return (source[:index] + '\n-- A smaller proved coefficient box keeps the numerical checks inexpensive.\n'
            + fast + '\n' + source[index:])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = ROOT/'RamanujanTau/MultiQuintupleFourFiftyThreeConverse.lean'
    source = generate()
    if args.check:
        if target.read_text() != source:
            raise SystemExit(f'Stale generated file: {target}')
        print('Modulus-53 Lean coefficient certificates reproduced exactly.')
    else:
        target.write_text(source)
        print(target)
