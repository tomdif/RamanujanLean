/-
# Local-support obstructions for triple quintuple products

Projective reflections explain cancellation after branch points occur.  This
file isolates the logically earlier question: which coefficient residues can
occur at all?

Let `d` be an odd divisor of the product modulus and also divide
`3*i`, `3*j`, and `3*k`.  Modulo `d`, the bilateral indices disappear from
the three Watson exponents.  A contributing exponent can therefore lie only
in one of the eight subset-sum classes

  `b1*i + b2*j + b3*k`,  with `bs in {0,1}`.

We prove the resulting exact coefficient sieve and its progression-wise
version for the actual stabilized Pochhammer product.  Taking `d` to be the
common divisor of the modulus and the three numbers `3*i,3*j,3*k` recovers
the full elementary local obstruction.  For a prime modulus `p >= 5` and
nonzero canonical indices this divisor is one, explaining why the sieve
disappears in the primitive projective-root regime.
-/
import RamanujanTau.MultiQuintupleRootVanishingClassification

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- The subset-sum residue attached to three Watson branch bits. -/
def tripleBranchSubsetResidue
    (b1 b2 b3 : Bool) (i j k : ℤ) : ℤ :=
  i * (if b1 then 1 else 0) +
    j * (if b2 then 1 else 0) +
    k * (if b3 then 1 else 0)

/-- A coefficient degree lies in one of the eight locally attainable branch
classes modulo `d`. -/
def TripleLocalReachable (d i j k K : ℕ) : Prop :=
  ∃ b1 b2 b3 : Bool,
    (d : ℤ) ∣ (K : ℤ) - tripleBranchSubsetResidue b1 b2 b3 i j k

/-- An odd divisor can be cancelled from twice an integer. -/
lemma int_dvd_of_dvd_two_mul_of_odd
    (d z : ℤ) (hdodd : Odd d) (hdiv : d ∣ 2 * z) : d ∣ z := by
  obtain ⟨a, ha⟩ := hdodd
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨z - a * q, ?_⟩
  linear_combination -z * ha - a * hq

/-- Once `d` divides `3*i`, `3*j`, and `3*k`, the bilateral-index part of
the linear residue is zero modulo `d`; only the three branch bits remain. -/
lemma tripleLinearResidue_sub_subset_dvd
    (b1 b2 b3 : Bool) (d i j k n1 n2 n3 : ℤ)
    (hdi : d ∣ 3 * i) (hdj : d ∣ 3 * j) (hdk : d ∣ 3 * k) :
    d ∣ tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 -
      tripleBranchSubsetResidue b1 b2 b3 i j k := by
  obtain ⟨qi, hqi⟩ := hdi
  obtain ⟨qj, hqj⟩ := hdj
  obtain ⟨qk, hqk⟩ := hdk
  refine ⟨qi * n1 + qj * n2 + qk * n3, ?_⟩
  simp only [tripleLinearResidue, tripleBranchSubsetResidue]
  linear_combination n1 * hqi + n2 * hqj + n3 * hqk

/-- Every bilateral branch point contributing to `q^K` satisfies the local
eight-class sieve. -/
lemma tripleLocalReachable_of_tripleQuintExp2
    (b1 b2 b3 : Bool) (d p i j k K : ℕ) (n1 n2 n3 : ℤ)
    (hdodd : Odd d)
    (hdp : d ∣ p) (hdi : d ∣ 3 * i) (hdj : d ∣ 3 * j) (hdk : d ∣ 3 * k)
    (hexp : tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 = 2 * (K : ℤ)) :
    TripleLocalReachable d i j k K := by
  have hdoddz : Odd (d : ℤ) := by exact_mod_cast hdodd
  have hdpz : (d : ℤ) ∣ (p : ℤ) := by exact_mod_cast hdp
  have hdiz : (d : ℤ) ∣ 3 * (i : ℤ) := by exact_mod_cast hdi
  have hdjz : (d : ℤ) ∣ 3 * (j : ℤ) := by exact_mod_cast hdj
  have hdkz : (d : ℤ) ∣ 3 * (k : ℤ) := by exact_mod_cast hdk
  let linear := tripleLinearResidue b1 b2 b3 i j k n1 n2 n3
  let subset := tripleBranchSubsetResidue b1 b2 b3 i j k
  obtain ⟨u, hu⟩ := tripleQuintExp2_eq_two_residue_add_p_mul
    b1 b2 b3 p i j k n1 n2 n3
  obtain ⟨qp, hqp⟩ := hdpz
  have htwice : (d : ℤ) ∣ 2 * ((K : ℤ) - linear) := by
    refine ⟨qp * u, ?_⟩
    dsimp [linear]
    linear_combination -hexp + hu + u * hqp
  have hcoefficient : (d : ℤ) ∣ (K : ℤ) - linear :=
    int_dvd_of_dvd_two_mul_of_odd (d : ℤ) ((K : ℤ) - linear) hdoddz htwice
  have hindices : (d : ℤ) ∣ linear - subset := by
    dsimp [linear, subset]
    exact tripleLinearResidue_sub_subset_dvd b1 b2 b3 d i j k n1 n2 n3
      hdiz hdjz hdkz
  refine ⟨b1, b2, b3, ?_⟩
  obtain ⟨q1, hq1⟩ := hcoefficient
  obtain ⟨q2, hq2⟩ := hindices
  refine ⟨q1 + q2, ?_⟩
  dsimp [subset] at hq2 ⊢
  linear_combination hq1 + hq2

/-- **Exact local-support coefficient sieve.**

If a degree misses all eight locally attainable branch classes, the
coefficient of the actual triple Pochhammer product is zero. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_not_localReachable
    (d p i j k K : ℕ)
    (hdodd : Odd d)
    (hdp : d ∣ p) (hdi : d ∣ 3 * i) (hdj : d ∣ 3 * j) (hdk : d ∣ 3 * k)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hmiss : ¬TripleLocalReachable d i j k K) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K
    hi hpi hj hpj hk hpk]
  apply Finset.sum_eq_zero
  intro x hx
  rw [pointContribution]
  split_ifs with hexp
  · exfalso
    apply hmiss
    exact tripleLocalReachable_of_tripleQuintExp2
      (pointB1 x) (pointB2 x) (pointB3 x) d p i j k K
      (pointN1 x) (pointN2 x) (pointN3 x)
      hdodd hdp hdi hdj hdk (by simpa [pointTripleExp2] using hexp)
  · rfl

/-- **Progression-wise local-support vanishing.**

Since `d ∣ p`, the locally attainable class of `p*N+R` is independent of
`N`.  Missing the eight subset sums once therefore kills the full
progression. -/
theorem persistentTripleVanishing_of_not_localReachable
    (d p i j k R : ℕ)
    (hdodd : Odd d)
    (hdp : d ∣ p) (hdi : d ∣ 3 * i) (hdj : d ∣ 3 * j) (hdk : d ∣ 3 * k)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hmiss : ¬TripleLocalReachable d i j k R) :
    PersistentTripleVanishing p i j k R := by
  intro N
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_not_localReachable
    d p i j k (p * N + R) hdodd hdp hdi hdj hdk
    hi hpi hj hpj hk hpk
  rintro ⟨b1, b2, b3, hreach⟩
  apply hmiss
  refine ⟨b1, b2, b3, ?_⟩
  have hdpz : (d : ℤ) ∣ (p : ℤ) := by exact_mod_cast hdp
  obtain ⟨qp, hqp⟩ := hdpz
  obtain ⟨q, hq⟩ := hreach
  refine ⟨q - qp * (N : ℤ), ?_⟩
  push_cast at hq
  linear_combination hq - (N : ℤ) * hqp

/-- A mixed, non-common-scale example: two `Q(q^3,q^15)` factors force the
remaining `Q(q,q^15)` product into residues `0` or `1` modulo three, so the
entire residue-`2` progression vanishes. -/
theorem persistentTripleVanishing_fifteen_one_three_three_two :
    PersistentTripleVanishing 15 1 3 3 2 := by
  apply persistentTripleVanishing_of_not_localReachable 3 15 1 3 3 2
  all_goals norm_num
  intro hreach
  rcases hreach with ⟨b1, b2, b3, hdiv⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    norm_num [tripleBranchSubsetResidue] at hdiv

end Ramanujan.MultiQuintuple
