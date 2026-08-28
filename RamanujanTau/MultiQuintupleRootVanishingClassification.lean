/-
# The exact classification boundary for sparse triple vanishings

For a fixed coefficient, vanishing is *exactly* equality between the number of
positive and negative bilateral branch points on that exponent shell.  Thus it
is equivalent to the existence of an abstract sign-reversing bijection between
the two finite supports.  This file proves that statement for the actual
three-factor Pochhammer product and then packages it progression-wise.

The uniform projective-root theorem supplies much more: one affine geometric
involution works coherently on every shell.  We prove that a projective-root
certificate implies shell balance and persistent vanishing.  Finally we show
that the desired bare Root--Vanishing biconditional is logically equivalent to
one sharply isolated rigidity statement: every shellwise balance must admit a
short projective-root certificate.  No such rigidity claim is assumed here.
The final section proves that the unrestricted version is false, exhibits the
separate imprimitive-scale mechanism, and states the corrected
prime/distinct/isotropic frontier.
-/
import RamanujanTau.MultiQuintupleRootVanishingEquivalence
import RamanujanTau.MultiQuintupleRootConverse
import RamanujanTau.MultiQuintupleCanonical

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- Contributing branch points of weight `+1` for one actual product
coefficient. -/
noncomputable def positiveCoefficientSupport (p i j k K : ℕ) :
    Finset TripleQuintBranchIndex :=
  (tripleQuintBranchBox K).filter fun x =>
    pointTripleExp2 p i j k x = 2 * (K : ℤ) ∧ pointBranchWeight x = 1

/-- Contributing branch points of weight `-1` for one actual product
coefficient. -/
noncomputable def negativeCoefficientSupport (p i j k K : ℕ) :
    Finset TripleQuintBranchIndex :=
  (tripleQuintBranchBox K).filter fun x =>
    pointTripleExp2 p i j k x = 2 * (K : ℤ) ∧ pointBranchWeight x = -1

/-- Every bilateral triple branch has weight exactly `+1` or `-1`. -/
lemma pointBranchWeight_eq_one_or_neg_one (x : TripleQuintBranchIndex) :
    pointBranchWeight x = 1 ∨ pointBranchWeight x = -1 := by
  rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    norm_num [pointBranchWeight, pointB1, pointB2, pointB3, branchSign]

/-- A point contribution is the difference of the positive- and
negative-support indicator functions. -/
lemma pointContribution_eq_sign_indicators
    (p i j k K : ℕ) (x : TripleQuintBranchIndex) :
    pointContribution p i j k K x =
      (if pointTripleExp2 p i j k x = 2 * (K : ℤ) ∧ pointBranchWeight x = 1
        then 1 else 0) -
      (if pointTripleExp2 p i j k x = 2 * (K : ℤ) ∧ pointBranchWeight x = -1
        then 1 else 0) := by
  by_cases hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)
  · rcases pointBranchWeight_eq_one_or_neg_one x with hweight | hweight
    · simp [pointContribution, hexp, hweight]
    · simp [pointContribution, hexp, hweight]
  · simp [pointContribution, hexp]

/-- The finite coefficient sum is literally `#positive - #negative`. -/
lemma sum_pointContribution_eq_support_card_sub
    (p i j k K : ℕ) :
    (∑ x ∈ tripleQuintBranchBox K, pointContribution p i j k K x) =
      ((positiveCoefficientSupport p i j k K).card : ℤ) -
        ((negativeCoefficientSupport p i j k K).card : ℤ) := by
  simp_rw [pointContribution_eq_sign_indicators]
  rw [Finset.sum_sub_distrib]
  simp [positiveCoefficientSupport, negativeCoefficientSupport]

/-- **Exact shell-balance criterion.**  An actual triple-product coefficient
vanishes iff its positive and negative finite branch supports have the same
cardinality. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_iff_support_card_eq
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 ↔
      (positiveCoefficientSupport p i j k K).card =
        (negativeCoefficientSupport p i j k K).card := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K
    hi hpi hj hpj hk hpk, sum_pointContribution_eq_support_card_sub]
  constructor
  · intro hzero
    have hcast : ((positiveCoefficientSupport p i j k K).card : ℤ) =
        ((negativeCoefficientSupport p i j k K).card : ℤ) := sub_eq_zero.mp hzero
    exact_mod_cast hcast
  · intro hcard
    apply sub_eq_zero.mpr
    exact_mod_cast hcard

/-- **Vanishing iff a sign-reversing shell bijection exists.**

This converse is completely unconditional, but the bijection is abstract: it
need not be affine, norm-preserving, or coherent between different shells. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_iff_support_equiv
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 ↔
      Nonempty
        ((positiveCoefficientSupport p i j k K : Set TripleQuintBranchIndex) ≃
          (negativeCoefficientSupport p i j k K : Set TripleQuintBranchIndex)) := by
  rw [coeff_tripleQuintupleSpecialized_eq_zero_iff_support_card_eq p i j k K
    hi hpi hj hpj hk hpk]
  constructor
  · intro hcard
    exact ⟨Fintype.equivOfCardEq (by simpa using hcard)⟩
  · rintro ⟨equiv⟩
    simpa using Fintype.card_congr equiv

/-- Every coefficient in one residue progression of the actual product is
zero. -/
def PersistentTripleVanishing (p i j k R : ℕ) : Prop :=
  ∀ N : ℕ,
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0

/-- Every exponent shell in a residue progression has equally many positive
and negative branch points. -/
def ShellwiseSignBalance (p i j k R : ℕ) : Prop :=
  ∀ N : ℕ,
    Nonempty
      ((positiveCoefficientSupport p i j k (p * N + R) :
          Set TripleQuintBranchIndex) ≃
        (negativeCoefficientSupport p i j k (p * N + R) :
          Set TripleQuintBranchIndex))

/-- Persistent vanishing and abstract shellwise sign balance are exactly
equivalent. -/
theorem persistentTripleVanishing_iff_shellwiseSignBalance
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    PersistentTripleVanishing p i j k R ↔ ShellwiseSignBalance p i j k R := by
  constructor <;> intro h N
  · exact (coeff_tripleQuintupleSpecialized_eq_zero_iff_support_equiv
      p i j k (p * N + R) hi hpi hj hpj hk hpk).mp (h N)
  · exact (coeff_tripleQuintupleSpecialized_eq_zero_iff_support_equiv
      p i j k (p * N + R) hi hpi hj hpj hk hpk).mpr (h N)

/-- The complete arithmetic data consumed by the uniform projective-root
vanishing theorem for a fixed residue. -/
structure ProjectiveRootTargetCertificate (p i j k R : ℕ) where
  lambda : ℤ
  e : ℤ
  c : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  u : ℤ
  he : e = 1 ∨ e = 2
  hw1 : w1 = lambda * i + p * a1
  hw2 : w2 = lambda * j + p * a2
  hw3 : w3 = lambda * k + p * a3
  hvw : ternaryDot i j k w1 w2 w3 = p * u
  hroot : ternaryNorm w1 w2 w3 = e * p
  hcoefficient : c * e = 2
  hcase :
    (((e * (p : ℤ) : ℤ) : ZMod 3) = 1 ∧
      ∃ h : ℤ, 2 * lambda * R = w1 + w2 + w3 - 6 * u + p * h) ∨
    (((e * (p : ℤ) : ℤ) : ZMod 3) = 2 ∧
      ∃ base h : ℤ,
        base = 2 * lambda * R - (w1 + w2 + w3) + 6 * u ∧
        c * lambda * base = 12 + p * h)

/-- Existence of a short projective root whose branch-closing target is the
specified residue. -/
def HasProjectiveRootTarget (p i j k R : ℕ) : Prop :=
  Nonempty (ProjectiveRootTargetCertificate p i j k R)

/-- The uniform projective root gives persistent vanishing, not merely one
zero coefficient. -/
theorem hasProjectiveRootTarget_implies_persistentTripleVanishing
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) :
    HasProjectiveRootTarget p i j k R → PersistentTripleVanishing p i j k R := by
  rintro ⟨root⟩ N
  exact coeff_tripleQuintupleSpecialized_eq_zero_of_projectiveRoot
    p i j k N R root.lambda root.e root.c root.w1 root.w2 root.w3
    root.a1 root.a2 root.a3 root.u hi hpi hj hpj hk hpk hpodd root.he
    root.hw1 root.hw2 root.hw3 root.hvw root.hroot root.hcoefficient root.hcase

/-- Hence a projective root supplies an abstract sign balance on every shell;
the proof actually constructs the stronger coherent affine involution upstream. -/
theorem hasProjectiveRootTarget_implies_shellwiseSignBalance
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) :
    HasProjectiveRootTarget p i j k R → ShellwiseSignBalance p i j k R := by
  intro hroot
  exact (persistentTripleVanishing_iff_shellwiseSignBalance p i j k R
    hi hpi hj hpj hk hpk).mp
      (hasProjectiveRootTarget_implies_persistentTripleVanishing p i j k R
        hi hpi hj hpj hk hpk hpodd hroot)

/-- The candidate unrestricted rigidity assertion, isolated as a named
proposition.  It says that arbitrary shellwise cardinality balance must come
from one coherent short projective root.  A counterexample is proved below;
the admissible replacement appears at the end of the file. -/
def RootVanishingRigidity (p i j k R : ℕ) : Prop :=
  ShellwiseSignBalance p i j k R → HasProjectiveRootTarget p i j k R

/-- **Exact reduction of Root--Vanishing Equivalence.**

Because the root-to-vanishing implication is proved, the unrestricted
biconditional is equivalent to `RootVanishingRigidity`.  This theorem makes the
later counterexample disprove both formulations at once. -/
theorem rootVanishingEquivalence_iff_rigidity
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) :
    (HasProjectiveRootTarget p i j k R ↔ PersistentTripleVanishing p i j k R) ↔
      RootVanishingRigidity p i j k R := by
  constructor
  · intro hequiv hbalance
    exact hequiv.mpr ((persistentTripleVanishing_iff_shellwiseSignBalance
      p i j k R hi hpi hj hpj hk hpk).mpr hbalance)
  · intro hrigidity
    constructor
    · exact hasProjectiveRootTarget_implies_persistentTripleVanishing
        p i j k R hi hpi hj hpj hk hpk hpodd
    · intro hvanishing
      apply hrigidity
      exact (persistentTripleVanishing_iff_shellwiseSignBalance
        p i j k R hi hpi hj hpj hk hpk).mp hvanishing

/-! ### The unrestricted rigidity statement is false

The preceding reduction was intentionally stated without asserting rigidity.
There is a genuine obstruction if the modulus and the Watson branch modulus
share a factor.  The example below is fully symbolic, not a finite coefficient
scan: every factor of `Q(q^3,q^9)` is supported on powers divisible by three,
so its cube vanishes in the progression `9N+1`.  A projective-root target is
impossible because both root norm classes are zero modulo three when `p=9`.
-/

/-- Scaling both Pochhammer parameters by `g` scales every exponent by `g`. -/
lemma pochhammerFinite_scale (g a d N : ℕ) (hg : 0 < g) :
    pochhammerFinite (g * a) (g * d) N =
      PowerSeries.expand g hg.ne' (pochhammerFinite a d N) := by
  rw [pochhammerFinite, pochhammerFinite, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  congr 2
  ring

/-- Hence a scaled infinite Pochhammer product is supported on multiples of
its scaling factor. -/
lemma supportedOnMultiples_pochhammerInf_scale
    (g a d : ℕ) (hg : 0 < g) (ha : 0 < a) (hd : 0 < d) :
    SupportedOnMultiples g (pochhammerInf (g * a) (g * d)) := by
  intro n hn
  rw [coeff_pochhammerInf (Nat.mul_pos hg ha) (Nat.mul_pos hg hd)
    (le_refl (n + 1)), pochhammerFinite_scale g a d (n + 1) hg]
  exact PowerSeries.coeff_expand_of_not_dvd g hg.ne' _ hn

/-- Scaling both parameters of a specialized quintuple product scales its
entire exponent support. -/
theorem quintupleSpecialized_scale_supported
    (g p i : ℕ) (hg : 0 < g) (hi : 0 < i) (hpi : 2 * i < p) :
    SupportedOnMultiples g (quintupleSpecialized (g * p) (g * i)) := by
  have hp : 0 < p := by omega
  have hpi1 : 0 < p - i := by omega
  have hpi2 : 0 < p - 2 * i := by omega
  have h1 := supportedOnMultiples_pochhammerInf_scale g i p hg hi hp
  have h2 := supportedOnMultiples_pochhammerInf_scale g (p - i) p hg hpi1 hp
  have h3 := supportedOnMultiples_pochhammerInf_scale g p p hg hp hp
  have h4 := supportedOnMultiples_pochhammerInf_scale g (p + 2 * i) (2 * p)
    hg (by omega) (by omega)
  have h5 := supportedOnMultiples_pochhammerInf_scale g (p - 2 * i) (2 * p)
    hg hpi2 (by omega)
  have hsub1 : g * p - g * i = g * (p - i) := by
    rw [Nat.mul_sub_left_distrib]
  have hadd : g * p + 2 * (g * i) = g * (p + 2 * i) := by ring
  have hsub2 : g * p - 2 * (g * i) = g * (p - 2 * i) := by
    rw [show 2 * (g * i) = g * (2 * i) by ring, Nat.mul_sub_left_distrib]
  have hdouble : 2 * (g * p) = g * (2 * p) := by ring
  simpa [quintupleSpecialized, pochhammerProductInf, hsub1, hadd, hsub2, hdouble]
    using supportedOnMultiples_mul h1
      (supportedOnMultiples_mul h2
        (supportedOnMultiples_mul h3 (supportedOnMultiples_mul h4 h5)))

/-- The single specialized factor `Q(q^3,q^9)` has only exponents divisible
by three. -/
lemma quintupleSpecialized_nine_three_supported :
    SupportedOnMultiples 3 (quintupleSpecialized 9 3) := by
  simpa using quintupleSpecialized_scale_supported 3 3 1
    (by norm_num) (by norm_num) (by norm_num)

/-- **Imprimitive-scale vanishing family.**  If a common scale `g` divides
all three indices and the modulus but not the chosen residue, the complete
progression vanishes for the elementary reason that every exponent is a
multiple of `g`. -/
theorem persistentTripleVanishing_of_common_scale
    (g p i j k R : ℕ)
    (hg : 0 < g)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hR : ¬g ∣ R) :
    PersistentTripleVanishing (g * p) (g * i) (g * j) (g * k) R := by
  have hiSupport := quintupleSpecialized_scale_supported g p i hg hi hpi
  have hjSupport := quintupleSpecialized_scale_supported g p j hg hj hpj
  have hkSupport := quintupleSpecialized_scale_supported g p k hg hk hpk
  have hproduct : SupportedOnMultiples g
      (quintupleSpecialized (g * p) (g * i) *
        quintupleSpecialized (g * p) (g * j) *
        quintupleSpecialized (g * p) (g * k)) :=
    supportedOnMultiples_mul (supportedOnMultiples_mul hiSupport hjSupport) hkSupport
  intro N
  apply hproduct
  intro hdvd
  apply hR
  have hterm : g ∣ (g * p) * N := ⟨p * N, by ring⟩
  exact (Nat.dvd_add_iff_right hterm).mpr hdvd

/-- A fully proved persistent vanishing outside the prime/distinct regime. -/
theorem persistentTripleVanishing_nine_three_three_three_one :
    PersistentTripleVanishing 9 3 3 3 1 := by
  have hfactor := quintupleSpecialized_nine_three_supported
  have hproduct : SupportedOnMultiples 3
      (quintupleSpecialized 9 3 * quintupleSpecialized 9 3 *
        quintupleSpecialized 9 3) :=
    supportedOnMultiples_mul (supportedOnMultiples_mul hfactor hfactor) hfactor
  intro N
  apply hproduct
  rintro ⟨d, hd⟩
  omega

/-- No projective-root certificate can exist at modulus nine: its required
mod-three root class would say `0=1` or `0=2`. -/
theorem not_hasProjectiveRootTarget_nine_three_three_three_one :
    ¬HasProjectiveRootTarget 9 3 3 3 1 := by
  rintro ⟨root⟩
  rcases root.hcase with ⟨hmod, _⟩ | ⟨hmod, _⟩
  · have hzero : (((9 : ℤ) : ZMod 3)) = 0 := by decide
    have : (0 : ZMod 3) = 1 := by
      simpa only [Int.cast_mul, hzero, mul_zero] using hmod
    exact (by decide : (0 : ZMod 3) ≠ 1) this
  · have hzero : (((9 : ℤ) : ZMod 3)) = 0 := by decide
    have : (0 : ZMod 3) = 2 := by
      simpa only [Int.cast_mul, hzero, mul_zero] using hmod
    exact (by decide : (0 : ZMod 3) ≠ 2) this

/-- **Counterexample to unrestricted Root--Vanishing Equivalence.** -/
theorem not_rootVanishingEquivalence_unrestricted :
    ¬(HasProjectiveRootTarget 9 3 3 3 1 ↔
      PersistentTripleVanishing 9 3 3 3 1) := by
  intro hequiv
  exact not_hasProjectiveRootTarget_nine_three_three_three_one
    (hequiv.mpr persistentTripleVanishing_nine_three_three_three_one)

/-- Consequently the unrestricted rigidity proposition itself is false. -/
theorem not_rootVanishingRigidity_unrestricted :
    ¬RootVanishingRigidity 9 3 3 3 1 := by
  intro hrigidity
  apply not_hasProjectiveRootTarget_nine_three_three_three_one
  apply hrigidity
  exact (persistentTripleVanishing_iff_shellwiseSignBalance 9 3 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mp
      persistentTripleVanishing_nine_three_three_three_one

/-! ### Correct prime/distinct/isotropic frontier -/

/-- The hypotheses of the genuine sparse-triple classification problem.
Ordering loses no products because multiplication is commutative, and makes
pairwise distinctness explicit. -/
def AdmissibleSparseTriple (p i j k : ℕ) : Prop :=
  Nat.Prime p ∧ p ≠ 3 ∧
    0 < i ∧ i < j ∧ j < k ∧ 2 * k < p ∧
    (p : ℤ) ∣ ternaryNorm i j k

/-- The corrected rigidity conjecture excludes the proved imprimitive
counterexample and states exactly the remaining research frontier. -/
def AdmissibleRootVanishingRigidity (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    ShellwiseSignBalance p i j k R → HasProjectiveRootTarget p i j k R

/-- For an admissible triple and canonical residue, the corrected
Root--Vanishing biconditional is equivalent to precisely the corrected
rigidity conjecture. -/
theorem admissibleRootVanishingEquivalence_iff_rigidity
    (p i j k R : ℕ) (hadmissible : AdmissibleSparseTriple p i j k)
    (hR : R < p) :
    (HasProjectiveRootTarget p i j k R ↔ PersistentTripleVanishing p i j k R) ↔
      AdmissibleRootVanishingRigidity p i j k R := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  rw [rootVanishingEquivalence_iff_rigidity p i j k R
    hi hpi hj hpj hk hpk hpodd]
  constructor
  · intro hrigidity _ _
    exact hrigidity
  · intro hrigidity hbalance
    exact hrigidity
      ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩ hR hbalance

end Ramanujan.MultiQuintuple
