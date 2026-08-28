/-
# Eight-coset theta encoding of triple quintuple products

The three Watson branch bits label eight shifted cosets of the cubic ternary
lattice `(6p Z)^3`.  Square completion identifies a coefficient shell of a
triple quintuple product with a common norm shell in these eight cosets.  The
original product coefficient is the parity-character projection of their
eight representation numbers.

This file makes that spectral reformulation exact over formal power series.
It is the interface needed to attack the remaining primitive
Root--Vanishing rigidity problem with ternary lattice-coset theta methods.
-/
import RamanujanTau.MultiQuintupleLocalSupport

namespace Ramanujan.MultiQuintuple
open PowerSeries

/-- The three Watson branch bits, viewed as the label of one shifted ternary
coset. -/
abbrev TripleBranchBits := (Bool × Bool) × Bool

/-- The branch label of a bilateral triple point. -/
def pointBranchBits (x : TripleQuintBranchIndex) : TripleBranchBits :=
  ((pointB1 x, pointB2 x), pointB3 x)

/-- The parity character selecting the signed triple-product coefficient. -/
def tripleBranchWeight (b : TripleBranchBits) : ℤ :=
  -(branchSign b.1.1 * branchSign b.1.2 * branchSign b.2)

lemma pointBranchWeight_eq_tripleBranchWeight (x : TripleQuintBranchIndex) :
    pointBranchWeight x = tripleBranchWeight (pointBranchBits x) := by
  rfl

/-- A point in the ambient integral ternary quadratic space. -/
abbrev TernaryIntPoint := (ℤ × ℤ) × ℤ

/-- The completed-square coordinate vector of a bilateral branch point. -/
def pointThetaVector (p i j k : ℕ)
    (x : TripleQuintBranchIndex) : TernaryIntPoint :=
  ((pointCoord1 p i x, pointCoord2 p j x), pointCoord3 p k x)

/-- The base point of one Watson branch coset of `(6p Z)^3`. -/
def watsonBranchCosetBase
    (p i j k : ℤ) (b : TripleBranchBits) : TernaryIntPoint :=
  ((6 * i + branchSign b.1.1 * p, 6 * j + branchSign b.1.2 * p),
    6 * k + branchSign b.2 * p)

/-- Membership in one of the eight shifted Watson cosets. -/
def InWatsonBranchCoset
    (p i j k : ℤ) (b : TripleBranchBits) (y : TernaryIntPoint) : Prop :=
  ∃ n1 n2 n3 : ℤ,
    y.1.1 = quintLatticeCoord b.1.1 p i n1 ∧
    y.1.2 = quintLatticeCoord b.1.2 p j n2 ∧
    y.2 = quintLatticeCoord b.2 p k n3

lemma quintLatticeCoord_eq_cosetBase_add_period
    (b : Bool) (p i n : ℤ) :
    quintLatticeCoord b p i n =
      6 * i + branchSign b * p + 6 * p * n := by
  cases b <;> simp [quintLatticeCoord, branchSign] <;> ring

/-- The existential coordinate definition is exactly membership in the
translate of `(6p Z)^3`. -/
theorem inWatsonBranchCoset_iff_coordinate_dvd
    (p i j k : ℤ) (b : TripleBranchBits) (y : TernaryIntPoint) :
    InWatsonBranchCoset p i j k b y ↔
      6 * p ∣ y.1.1 - (watsonBranchCosetBase p i j k b).1.1 ∧
      6 * p ∣ y.1.2 - (watsonBranchCosetBase p i j k b).1.2 ∧
      6 * p ∣ y.2 - (watsonBranchCosetBase p i j k b).2 := by
  constructor
  · rintro ⟨n1, n2, n3, h1, h2, h3⟩
    rw [h1, h2, h3]
    refine ⟨⟨n1, ?_⟩, ⟨n2, ?_⟩, ⟨n3, ?_⟩⟩ <;>
      simp [watsonBranchCosetBase,
        quintLatticeCoord_eq_cosetBase_add_period]
  · rintro ⟨⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩⟩
    refine ⟨n1, n2, n3, ?_, ?_, ?_⟩
    · rw [quintLatticeCoord_eq_cosetBase_add_period]
      dsimp [watsonBranchCosetBase] at h1 ⊢
      linear_combination h1
    · rw [quintLatticeCoord_eq_cosetBase_add_period]
      dsimp [watsonBranchCosetBase] at h2 ⊢
      linear_combination h2
    · rw [quintLatticeCoord_eq_cosetBase_add_period]
      dsimp [watsonBranchCosetBase] at h3 ⊢
      linear_combination h3

/-- Every bilateral branch point lands in the shifted coset labeled by its
three branch bits. -/
theorem pointThetaVector_mem_watsonBranchCoset
    (p i j k : ℕ) (x : TripleQuintBranchIndex) :
    InWatsonBranchCoset p i j k (pointBranchBits x)
      (pointThetaVector p i j k x) := by
  refine ⟨pointN1 x, pointN2 x, pointN3 x, ?_, ?_, ?_⟩ <;> rfl

/-- Points of one fixed Watson branch on the coefficient shell `q^K`. -/
noncomputable def branchExponentShell
    (p i j k K : ℕ) (b : TripleBranchBits) : Finset TripleQuintBranchIndex :=
  (tripleQuintBranchBox K).filter fun x =>
    pointBranchBits x = b ∧ pointTripleExp2 p i j k x = 2 * (K : ℤ)

/-- The formal theta component recording the representation numbers of one
Watson branch coset, indexed by the original coefficient degree. -/
noncomputable def branchThetaComponent
    (p i j k : ℕ) (b : TripleBranchBits) : PowerSeries ℤ :=
  PowerSeries.mk fun K => ((branchExponentShell p i j k K b).card : ℤ)

@[simp] lemma coeff_branchThetaComponent
    (p i j k K : ℕ) (b : TripleBranchBits) :
    coeff K (branchThetaComponent p i j k b) =
      ((branchExponentShell p i j k K b).card : ℤ) := by
  simp [branchThetaComponent]

/-- The parity-character projection of the eight branch theta components. -/
noncomputable def signedWatsonCosetTheta
    (p i j k : ℕ) : PowerSeries ℤ :=
  ∑ b : TripleBranchBits,
    PowerSeries.C (tripleBranchWeight b) * branchThetaComponent p i j k b

/-- The unsigned union of the four positive-parity Watson cosets. -/
noncomputable def positiveWatsonCosetTheta
    (p i j k : ℕ) : PowerSeries ℤ :=
  ∑ b : TripleBranchBits,
    if tripleBranchWeight b = 1 then branchThetaComponent p i j k b else 0

/-- The unsigned union of the four negative-parity Watson cosets. -/
noncomputable def negativeWatsonCosetTheta
    (p i j k : ℕ) : PowerSeries ℤ :=
  ∑ b : TripleBranchBits,
    if tripleBranchWeight b = -1 then branchThetaComponent p i j k b else 0

/-- The signed theta series is exactly the difference of two honest,
nonnegative representation series, each a union of four shifted cosets. -/
theorem signedWatsonCosetTheta_eq_positive_sub_negative
    (p i j k : ℕ) :
    signedWatsonCosetTheta p i j k =
      positiveWatsonCosetTheta p i j k - negativeWatsonCosetTheta p i j k := by
  rw [signedWatsonCosetTheta, positiveWatsonCosetTheta, negativeWatsonCosetTheta,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rcases b with ⟨⟨b1, b2⟩, b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [tripleBranchWeight, branchSign]

lemma coeff_signedWatsonCosetTheta
    (p i j k K : ℕ) :
    coeff K (signedWatsonCosetTheta p i j k) =
      ∑ b : TripleBranchBits,
        tripleBranchWeight b * ((branchExponentShell p i j k K b).card : ℤ) := by
  simp only [signedWatsonCosetTheta, map_sum,
    PowerSeries.coeff_C_mul, coeff_branchThetaComponent]

/-! ### The finite Walsh transform of the eight cosets -/

/-- The two-point Walsh character. -/
def boolWalshCharacter (a b : Bool) : ℤ :=
  if a then (if b then -1 else 1) else 1

/-- The product Walsh character on the branch cube `(Z/2Z)^3`. -/
def tripleWalshCharacter (a b : TripleBranchBits) : ℤ :=
  boolWalshCharacter a.1.1 b.1.1 *
    boolWalshCharacter a.1.2 b.1.2 * boolWalshCharacter a.2 b.2

/-- All eight character projections of the branch-coset theta vector. -/
noncomputable def branchWalshTheta
    (p i j k : ℕ) (a : TripleBranchBits) : PowerSeries ℤ :=
  ∑ b : TripleBranchBits,
    PowerSeries.C (tripleWalshCharacter a b) * branchThetaComponent p i j k b

lemma tripleBranchWeight_eq_parityWalsh (b : TripleBranchBits) :
    tripleBranchWeight b = tripleWalshCharacter ((true, true), true) b := by
  rcases b with ⟨⟨b1, b2⟩, b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    norm_num [tripleBranchWeight, tripleWalshCharacter,
      boolWalshCharacter, branchSign]

/-- The quintuple-product projection is the top parity Walsh component. -/
theorem signedWatsonCosetTheta_eq_parityWalsh
    (p i j k : ℕ) :
    signedWatsonCosetTheta p i j k =
      branchWalshTheta p i j k ((true, true), true) := by
  simp only [signedWatsonCosetTheta, branchWalshTheta,
    tripleBranchWeight_eq_parityWalsh]

/-- Orthogonality of the eight Walsh characters. -/
lemma tripleWalsh_orthogonality (b c : TripleBranchBits) :
    (∑ a : TripleBranchBits,
      tripleWalshCharacter a b * tripleWalshCharacter a c) =
        if b = c then 8 else 0 := by
  rcases b with ⟨⟨b1, b2⟩, b3⟩
  rcases c with ⟨⟨c1, c2⟩, c3⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    cases c1 <;> cases c2 <;> cases c3 <;>
      norm_num [Fintype.sum_prod_type, Fintype.sum_bool,
        tripleWalshCharacter, boolWalshCharacter]

/-- Finite Fourier inversion on the branch cube. -/
lemma tripleWalsh_inversion
    (f : TripleBranchBits → ℤ) (b : TripleBranchBits) :
    (∑ a : TripleBranchBits,
      tripleWalshCharacter a b *
        (∑ c : TripleBranchBits, tripleWalshCharacter a c * f c)) =
      8 * f b := by
  show (∑ a ∈ (Finset.univ : Finset TripleBranchBits),
      tripleWalshCharacter a b *
        (∑ c ∈ (Finset.univ : Finset TripleBranchBits),
          tripleWalshCharacter a c * f c)) = 8 * f b
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ c ∈ (Finset.univ : Finset TripleBranchBits),
      ∑ a ∈ (Finset.univ : Finset TripleBranchBits),
        tripleWalshCharacter a b *
          (tripleWalshCharacter a c * f c)) =
        ∑ c ∈ (Finset.univ : Finset TripleBranchBits),
          (∑ a : TripleBranchBits,
            tripleWalshCharacter a b * tripleWalshCharacter a c) * f c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 8 * f b := by
      simp_rw [tripleWalsh_orthogonality]
      simp

lemma tripleWalshCharacter_comm (a b : TripleBranchBits) :
    tripleWalshCharacter a b = tripleWalshCharacter b a := by
  rcases a with ⟨⟨a1, a2⟩, a3⟩
  rcases b with ⟨⟨b1, b2⟩, b3⟩
  cases a1 <;> cases a2 <;> cases a3 <;>
    cases b1 <;> cases b2 <;> cases b3 <;>
      norm_num [tripleWalshCharacter, boolWalshCharacter]

/-- Walsh transform of one Walsh character. -/
lemma tripleWalsh_transform_character (a c : TripleBranchBits) :
    (∑ b : TripleBranchBits,
      tripleWalshCharacter a b * tripleWalshCharacter c b) =
        if a = c then 8 else 0 := by
  calc
    (∑ b : TripleBranchBits,
      tripleWalshCharacter a b * tripleWalshCharacter c b) =
        ∑ b : TripleBranchBits,
          tripleWalshCharacter b a * tripleWalshCharacter b c := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [tripleWalshCharacter_comm a b,
              tripleWalshCharacter_comm c b]
    _ = if a = c then 8 else 0 := tripleWalsh_orthogonality a c

/-- The single parity projection is not injective on branch spectra.  Thus a
scalar vanishing identity alone cannot justify applying theta-series rigidity
componentwise; additional modular/Hecke transforms really are required. -/
theorem parityWalshProjection_not_injective :
    ¬Function.Injective
      (fun f : TripleBranchBits → ℤ =>
        ∑ b : TripleBranchBits,
          tripleWalshCharacter ((true, true), true) b * f b) := by
  intro hinjective
  let f : TripleBranchBits → ℤ := fun b =>
    if b = ((false, false), false) ∨ b = ((false, false), true) then 1 else 0
  have hprojection :
      (∑ b : TripleBranchBits,
        tripleWalshCharacter ((true, true), true) b * f b) =
      ∑ b : TripleBranchBits,
        tripleWalshCharacter ((true, true), true) b * (0 : ℤ) := by
    norm_num [f, Fintype.sum_prod_type, Fintype.sum_bool,
      tripleWalshCharacter, boolWalshCharacter]
  have hfunction := hinjective hprojection
  have hvalue := congrFun hfunction ((false, false), false)
  norm_num [f] at hvalue

/-- By contrast, simultaneous vanishing of all eight Walsh projections forces
the entire branch spectrum to vanish. -/
theorem tripleWalsh_all_zero_implies_zero
    (f : TripleBranchBits → ℤ)
    (hzero : ∀ a : TripleBranchBits,
      (∑ b : TripleBranchBits, tripleWalshCharacter a b * f b) = 0) :
    ∀ b, f b = 0 := by
  intro b
  have hinversion := tripleWalsh_inversion f b
  simp_rw [hzero] at hinversion
  norm_num at hinversion ⊢
  exact hinversion

/-- **Walsh recovery theorem.**  The eight character projections retain the
entire vector-valued theta series: every branch-coset component is recovered
integrally after multiplication by eight. -/
theorem branchThetaComponent_walsh_inversion
    (p i j k : ℕ) (b : TripleBranchBits) :
    PowerSeries.C 8 * branchThetaComponent p i j k b =
      ∑ a : TripleBranchBits,
        PowerSeries.C (tripleWalshCharacter a b) *
          branchWalshTheta p i j k a := by
  ext K
  simp only [PowerSeries.coeff_C_mul, coeff_branchThetaComponent,
    map_sum, branchWalshTheta]
  simpa [PowerSeries.coeff_C_mul] using
    (tripleWalsh_inversion
      (fun c => ((branchExponentShell p i j k K c).card : ℤ)) b).symm

lemma branchExponentShell_card_eq_indicatorSum
    (p i j k K : ℕ) (b : TripleBranchBits) :
    ((branchExponentShell p i j k K b).card : ℤ) =
      ∑ x ∈ tripleQuintBranchBox K,
        if pointBranchBits x = b ∧
          pointTripleExp2 p i j k x = 2 * (K : ℤ) then 1 else 0 := by
  simp [branchExponentShell]

lemma tripleBranchWeight_mul_branchExponentShell_card
    (p i j k K : ℕ) (b : TripleBranchBits) :
    tripleBranchWeight b * ((branchExponentShell p i j k K b).card : ℤ) =
      ∑ x ∈ tripleQuintBranchBox K,
        if pointBranchBits x = b ∧
          pointTripleExp2 p i j k x = 2 * (K : ℤ)
        then tripleBranchWeight b else 0 := by
  rw [branchExponentShell_card_eq_indicatorSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : pointBranchBits x = b ∧
      pointTripleExp2 p i j k x = 2 * (K : ℤ) <;> simp [h]

/-- The signed eight-coset theta projection is exactly the actual triple
quintuple product. -/
theorem signedWatsonCosetTheta_eq_tripleQuintupleSpecialized
    (p i j k : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    signedWatsonCosetTheta p i j k =
      quintupleSpecialized p i * quintupleSpecialized p j *
        quintupleSpecialized p k := by
  ext K
  rw [coeff_signedWatsonCosetTheta,
    coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k K
      hi hpi hj hpj hk hpk]
  simp_rw [tripleBranchWeight_mul_branchExponentShell_card]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)
  · simp [pointContribution, hexp, pointBranchWeight_eq_tripleBranchWeight]
  · simp [pointContribution, hexp]

/-- The branch-independent square-completion offset. -/
def tripleThetaOffset (p i j k : ℕ) : ℤ :=
  (6 * (i : ℤ) - p) ^ 2 + (6 * (j : ℤ) - p) ^ 2 +
    (6 * (k : ℤ) - p) ^ 2

/-- Squared Euclidean norm of the three completed Watson coordinates. -/
def pointThetaNorm (p i j k : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  ternaryNorm (pointCoord1 p i x) (pointCoord2 p j x) (pointCoord3 p k x)

/-- The common ternary norm corresponding to coefficient degree `K`. -/
def tripleThetaNormTarget (p i j k K : ℕ) : ℤ :=
  24 * (p : ℤ) * K + tripleThetaOffset p i j k

/-- Square completion in point notation. -/
lemma pointThetaNorm_eq_squareCompletion
    (p i j k : ℕ) (x : TripleQuintBranchIndex) :
    pointThetaNorm p i j k x =
      12 * (p : ℤ) * pointTripleExp2 p i j k x +
        tripleThetaOffset p i j k := by
  have h := tripleQuintExp2_square_completion
    (pointB1 x) (pointB2 x) (pointB3 x) p i j k
    (pointN1 x) (pointN2 x) (pointN3 x)
  change tripleQuintNorm (pointB1 x) (pointB2 x) (pointB3 x) p i j k
      (pointN1 x) (pointN2 x) (pointN3 x) = _
  rw [← h]
  simp only [pointTripleExp2, tripleThetaOffset]
  ring

/-- For positive modulus, an exponent shell is exactly its shifted ternary
coset norm shell. -/
lemma pointTripleExp2_eq_iff_pointThetaNorm_eq
    (p i j k K : ℕ) (x : TripleQuintBranchIndex) (hp : 0 < p) :
    pointTripleExp2 p i j k x = 2 * (K : ℤ) ↔
      pointThetaNorm p i j k x = tripleThetaNormTarget p i j k K := by
  rw [pointThetaNorm_eq_squareCompletion]
  simp only [tripleThetaNormTarget]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have hmul :
        12 * (p : ℤ) * pointTripleExp2 p i j k x =
          12 * (p : ℤ) * (2 * (K : ℤ)) := by
      dsimp [tripleThetaOffset] at h ⊢
      linear_combination h
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (12 : ℤ) ≠ 0)
      (by exact_mod_cast hp.ne')) hmul

/-- One fixed shifted-coset norm shell. -/
noncomputable def branchThetaNormShell
    (p i j k K : ℕ) (b : TripleBranchBits) : Finset TripleQuintBranchIndex :=
  (tripleQuintBranchBox K).filter fun x =>
    pointBranchBits x = b ∧
      pointThetaNorm p i j k x = tripleThetaNormTarget p i j k K

/-- The exponent-shell and norm-shell models of every branch component agree
exactly. -/
theorem branchExponentShell_eq_branchThetaNormShell
    (p i j k K : ℕ) (b : TripleBranchBits) (hp : 0 < p) :
    branchExponentShell p i j k K b = branchThetaNormShell p i j k K b := by
  apply Finset.filter_congr
  intro x hx
  simp only [and_congr_right_iff]
  intro _
  exact pointTripleExp2_eq_iff_pointThetaNorm_eq p i j k K x hp

/-! ### Exact spectral reformulation of persistent vanishing -/

/-- The top Walsh component vanishes on every coefficient in one arithmetic
progression. -/
def PersistentThetaCosetVanishing (p i j k R : ℕ) : Prop :=
  ∀ N : ℕ, coeff (p * N + R) (signedWatsonCosetTheta p i j k) = 0

/-- Persistent signed vanishing is precisely isospectrality, along the
selected norm progression, of the positive and negative four-coset unions. -/
theorem persistentThetaCosetVanishing_iff_parityCosets_isospectral
    (p i j k R : ℕ) :
    PersistentThetaCosetVanishing p i j k R ↔
      ∀ N : ℕ,
        coeff (p * N + R) (positiveWatsonCosetTheta p i j k) =
          coeff (p * N + R) (negativeWatsonCosetTheta p i j k) := by
  rw [PersistentThetaCosetVanishing]
  simp_rw [signedWatsonCosetTheta_eq_positive_sub_negative,
    map_sub, sub_eq_zero]

/-- Persistent product vanishing and persistent vanishing of the signed
eight-coset theta projection are definitionally the same after the exact
bilateral bridge. -/
theorem persistentThetaCosetVanishing_iff_persistentTripleVanishing
    (p i j k R : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    PersistentThetaCosetVanishing p i j k R ↔
      PersistentTripleVanishing p i j k R := by
  rw [PersistentThetaCosetVanishing, PersistentTripleVanishing,
    signedWatsonCosetTheta_eq_tripleQuintupleSpecialized p i j k
      hi hpi hj hpj hk hpk]

/-- The remaining primitive rigidity problem, stated purely for the signed
theta spectrum of the eight shifted ternary cosets. -/
def AdmissibleThetaCosetRigidity (p i j k R : ℕ) : Prop :=
  AdmissibleSparseTriple p i j k → R < p →
    PersistentThetaCosetVanishing p i j k R →
      HasProjectiveRootTarget p i j k R

/-- **Exact theta-rigidity reduction.**  Solving the eight-coset spectral
rigidity statement is neither weaker nor stronger than the remaining
admissible Root--Vanishing rigidity conjecture: the two propositions are
logically equivalent. -/
theorem admissibleThetaCosetRigidity_iff_rootVanishingRigidity
    (p i j k R : ℕ) :
    AdmissibleThetaCosetRigidity p i j k R ↔
      AdmissibleRootVanishingRigidity p i j k R := by
  constructor
  · intro htheta hadmissible hR hbalance
    have hadmissible' := hadmissible
    rcases hadmissible' with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
    have hpi : 2 * i < p := by omega
    have hj : 0 < j := by omega
    have hpj : 2 * j < p := by omega
    have hk : 0 < k := by omega
    apply htheta hadmissible hR
    apply (persistentThetaCosetVanishing_iff_persistentTripleVanishing
      p i j k R hi hpi hj hpj hk hpk).mpr
    exact (persistentTripleVanishing_iff_shellwiseSignBalance
      p i j k R hi hpi hj hpj hk hpk).mpr hbalance
  · intro hroot hadmissible hR htheta
    have hadmissible' := hadmissible
    rcases hadmissible' with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
    have hpi : 2 * i < p := by omega
    have hj : 0 < j := by omega
    have hpj : 2 * j < p := by omega
    have hk : 0 < k := by omega
    apply hroot hadmissible hR
    apply (persistentTripleVanishing_iff_shellwiseSignBalance
      p i j k R hi hpi hj hpj hk hpk).mp
    exact (persistentThetaCosetVanishing_iff_persistentTripleVanishing
      p i j k R hi hpi hj hpj hk hpk).mp htheta

/-- On admissible data, the desired projective-root biconditional can now be
read entirely as a theta-coset statement. -/
theorem admissibleRootTarget_iff_persistentTheta_iff_thetaRigidity
    (p i j k R : ℕ) (hadmissible : AdmissibleSparseTriple p i j k)
    (hR : R < p) :
    (HasProjectiveRootTarget p i j k R ↔
      PersistentThetaCosetVanishing p i j k R) ↔
        AdmissibleThetaCosetRigidity p i j k R := by
  have hadmissible' := hadmissible
  rcases hadmissible' with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpi : 2 * i < p := by omega
  have hj : 0 < j := by omega
  have hpj : 2 * j < p := by omega
  have hk : 0 < k := by omega
  rw [persistentThetaCosetVanishing_iff_persistentTripleVanishing
    p i j k R hi hpi hj hpj hk hpk,
    admissibleRootVanishingEquivalence_iff_rigidity
      p i j k R hadmissible hR,
    admissibleThetaCosetRigidity_iff_rootVanishingRigidity]

end Ramanujan.MultiQuintuple
