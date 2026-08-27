/-
# Finite cancellation for sparse triple quintuple products

This file is the end-to-end finite-sum capstone for the short-root method.  It
packages the three bilateral Watson branches contributing to one coefficient,
and then applies the universal positive or negative short-root matching as a
sign-reversing involution.
-/
import RamanujanTau.MultiQuintupleBilateralBridge
import RamanujanTau.MultiQuintupleRootBranch

namespace Ramanujan.MultiQuintuple
open PowerSeries

set_option maxRecDepth 2048

/-! ### Positivity, parity, and finite support of a bilateral branch -/

/-- Every canonical Watson branch has nonnegative doubled exponent. -/
lemma quintExp2_nonneg (negative : Bool) (p i : ℕ) (n : ℤ)
    (hi : 0 < i) (hp : 2 * i < p) :
    0 ≤ quintExp2 negative p i n := by
  cases negative
  · simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2]
    rw [show (p : ℤ) * n * (3 * n - 1) + 6 * i * n =
        n * ((p : ℤ) * (3 * n - 1) + 6 * i) by ring]
    by_cases hn : 0 ≤ n
    · by_cases hn0 : n = 0
      · simp [hn0]
      · exact mul_nonneg hn (by
          have hn1 : (1 : ℤ) ≤ n := by omega
          have hp0 : (0 : ℤ) ≤ p := by positivity
          nlinarith [mul_nonneg hp0 (show (0 : ℤ) ≤ 3 * n - 1 by omega)])
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by nlinarith)
  · simp only [quintExp2, ↓reduceIte, quintExpB2]
    rw [show (p : ℤ) * n * (3 * n + 1) + 2 * i * (3 * n + 1) =
        (3 * n + 1) * ((p : ℤ) * n + 2 * i) by ring]
    by_cases hn : 0 ≤ n
    · exact mul_nonneg (by nlinarith) (by positivity)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by nlinarith)

/-- Every doubled Watson exponent is even. -/
lemma quintExp2_even (negative : Bool) (p i : ℕ) (n : ℤ) :
    Even (quintExp2 negative p i n) := by
  cases negative
  · obtain ⟨a, ha⟩ := Int.even_mul_pred_self n
    refine ⟨(p : ℤ) * (3 * a + n) + 3 * i * n, ?_⟩
    simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2]
    linear_combination 3 * (p : ℤ) * ha
  · obtain ⟨a, ha⟩ := Int.even_mul_succ_self n
    refine ⟨(p : ℤ) * (3 * a - n) + (i : ℤ) * (3 * n + 1), ?_⟩
    simp only [quintExp2, ↓reduceIte, quintExpB2]
    linear_combination 3 * (p : ℤ) * ha

/-- A branch term contributing to `q^k` lies in the canonical finite interval
`|n| ≤ k+1`.  This is the cutoff used by the coefficient bridge. -/
lemma quintExp2_natAbs_le_add_one (negative : Bool) (p i k : ℕ) (n : ℤ)
    (hi : 0 < i) (hp : 2 * i < p)
    (hexp : quintExp2 negative p i n = 2 * (k : ℤ)) :
    n.natAbs ≤ k + 1 := by
  have hpz : (2 : ℤ) * i + 1 ≤ p := by exact_mod_cast hp
  have hiz : (1 : ℤ) ≤ i := by exact_mod_cast hi
  by_cases hn : 0 ≤ n
  · have habs : ((n.natAbs : ℕ) : ℤ) = n := Int.natAbs_of_nonneg hn
    cases negative
    · simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2] at hexp
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hn1 : (1 : ℤ) ≤ n := by omega
        have hbracket : (2 : ℤ) ≤ (p : ℤ) * (3 * n - 1) + 6 * i := by
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ p by positivity)
            (show (0 : ℤ) ≤ 3 * n - 1 by omega)]
        have hmul := mul_le_mul_of_nonneg_left hbracket hn
        rw [show (p : ℤ) * n * (3 * n - 1) + 6 * i * n =
          n * ((p : ℤ) * (3 * n - 1) + 6 * i) by ring] at hexp
        have hz : ((n.natAbs : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
          rw [habs]
          push_cast
          nlinarith [hmul]
        exact_mod_cast hz
    · simp only [quintExp2, ↓reduceIte, quintExpB2] at hexp
      have hleft : n ≤ 3 * n + 1 := by omega
      have hright : (2 : ℤ) ≤ (p : ℤ) * n + 2 * i := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ p by positivity) hn]
      have hprod : 2 * n ≤ (3 * n + 1) * ((p : ℤ) * n + 2 * i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hleft)
          (show (0 : ℤ) ≤ (p : ℤ) * n + 2 * i by omega),
          mul_nonneg hn (sub_nonneg.mpr hright)]
      rw [show (p : ℤ) * n * (3 * n + 1) + 2 * i * (3 * n + 1) =
        (3 * n + 1) * ((p : ℤ) * n + 2 * i) by ring] at hexp
      have hz : ((n.natAbs : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
        rw [habs]
        push_cast
        nlinarith [hprod]
      exact_mod_cast hz
  · have hm : (1 : ℤ) ≤ -n := by omega
    have habs : ((n.natAbs : ℕ) : ℤ) = -n := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    cases negative
    · simp only [quintExp2, Bool.false_eq_true, ↓reduceIte, quintExpA2] at hexp
      have hscaleRaw :=
        mul_le_mul_of_nonneg_left (show (4 : ℤ) ≤ 3 * (-n) + 1 by omega)
          (show (0 : ℤ) ≤ p by exact_mod_cast Nat.zero_le p)
      have hscale : (4 : ℤ) * p ≤ (p : ℤ) * (3 * (-n) + 1) := by
        simpa [mul_comm] using hscaleRaw
      have hbracket : (2 : ℤ) ≤ (p : ℤ) * (3 * (-n) + 1) - 6 * i := by
        nlinarith
      have hprodRaw := mul_le_mul_of_nonneg_left hbracket (show (0 : ℤ) ≤ -n by omega)
      have hprod : 2 * (-n) ≤ (-n) * ((p : ℤ) * (3 * (-n) + 1) - 6 * i) := by
        simpa [mul_comm] using hprodRaw
      have hre : (p : ℤ) * n * (3 * n - 1) + 6 * i * n =
          (-n) * ((p : ℤ) * (3 * (-n) + 1) - 6 * i) := by ring
      rw [hre] at hexp
      have hz : ((n.natAbs : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
        rw [habs]
        push_cast
        nlinarith [hprod]
      exact_mod_cast hz
    · simp only [quintExp2, ↓reduceIte, quintExpB2] at hexp
      have hleft : 2 * (-n) ≤ 3 * (-n) - 1 := by omega
      have hright : (1 : ℤ) ≤ (p : ℤ) * (-n) - 2 * i := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 2 * i by omega)
          (show (0 : ℤ) ≤ -n - 1 by omega)]
      have hprod : 2 * (-n) ≤
          (3 * (-n) - 1) * ((p : ℤ) * (-n) - 2 * i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hleft)
          (show (0 : ℤ) ≤ (p : ℤ) * (-n) - 2 * i by omega),
          mul_nonneg (show (0 : ℤ) ≤ 2 * (-n) by omega)
            (sub_nonneg.mpr hright)]
      have hre : (p : ℤ) * n * (3 * n + 1) + 2 * i * (3 * n + 1) =
          (3 * (-n) - 1) * ((p : ℤ) * (-n) - 2 * i) := by ring
      rw [hre] at hexp
      have hz : ((n.natAbs : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
        rw [habs]
        push_cast
        nlinarith [hprod]
      exact_mod_cast hz

/-! ### A finite monomial model for one bilateral factor -/

/-- The natural exponent obtained by halving the doubled branch exponent. -/
noncomputable def quintExpHalf (negative : Bool) (p i : ℕ) (n : ℤ) : ℕ :=
  (quintExp2 negative p i n / 2).toNat

lemma quintExp2_eq_two_mul_quintExpHalf (negative : Bool) (p i : ℕ) (n : ℤ)
    (hi : 0 < i) (hp : 2 * i < p) :
    quintExp2 negative p i n = 2 * (quintExpHalf negative p i n : ℤ) := by
  have hnonneg := quintExp2_nonneg negative p i n hi hp
  have hhalf_nonneg : 0 ≤ quintExp2 negative p i n / 2 :=
    Int.ediv_nonneg hnonneg (by norm_num)
  rw [quintExpHalf, Int.toNat_of_nonneg hhalf_nonneg]
  exact (Int.two_mul_ediv_two_of_even (quintExp2_even negative p i n)).symm

/-- One branch contribution as a monomial in an ordinary power series. -/
noncomputable def quintBilateralMonomial
    (negative : Bool) (p i : ℕ) (n : ℤ) : PowerSeries ℤ :=
  PowerSeries.C (-branchSign negative) * X ^ quintExpHalf negative p i n

lemma coeff_quintBilateralMonomial
    (negative : Bool) (p i a : ℕ) (n : ℤ)
    (hi : 0 < i) (hp : 2 * i < p) :
    coeff a (quintBilateralMonomial negative p i n) =
      quintBilateralTermCoeff negative p i a n := by
  have hexp := quintExp2_eq_two_mul_quintExpHalf negative p i n hi hp
  have hcond : (a = quintExpHalf negative p i n) ↔
      quintExp2 negative p i n = 2 * (a : ℤ) := by
    constructor
    · intro ha
      rw [ha]
      exact hexp
    · intro ha
      nlinarith [hexp]
  simp only [quintBilateralMonomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    quintBilateralTermCoeff]
  by_cases ha : a = quintExpHalf negative p i n
  · have he := hcond.mp ha
    cases negative <;> simp [ha, he, branchSign]
  · have he : ¬quintExp2 negative p i n = 2 * (a : ℤ) :=
      fun h => ha (hcond.mpr h)
    cases negative <;> simp [ha, he, branchSign]

private lemma quintBilateralTermCoeff_eq_zero_of_cutoff
    (negative : Bool) (p i a : ℕ) (n : ℤ)
    (hi : 0 < i) (hp : 2 * i < p) (hout : a + 1 < n.natAbs) :
    quintBilateralTermCoeff negative p i a n = 0 := by
  have hne : ¬quintExp2 negative p i n = 2 * (a : ℤ) := by
    intro hexp
    have := quintExp2_natAbs_le_add_one negative p i a n hi hp hexp
    omega
  simp [quintBilateralTermCoeff, hne]

/-- Symmetric interval large enough for every branch term contributing through
degree `K`. -/
noncomputable def quintBranchInterval (K : ℕ) : Finset ℤ :=
  Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)

/-- Finite monomial truncation of one Watson bilateral factor. -/
noncomputable def quintBilateralTrunc (p i K : ℕ) : PowerSeries ℤ :=
  ∑ x ∈ (Finset.univ : Finset Bool).product (quintBranchInterval K),
    quintBilateralMonomial x.1 p i x.2

lemma coeff_quintBilateralTrunc (p i K a : ℕ)
    (hi : 0 < i) (hp : 2 * i < p) (ha : a ≤ K) :
    coeff a (quintBilateralTrunc p i K) = quintBilateralCoeff p i a := by
  have hsubset : quintBranchInterval a ⊆ quintBranchInterval K := by
    intro n hn
    simp only [quintBranchInterval, Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  have hsum :
      (∑ n ∈ quintBranchInterval K,
        (quintBilateralTermCoeff false p i a n +
          quintBilateralTermCoeff true p i a n)) =
      ∑ n ∈ quintBranchInterval a,
        (quintBilateralTermCoeff false p i a n +
          quintBilateralTermCoeff true p i a n) := by
    symm
    apply Finset.sum_subset hsubset
    intro n hnK hnA
    have hout : a + 1 < n.natAbs := by
      simp only [quintBranchInterval, Finset.mem_Icc] at hnA
      rw [not_and_or] at hnA
      rcases hnA with hnA | hnA <;> omega
    rw [quintBilateralTermCoeff_eq_zero_of_cutoff false p i a n hi hp hout,
      quintBilateralTermCoeff_eq_zero_of_cutoff true p i a n hi hp hout]
    simp
  rw [quintBilateralTrunc]
  have hprod :
      (∑ x ∈ (Finset.univ : Finset Bool).product (quintBranchInterval K),
        quintBilateralMonomial x.1 p i x.2) =
      ∑ b ∈ (Finset.univ : Finset Bool), ∑ n ∈ quintBranchInterval K,
        quintBilateralMonomial b p i n := Finset.sum_product _ _ _
  rw [hprod]
  simp_rw [map_sum, coeff_quintBilateralMonomial _ p i a _ hi hp]
  rw [Finset.sum_comm]
  simp
  calc
    (∑ x ∈ quintBranchInterval K,
        (quintBilateralTermCoeff true p i a x +
          quintBilateralTermCoeff false p i a x)) =
        ∑ x ∈ quintBranchInterval K,
          (quintBilateralTermCoeff false p i a x +
            quintBilateralTermCoeff true p i a x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x ∈ quintBranchInterval a,
          (quintBilateralTermCoeff false p i a x +
            quintBilateralTermCoeff true p i a x) := hsum
    _ = quintBilateralCoeff p i a := rfl

/-- Up to the target degree, the finite monomial model and the actual
five-Pochhammer quintuple specialization have identical coefficients. -/
lemma coeff_quintupleSpecialized_eq_trunc (p i K a : ℕ)
    (hi : 0 < i) (hp : 2 * i < p) (ha : a ≤ K) :
    coeff a (quintupleSpecialized p i) = coeff a (quintBilateralTrunc p i K) := by
  rw [coeff_quintupleSpecialized_eq_bilateral p i a hi hp,
    coeff_quintBilateralTrunc p i K a hi hp ha]

/-! ### The finite three-factor coefficient box -/

/-- A branch bit together with its bilateral integer index. -/
abbrev QuintBranchIndex := Bool × ℤ

/-- Three branch-index pairs, grouped to match a threefold Cartesian product. -/
abbrev TripleQuintBranchIndex :=
  (QuintBranchIndex × QuintBranchIndex) × QuintBranchIndex

def pointB1 (x : TripleQuintBranchIndex) : Bool := x.1.1.1
def pointN1 (x : TripleQuintBranchIndex) : ℤ := x.1.1.2
def pointB2 (x : TripleQuintBranchIndex) : Bool := x.1.2.1
def pointN2 (x : TripleQuintBranchIndex) : ℤ := x.1.2.2
def pointB3 (x : TripleQuintBranchIndex) : Bool := x.2.1
def pointN3 (x : TripleQuintBranchIndex) : ℤ := x.2.2

noncomputable def quintBranchBox (K : ℕ) : Finset QuintBranchIndex :=
  (Finset.univ : Finset Bool).product (quintBranchInterval K)

lemma mem_quintBranchBox_of_natAbs_le (K : ℕ) (b : Bool) (n : ℤ)
    (h : n.natAbs ≤ K + 1) : (b, n) ∈ quintBranchBox K := by
  rw [quintBranchBox]
  refine Finset.mem_product.mpr ⟨Finset.mem_univ b, ?_⟩
  rw [quintBranchInterval]
  have hz : |n| ≤ ((K + 1 : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  exact Finset.mem_Icc.mpr (abs_le.mp hz)

noncomputable def tripleQuintBranchBox (K : ℕ) : Finset TripleQuintBranchIndex :=
  (quintBranchBox K).product (quintBranchBox K) |>.product (quintBranchBox K)

lemma sum_quintBranchBox (K : ℕ) (f : QuintBranchIndex → ℤ) :
    (∑ x ∈ quintBranchBox K, f x) =
      ∑ b ∈ (Finset.univ : Finset Bool), ∑ n ∈ quintBranchInterval K, f (b, n) := by
  rw [quintBranchBox]
  exact Finset.sum_product _ _ _

lemma sum_tripleQuintBranchBox (K : ℕ) (f : TripleQuintBranchIndex → ℤ) :
    (∑ x ∈ tripleQuintBranchBox K, f x) =
      ∑ x1 ∈ quintBranchBox K, ∑ x2 ∈ quintBranchBox K,
        ∑ x3 ∈ quintBranchBox K, f ((x1, x2), x3) := by
  rw [tripleQuintBranchBox]
  calc
    (∑ x ∈ ((quintBranchBox K).product (quintBranchBox K)).product
        (quintBranchBox K), f x) =
      ∑ x12 ∈ (quintBranchBox K).product (quintBranchBox K),
        ∑ x3 ∈ quintBranchBox K, f (x12, x3) := Finset.sum_product _ _ _
    _ = ∑ x1 ∈ quintBranchBox K, ∑ x2 ∈ quintBranchBox K,
        ∑ x3 ∈ quintBranchBox K, f ((x1, x2), x3) :=
      Finset.sum_product _ _ _

def pointTripleExp2 (p i j k : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  tripleQuintExp2 (pointB1 x) (pointB2 x) (pointB3 x) p i j k
    (pointN1 x) (pointN2 x) (pointN3 x)

def pointBranchWeight (x : TripleQuintBranchIndex) : ℤ :=
  -(branchSign (pointB1 x) * branchSign (pointB2 x) * branchSign (pointB3 x))

def pointContribution (p i j k K : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  if pointTripleExp2 p i j k x = 2 * (K : ℤ) then pointBranchWeight x else 0

private lemma coeff_three_quintBilateralMonomial
    (b1 b2 b3 : Bool) (p i j k K : ℕ) (n1 n2 n3 : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintBilateralMonomial b1 p i n1 *
      quintBilateralMonomial b2 p j n2 *
      quintBilateralMonomial b3 p k n3) =
      if tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 = 2 * (K : ℤ) then
        -(branchSign b1 * branchSign b2 * branchSign b3)
      else 0 := by
  have he1 := quintExp2_eq_two_mul_quintExpHalf b1 p i n1 hi hpi
  have he2 := quintExp2_eq_two_mul_quintExpHalf b2 p j n2 hj hpj
  have he3 := quintExp2_eq_two_mul_quintExpHalf b3 p k n3 hk hpk
  simp only [quintBilateralMonomial]
  rw [show
    (PowerSeries.C (-branchSign b1) * X ^ quintExpHalf b1 p i n1) *
        (PowerSeries.C (-branchSign b2) * X ^ quintExpHalf b2 p j n2) *
        (PowerSeries.C (-branchSign b3) * X ^ quintExpHalf b3 p k n3) =
      PowerSeries.C (-(branchSign b1 * branchSign b2 * branchSign b3)) *
        X ^ (quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
          quintExpHalf b3 p k n3) by
    simp [pow_add]
    ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  have hcond :
      (K = quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
        quintExpHalf b3 p k n3) ↔
      tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 = 2 * (K : ℤ) := by
    simp only [tripleQuintExp2]
    constructor <;> intro h
    · push_cast at h
      nlinarith
    · nlinarith
  by_cases h : K = quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
      quintExpHalf b3 p k n3
  · have he := hcond.mp h
    rw [if_pos h, if_pos he]
    ring
  · have he : ¬tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 = 2 * (K : ℤ) :=
      fun he => h (hcond.mpr he)
    rw [if_neg h, if_neg he]
    ring

lemma coeff_tripleQuintupleSpecialized_eq_trunc
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) =
    coeff K (quintBilateralTrunc p i K * quintBilateralTrunc p j K *
      quintBilateralTrunc p k K) := by
  apply coeff_mul_congr_upto
  · intro a ha
    exact coeff_mul_congr_upto
      (fun x hx => coeff_quintupleSpecialized_eq_trunc p i K x hi hpi (hx.trans ha))
      (fun x hx => coeff_quintupleSpecialized_eq_trunc p j K x hj hpj (hx.trans ha))
  · intro a ha
    exact coeff_quintupleSpecialized_eq_trunc p k K a hk hpk ha

/-- **Finite triple coefficient formula.**  Every coefficient of the actual
threefold five-Pochhammer product is the signed sum over one explicit finite
box of bilateral branch points having the target doubled exponent. -/
theorem coeff_tripleQuintupleSpecialized_eq_finiteBox
    (p i j k K : ℕ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) =
      ∑ x ∈ tripleQuintBranchBox K, pointContribution p i j k K x := by
  rw [coeff_tripleQuintupleSpecialized_eq_trunc p i j k K hi hpi hj hpj hk hpk]
  simp only [quintBilateralTrunc]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [sum_tripleQuintBranchBox]
  simp_rw [Finset.sum_mul, map_sum]
  simp_rw [coeff_three_quintBilateralMonomial _ _ _ p i j k K _ _ _
    hi hpi hj hpj hk hpk]
  simp only [pointContribution, pointTripleExp2, pointBranchWeight,
    pointB1, pointB2, pointB3, pointN1, pointN2, pointN3]
  simp only [quintBranchBox]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

/-! ### Residue and boundedness facts for the reflection -/

def pointLinearResidue (i j k : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  tripleLinearResidue (pointB1 x) (pointB2 x) (pointB3 x) i j k
    (pointN1 x) (pointN2 x) (pointN3 x)

lemma tripleQuintExp2_eq_two_residue_add_p_mul
    (b1 b2 b3 : Bool) (p i j k : ℤ) (n1 n2 n3 : ℤ) :
    ∃ u : ℤ, tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 =
      2 * tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 + p * u := by
  refine ⟨n1 * (3 * n1 + if b1 then 1 else -1) +
    n2 * (3 * n2 + if b2 then 1 else -1) +
    n3 * (3 * n3 + if b3 then 1 else -1), ?_⟩
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [tripleQuintExp2, tripleLinearResidue, quintExp2, quintExpA2,
      quintExpB2] <;> ring

/-- A target exponent `p*N+r` automatically lies in the affine residue fiber
used by the short-root branch theorem. -/
lemma tripleLinearResidue_eq_progression
    (b1 b2 b3 : Bool) (p i j k : ℤ) (N : ℕ) (r n1 n2 n3 : ℤ)
    (hpodd : Odd p)
    (hexp : tripleQuintExp2 b1 b2 b3 p i j k n1 n2 n3 =
      2 * ((p : ℤ) * N + r)) :
    ∃ q : ℤ, tripleLinearResidue b1 b2 b3 i j k n1 n2 n3 = r + p * q := by
  obtain ⟨u, hu⟩ := tripleQuintExp2_eq_two_residue_add_p_mul
    b1 b2 b3 p i j k n1 n2 n3
  have hpone : (p : ZMod 2) = 1 := by
    obtain ⟨a, ha⟩ := hpodd
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [ha]
    simp [htwo]
  have hueven : Even u := by
    have hcast := congrArg (fun x : ℤ => (x : ZMod 2)) (hexp.symm.trans hu)
    have htwo : (2 : ZMod 2) = 0 := by decide
    have huzero : (u : ZMod 2) = 0 := by
      simpa [htwo, hpone] using hcast.symm
    exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp huzero)
  obtain ⟨v, hv⟩ := hueven
  refine ⟨(N : ℤ) - v, ?_⟩
  rw [hv] at hu
  nlinarith

lemma triplePoint_natAbs_le_add_one
    (p i j k K : ℕ) (x : TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hexp : pointTripleExp2 p i j k x = 2 * (K : ℤ)) :
    (pointN1 x).natAbs ≤ K + 1 ∧
      (pointN2 x).natAbs ≤ K + 1 ∧ (pointN3 x).natAbs ≤ K + 1 := by
  have he1 := quintExp2_eq_two_mul_quintExpHalf (pointB1 x) p i (pointN1 x) hi hpi
  have he2 := quintExp2_eq_two_mul_quintExpHalf (pointB2 x) p j (pointN2 x) hj hpj
  have he3 := quintExp2_eq_two_mul_quintExpHalf (pointB3 x) p k (pointN3 x) hk hpk
  have hn1 := quintExp2_nonneg (pointB1 x) p i (pointN1 x) hi hpi
  have hn2 := quintExp2_nonneg (pointB2 x) p j (pointN2 x) hj hpj
  have hn3 := quintExp2_nonneg (pointB3 x) p k (pointN3 x) hk hpk
  have hsum : quintExp2 (pointB1 x) p i (pointN1 x) +
      quintExp2 (pointB2 x) p j (pointN2 x) +
      quintExp2 (pointB3 x) p k (pointN3 x) = 2 * (K : ℤ) := by
    simpa [pointTripleExp2, tripleQuintExp2] using hexp
  have hh1 : quintExpHalf (pointB1 x) p i (pointN1 x) ≤ K := by
    exact_mod_cast (show (quintExpHalf (pointB1 x) p i (pointN1 x) : ℤ) ≤ K by
      nlinarith)
  have hh2 : quintExpHalf (pointB2 x) p j (pointN2 x) ≤ K := by
    exact_mod_cast (show (quintExpHalf (pointB2 x) p j (pointN2 x) : ℤ) ≤ K by
      nlinarith)
  have hh3 : quintExpHalf (pointB3 x) p k (pointN3 x) ≤ K := by
    exact_mod_cast (show (quintExpHalf (pointB3 x) p k (pointN3 x) : ℤ) ≤ K by
      nlinarith)
  refine ⟨?_, ?_, ?_⟩
  · exact (quintExp2_natAbs_le_add_one (pointB1 x) p i
      (quintExpHalf (pointB1 x) p i (pointN1 x)) (pointN1 x) hi hpi he1).trans (by omega)
  · exact (quintExp2_natAbs_le_add_one (pointB2 x) p j
      (quintExpHalf (pointB2 x) p j (pointN2 x)) (pointN2 x) hj hpj he2).trans (by omega)
  · exact (quintExp2_natAbs_le_add_one (pointB3 x) p k
      (quintExpHalf (pointB3 x) p k (pointN3 x)) (pointN3 x) hk hpk he3).trans (by omega)

/-! ### Deterministic residue quotients and partner specifications -/

noncomputable def pointResidueQuotient
    (p i j k : ℕ) (r : ℤ) (x : TripleQuintBranchIndex) : ℤ :=
  by
    classical
    exact if h : ∃ q : ℤ, pointLinearResidue i j k x = r + (p : ℤ) * q then
      Classical.choose h
    else 0

lemma pointLinearResidue_eq_add_mul_quotient
    (p i j k : ℕ) (r : ℤ) (x : TripleQuintBranchIndex)
    (h : ∃ q : ℤ, pointLinearResidue i j k x = r + (p : ℤ) * q) :
    pointLinearResidue i j k x =
      r + (p : ℤ) * pointResidueQuotient p i j k r x := by
  rw [pointResidueQuotient, dif_pos h]
  exact Classical.choose_spec h

lemma quintBranchIndex_eq_of_coord_eq
    (p i : ℤ) (hp : p ≠ 0) (x y : QuintBranchIndex)
    (hcoord : quintLatticeCoord x.1 p i x.2 = quintLatticeCoord y.1 p i y.2) :
    x = y := by
  rcases x with ⟨b, n⟩
  rcases y with ⟨b', n'⟩
  cases b <;> cases b'
  · simp only [quintLatticeCoord, Bool.false_eq_true, if_false] at hcoord
    have hmul : p * (6 * n - 1) = p * (6 * n' - 1) := by
      linear_combination hcoord
    have := mul_left_cancel₀ hp hmul
    congr
    omega
  · simp only [quintLatticeCoord, Bool.false_eq_true, if_false, if_true] at hcoord
    have hmul : p * (6 * n - 1) = p * (6 * n' + 1) := by
      linear_combination hcoord
    have := mul_left_cancel₀ hp hmul
    exfalso
    omega
  · simp only [quintLatticeCoord, Bool.false_eq_true, if_false, if_true] at hcoord
    have hmul : p * (6 * n + 1) = p * (6 * n' - 1) := by
      linear_combination hcoord
    have := mul_left_cancel₀ hp hmul
    exfalso
    omega
  · simp only [quintLatticeCoord, if_true] at hcoord
    have hmul : p * (6 * n + 1) = p * (6 * n' + 1) := by
      linear_combination hcoord
    have := mul_left_cancel₀ hp hmul
    congr
    omega

def pointCoord1 (p i : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  quintLatticeCoord (pointB1 x) p i (pointN1 x)
def pointCoord2 (p j : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  quintLatticeCoord (pointB2 x) p j (pointN2 x)
def pointCoord3 (p k : ℕ) (x : TripleQuintBranchIndex) : ℤ :=
  quintLatticeCoord (pointB3 x) p k (pointN3 x)

def positivePartnerSpec
    (p i j k : ℕ) (c r h : ℤ)
    (x y : TripleQuintBranchIndex) : Prop :=
  let qx := pointResidueQuotient p i j k r x
  pointBranchWeight y = -pointBranchWeight x ∧
    pointTripleExp2 p i j k y = pointTripleExp2 p i j k x ∧
    pointResidueQuotient p i j k r y = -h - qx ∧
    pointCoord1 p i y = shortRootReflectCoord c ((p : ℤ) * (h + 2 * qx)) i
      (pointCoord1 p i x) ∧
    pointCoord2 p j y = shortRootReflectCoord c ((p : ℤ) * (h + 2 * qx)) j
      (pointCoord2 p j x) ∧
    pointCoord3 p k y = shortRootReflectCoord c ((p : ℤ) * (h + 2 * qx)) k
      (pointCoord3 p k x) ∧
    shortRootReflectCoord c (-((p : ℤ) * (h + 2 * qx))) i
      (pointCoord1 p i y) = pointCoord1 p i x ∧
    shortRootReflectCoord c (-((p : ℤ) * (h + 2 * qx))) j
      (pointCoord2 p j y) = pointCoord2 p j x ∧
    shortRootReflectCoord c (-((p : ℤ) * (h + 2 * qx))) k
      (pointCoord3 p k y) = pointCoord3 p k x

/-- Doubled exponent of the coefficient in the progression `p*N+R`, written
directly in integers to keep all reflection predicates syntactically stable. -/
def progressionTarget (p N R : ℕ) : ℤ :=
  2 * ((p : ℤ) * (N : ℤ) + (R : ℤ))

lemma progressionTarget_eq_cast (p N R : ℕ) :
    progressionTarget p N R = 2 * ((p * N + R : ℕ) : ℤ) := by
  simp [progressionTarget]

lemma positivePartnerSpec_unique_return
    (p i j k : ℕ) (c r h : ℤ) (hp : (p : ℤ) ≠ 0)
    (x y z : TripleQuintBranchIndex)
    (hxy : positivePartnerSpec p i j k c r h x y)
    (hyz : positivePartnerSpec p i j k c r h y z) :
    z = x := by
  dsimp [positivePartnerSpec] at hxy hyz
  have hq := hxy.2.2.1
  have hc1 : pointCoord1 p i z = pointCoord1 p i x := by
    rw [hyz.2.2.2.1, hq]
    convert hxy.2.2.2.2.2.2.1 using 1 <;> ring
  have hc2 : pointCoord2 p j z = pointCoord2 p j x := by
    rw [hyz.2.2.2.2.1, hq]
    convert hxy.2.2.2.2.2.2.2.1 using 1 <;> ring
  have hc3 : pointCoord3 p k z = pointCoord3 p k x := by
    rw [hyz.2.2.2.2.2.1, hq]
    convert hxy.2.2.2.2.2.2.2.2 using 1 <;> ring
  apply Prod.ext
  · apply Prod.ext
    · exact quintBranchIndex_eq_of_coord_eq p i hp z.1.1 x.1.1 (by simpa [pointCoord1] using hc1)
    · exact quintBranchIndex_eq_of_coord_eq p j hp z.1.2 x.1.2 (by simpa [pointCoord2] using hc2)
  · exact quintBranchIndex_eq_of_coord_eq p k hp z.2 x.2 (by simpa [pointCoord3] using hc3)

lemma exists_positivePartner
    (p i j k N R : ℕ) (e c h : ℤ) (x : TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm (i : ℤ) j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * (R : ℤ) = (i : ℤ) + j + k - 6 * e + p * h)
    (hexp : pointTripleExp2 p i j k x = progressionTarget p N R) :
    ∃ y ∈ tripleQuintBranchBox (p * N + R),
      positivePartnerSpec p i j k c R h x y := by
  obtain ⟨q, hres⟩ := tripleLinearResidue_eq_progression
    (pointB1 x) (pointB2 x) (pointB3 x) p i j k N R
    (pointN1 x) (pointN2 x) (pointN3 x) hpodd (by
      simpa [pointTripleExp2] using hexp)
  obtain ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
      htargetResidue, hcoord1, hcoord2, hcoord3, hexponent,
      hreturn1, hreturn2, hreturn3⟩ :=
    directRoot_positive_eight_branch_matching
      (pointB1 x) (pointB2 x) (pointB3 x) p e c i j k
      (pointN1 x) (pointN2 x) (pointN3 x) R q h
      hpodd he hep hroot hcoefficient
      (by simpa [pointLinearResidue] using hres) htarget
  let y : TripleQuintBranchIndex :=
    (((b1', pointN1 x + z1), (b2', pointN2 x + z2)),
      (b3', pointN3 x + z3))
  have hyexp : pointTripleExp2 p i j k y = 2 * ((p * N + R : ℕ) : ℤ) := by
    rw [show pointTripleExp2 p i j k y = pointTripleExp2 p i j k x by
      simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1, pointN2,
        pointN3] using hexponent.symm]
    simpa [progressionTarget] using hexp
  have hybounds := triplePoint_natAbs_le_add_one p i j k (p * N + R) y
    hi hpi hj hpj hk hpk hyexp
  have hymem : y ∈ tripleQuintBranchBox (p * N + R) := by
    rw [tripleQuintBranchBox]
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.1
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.2.1
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.2.2
  have hxExists : ∃ qx : ℤ, pointLinearResidue i j k x = R + (p : ℤ) * qx :=
    ⟨q, by simpa [pointLinearResidue] using hres⟩
  have hxquot := pointLinearResidue_eq_add_mul_quotient p i j k R x hxExists
  have hqx : pointResidueQuotient p i j k R x = q := by
    have hpne : (p : ℤ) ≠ 0 := by
      exact_mod_cast (show p ≠ 0 by omega)
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R x =
          pointLinearResidue i j k x - R := by linarith [hxquot]
      _ = (p : ℤ) * q := by
        simpa [pointLinearResidue] using congrArg (fun t => t - (R : ℤ)) hres
  have hyExists : ∃ qy : ℤ, pointLinearResidue i j k y = R + (p : ℤ) * qy := by
    refine ⟨-h - q, ?_⟩
    simpa [pointLinearResidue, y, pointB1, pointB2, pointB3, pointN1, pointN2,
      pointN3] using htargetResidue
  have hyquot := pointLinearResidue_eq_add_mul_quotient p i j k R y hyExists
  have hpne : (p : ℤ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  have hqy : pointResidueQuotient p i j k R y = -h - q := by
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R y =
          pointLinearResidue i j k y - R := by linarith [hyquot]
      _ = (p : ℤ) * (-h - q) := by
        have hyqeq : pointLinearResidue i j k y = R + (p : ℤ) * (-h - q) := by
          simpa [pointLinearResidue, y, pointB1, pointB2, pointB3, pointN1,
            pointN2, pointN3] using htargetResidue
        linarith
  refine ⟨y, hymem, ?_⟩
  dsimp [positivePartnerSpec]
  rw [hqx]
  refine ⟨?_, ?_, hqy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
    rw [hproduct]
    simp [pointB1, pointB2, pointB3]
  · simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1, pointN2,
      pointN3] using hexponent.symm
  · simpa [pointCoord1, y, pointB1, pointN1] using hcoord1
  · simpa [pointCoord2, y, pointB2, pointN2] using hcoord2
  · simpa [pointCoord3, y, pointB3, pointN3] using hcoord3
  · simpa [pointCoord1, y, pointB1, pointN1] using hreturn1
  · simpa [pointCoord2, y, pointB2, pointN2] using hreturn2
  · simpa [pointCoord3, y, pointB3, pointN3] using hreturn3

/-- **Positive short-root cancellation theorem.**  Under the positive target
residue equation, the short-root reflection is a fixed-point-free,
sign-reversing involution of the complete finite coefficient box. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_positive_shortRoot
    (p i j k N R : ℕ) (e c h : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 1)
    (hroot : ternaryNorm (i : ℤ) j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * (R : ℤ) = (i : ℤ) + j + k - 6 * e + p * h) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k (p * N + R)
    hi hpi hj hpj hk hpk]
  let s := tripleQuintBranchBox (p * N + R)
  let partner : ∀ x ∈ s, TripleQuintBranchIndex := fun x _ =>
    if hx : pointTripleExp2 p i j k x = progressionTarget p N R then
      Classical.choose (exists_positivePartner p i j k N R e c h x
        hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hx)
    else x
  have partner_mem : ∀ x (hx : x ∈ s), partner x hx ∈ s := by
    intro x hx
    dsimp [partner]
    split_ifs with hexp
    · exact (Classical.choose_spec (exists_positivePartner p i j k N R e c h x
        hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hexp)).1
    · exact hx
  have partner_spec : ∀ x (hx : x ∈ s),
      pointTripleExp2 p i j k x = progressionTarget p N R →
      positivePartnerSpec p i j k c R h x (partner x hx) := by
    intro x hx hexp
    dsimp [partner]
    simp only [dif_pos hexp]
    exact (Classical.choose_spec (exists_positivePartner p i j k N R e c h x
      hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hexp)).2
  change (∑ x ∈ s, pointContribution p i j k (p * N + R) x) = 0
  refine Finset.sum_involution partner ?_ ?_ partner_mem ?_
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = progressionTarget p N R
    · have hspec := partner_spec x hx hexp
      have hpartnerExp : pointTripleExp2 p i j k (partner x hx) =
          progressionTarget p N R := hspec.2.1.trans hexp
      have hexp' : pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hexp
      have hpartnerExp' : pointTripleExp2 p i j k (partner x hx) =
          2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hpartnerExp
      simp [pointContribution, hexp', hpartnerExp', hspec.1]
    · have hself : partner x hx = x := by
        dsimp [partner]
        rw [dif_neg hexp]
      have hexp' : ¬pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hexp
      rw [pointContribution, if_neg hexp', hself, pointContribution, if_neg hexp']
      simp
  · intro x hx hnonzero
    have hexp' : pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
      by_contra hne
      rw [pointContribution, if_neg hne] at hnonzero
      exact hnonzero rfl
    have hexp : pointTripleExp2 p i j k x = progressionTarget p N R := by
      simpa [progressionTarget] using hexp'
    have hspec := partner_spec x hx hexp
    intro heq
    have hweight : pointBranchWeight x = -pointBranchWeight x := by
      simpa [heq] using hspec.1
    have hweight_ne : pointBranchWeight x ≠ 0 := by
      rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
      cases b1 <;> cases b2 <;> cases b3 <;>
        norm_num [pointBranchWeight, pointB1, pointB2, pointB3, branchSign]
    apply hweight_ne
    nlinarith
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = progressionTarget p N R
    · have hxy := partner_spec x hx hexp
      have hyexp : pointTripleExp2 p i j k (partner x hx) =
          progressionTarget p N R := hxy.2.1.trans hexp
      have hyz := partner_spec (partner x hx) (partner_mem x hx) hyexp
      have hpne : (p : ℤ) ≠ 0 := by
        rintro hpzero
        have : p = 0 := by exact_mod_cast hpzero
        omega
      exact positivePartnerSpec_unique_return p i j k c R h hpne
        x (partner x hx) (partner (partner x hx) (partner_mem x hx)) hxy hyz
    · have hself : partner x hx = x := by simp [partner, hexp]
      have hyexp : ¬pointTripleExp2 p i j k (partner x hx) = progressionTarget p N R := by
        simpa [hself] using hexp
      have hsecond : partner (partner x hx) (partner_mem x hx) = partner x hx := by
        dsimp [partner]
        rw [dif_neg hyexp]
      exact hsecond.trans hself

def negativePartnerSpec
    (p i j k : ℕ) (e c r h : ℤ)
    (x y : TripleQuintBranchIndex) : Prop :=
  let qx := pointResidueQuotient p i j k r x
  let t := (p : ℤ) * (h + 2 * qx) + 6 * e
  pointBranchWeight y = -pointBranchWeight x ∧
    pointTripleExp2 p i j k y = pointTripleExp2 p i j k x ∧
    pointResidueQuotient p i j k r y = qx ∧
    pointCoord1 p i y = -shortRootReflectCoord c t i (pointCoord1 p i x) ∧
    pointCoord2 p j y = -shortRootReflectCoord c t j (pointCoord2 p j x) ∧
    pointCoord3 p k y = -shortRootReflectCoord c t k (pointCoord3 p k x) ∧
    -shortRootReflectCoord c t i (pointCoord1 p i y) = pointCoord1 p i x ∧
    -shortRootReflectCoord c t j (pointCoord2 p j y) = pointCoord2 p j x ∧
    -shortRootReflectCoord c t k (pointCoord3 p k y) = pointCoord3 p k x

lemma negativePartnerSpec_unique_return
    (p i j k : ℕ) (e c r h : ℤ) (hp : (p : ℤ) ≠ 0)
    (x y z : TripleQuintBranchIndex)
    (hxy : negativePartnerSpec p i j k e c r h x y)
    (hyz : negativePartnerSpec p i j k e c r h y z) :
    z = x := by
  dsimp [negativePartnerSpec] at hxy hyz
  have hq := hxy.2.2.1
  have hc1 : pointCoord1 p i z = pointCoord1 p i x := by
    rw [hyz.2.2.2.1, hq]
    exact hxy.2.2.2.2.2.2.1
  have hc2 : pointCoord2 p j z = pointCoord2 p j x := by
    rw [hyz.2.2.2.2.1, hq]
    exact hxy.2.2.2.2.2.2.2.1
  have hc3 : pointCoord3 p k z = pointCoord3 p k x := by
    rw [hyz.2.2.2.2.2.1, hq]
    exact hxy.2.2.2.2.2.2.2.2
  apply Prod.ext
  · apply Prod.ext
    · exact quintBranchIndex_eq_of_coord_eq p i hp z.1.1 x.1.1 (by simpa [pointCoord1] using hc1)
    · exact quintBranchIndex_eq_of_coord_eq p j hp z.1.2 x.1.2 (by simpa [pointCoord2] using hc2)
  · exact quintBranchIndex_eq_of_coord_eq p k hp z.2 x.2 (by simpa [pointCoord3] using hc3)

lemma exists_negativePartner
    (p i j k N R : ℕ) (e c h : ℤ) (x : TripleQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm (i : ℤ) j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * (R : ℤ) = (i : ℤ) + j + k + p * h)
    (hexp : pointTripleExp2 p i j k x = progressionTarget p N R) :
    ∃ y ∈ tripleQuintBranchBox (p * N + R),
      negativePartnerSpec p i j k e c R h x y := by
  obtain ⟨q, hres⟩ := tripleLinearResidue_eq_progression
    (pointB1 x) (pointB2 x) (pointB3 x) p i j k N R
    (pointN1 x) (pointN2 x) (pointN3 x) hpodd (by
      simpa [pointTripleExp2] using hexp)
  obtain ⟨b1', b2', b3', z1, z2, z3, hz1, hz2, hz3, hproduct,
      htargetResidue, hcoord1, hcoord2, hcoord3, hexponent,
      hreturn1, hreturn2, hreturn3⟩ :=
    directRoot_negative_eight_branch_matching
      (pointB1 x) (pointB2 x) (pointB3 x) p e c i j k
      (pointN1 x) (pointN2 x) (pointN3 x) R q h
      hpodd he hep hroot hcoefficient
      (by simpa [pointLinearResidue] using hres) htarget
  let y : TripleQuintBranchIndex :=
    (((b1', -pointN1 x + z1), (b2', -pointN2 x + z2)),
      (b3', -pointN3 x + z3))
  have hyexp : pointTripleExp2 p i j k y = 2 * ((p * N + R : ℕ) : ℤ) := by
    rw [show pointTripleExp2 p i j k y = pointTripleExp2 p i j k x by
      simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1, pointN2,
        pointN3] using hexponent.symm]
    simpa [progressionTarget] using hexp
  have hybounds := triplePoint_natAbs_le_add_one p i j k (p * N + R) y
    hi hpi hj hpj hk hpk hyexp
  have hymem : y ∈ tripleQuintBranchBox (p * N + R) := by
    rw [tripleQuintBranchBox]
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.1
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.2.1
    · exact mem_quintBranchBox_of_natAbs_le _ _ _ hybounds.2.2
  have hxExists : ∃ qx : ℤ, pointLinearResidue i j k x = R + (p : ℤ) * qx :=
    ⟨q, by simpa [pointLinearResidue] using hres⟩
  have hxquot := pointLinearResidue_eq_add_mul_quotient p i j k R x hxExists
  have hpne : (p : ℤ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  have hqx : pointResidueQuotient p i j k R x = q := by
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R x =
          pointLinearResidue i j k x - R := by linarith [hxquot]
      _ = (p : ℤ) * q := by
        simpa [pointLinearResidue] using congrArg (fun t => t - (R : ℤ)) hres
  have hyExists : ∃ qy : ℤ, pointLinearResidue i j k y = R + (p : ℤ) * qy := by
    refine ⟨q, ?_⟩
    simpa [pointLinearResidue, y, pointB1, pointB2, pointB3, pointN1, pointN2,
      pointN3] using htargetResidue
  have hyquot := pointLinearResidue_eq_add_mul_quotient p i j k R y hyExists
  have hqy : pointResidueQuotient p i j k R y = q := by
    apply mul_left_cancel₀ hpne
    calc
      (p : ℤ) * pointResidueQuotient p i j k R y =
          pointLinearResidue i j k y - R := by linarith [hyquot]
      _ = (p : ℤ) * q := by
        have hyqeq : pointLinearResidue i j k y = R + (p : ℤ) * q := by
          simpa [pointLinearResidue, y, pointB1, pointB2, pointB3, pointN1,
            pointN2, pointN3] using htargetResidue
        linarith
  refine ⟨y, hymem, ?_⟩
  dsimp [negativePartnerSpec]
  rw [hqx]
  refine ⟨?_, ?_, hqy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [pointBranchWeight, y, pointB1, pointB2, pointB3]
    rw [hproduct]
    simp [pointB1, pointB2, pointB3]
  · simpa [pointTripleExp2, y, pointB1, pointB2, pointB3, pointN1, pointN2,
      pointN3] using hexponent.symm
  · simpa [pointCoord1, y, pointB1, pointN1] using hcoord1
  · simpa [pointCoord2, y, pointB2, pointN2] using hcoord2
  · simpa [pointCoord3, y, pointB3, pointN3] using hcoord3
  · simpa [pointCoord1, y, pointB1, pointN1] using hreturn1
  · simpa [pointCoord2, y, pointB2, pointN2] using hreturn2
  · simpa [pointCoord3, y, pointB3, pointN3] using hreturn3

/-- **Negative short-root cancellation theorem.**  In the complementary
`e*p = 2 (mod 3)` case, the sign-corrected reflection `-R` cancels the full
finite coefficient box. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_negative_shortRoot
    (p i j k N R : ℕ) (e c h : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hep : ((e * (p : ℤ) : ℤ) : ZMod 3) = 2)
    (hroot : ternaryNorm (i : ℤ) j k = e * p)
    (hcoefficient : c * e = 2)
    (htarget : 2 * (R : ℤ) = (i : ℤ) + j + k + p * h) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rw [coeff_tripleQuintupleSpecialized_eq_finiteBox p i j k (p * N + R)
    hi hpi hj hpj hk hpk]
  let s := tripleQuintBranchBox (p * N + R)
  let partner : ∀ x ∈ s, TripleQuintBranchIndex := fun x _ =>
    if hx : pointTripleExp2 p i j k x = progressionTarget p N R then
      Classical.choose (exists_negativePartner p i j k N R e c h x
        hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hx)
    else x
  have partner_mem : ∀ x (hx : x ∈ s), partner x hx ∈ s := by
    intro x hx
    dsimp [partner]
    split_ifs with hexp
    · exact (Classical.choose_spec (exists_negativePartner p i j k N R e c h x
        hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hexp)).1
    · exact hx
  have partner_spec : ∀ x (hx : x ∈ s),
      pointTripleExp2 p i j k x = progressionTarget p N R →
      negativePartnerSpec p i j k e c R h x (partner x hx) := by
    intro x hx hexp
    dsimp [partner]
    simp only [dif_pos hexp]
    exact (Classical.choose_spec (exists_negativePartner p i j k N R e c h x
      hi hpi hj hpj hk hpk hpodd he hep hroot hcoefficient htarget hexp)).2
  change (∑ x ∈ s, pointContribution p i j k (p * N + R) x) = 0
  refine Finset.sum_involution partner ?_ ?_ partner_mem ?_
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = progressionTarget p N R
    · have hspec := partner_spec x hx hexp
      have hpartnerExp : pointTripleExp2 p i j k (partner x hx) =
          progressionTarget p N R := hspec.2.1.trans hexp
      have hexp' : pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hexp
      have hpartnerExp' : pointTripleExp2 p i j k (partner x hx) =
          2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hpartnerExp
      simp [pointContribution, hexp', hpartnerExp', hspec.1]
    · have hself : partner x hx = x := by
        dsimp [partner]
        rw [dif_neg hexp]
      have hexp' : ¬pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
        simpa [progressionTarget] using hexp
      rw [pointContribution, if_neg hexp', hself, pointContribution, if_neg hexp']
      simp
  · intro x hx hnonzero
    have hexp' : pointTripleExp2 p i j k x = 2 * ((p * N + R : ℕ) : ℤ) := by
      by_contra hne
      rw [pointContribution, if_neg hne] at hnonzero
      exact hnonzero rfl
    have hexp : pointTripleExp2 p i j k x = progressionTarget p N R := by
      simpa [progressionTarget] using hexp'
    have hspec := partner_spec x hx hexp
    intro heq
    have hweight : pointBranchWeight x = -pointBranchWeight x := by
      simpa [heq] using hspec.1
    have hweight_ne : pointBranchWeight x ≠ 0 := by
      rcases x with ⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩
      cases b1 <;> cases b2 <;> cases b3 <;>
        norm_num [pointBranchWeight, pointB1, pointB2, pointB3, branchSign]
    apply hweight_ne
    nlinarith
  · intro x hx
    by_cases hexp : pointTripleExp2 p i j k x = progressionTarget p N R
    · have hxy := partner_spec x hx hexp
      have hyexp : pointTripleExp2 p i j k (partner x hx) =
          progressionTarget p N R := hxy.2.1.trans hexp
      have hyz := partner_spec (partner x hx) (partner_mem x hx) hyexp
      have hpne : (p : ℤ) ≠ 0 := by
        rintro hpzero
        have : p = 0 := by exact_mod_cast hpzero
        omega
      exact negativePartnerSpec_unique_return p i j k e c R h hpne
        x (partner x hx) (partner (partner x hx) (partner_mem x hx)) hxy hyz
    · have hself : partner x hx = x := by simp [partner, hexp]
      have hyexp : ¬pointTripleExp2 p i j k (partner x hx) = progressionTarget p N R := by
        simpa [hself] using hexp
      have hsecond : partner (partner x hx) (partner_mem x hx) = partner x hx := by
        dsimp [partner]
        rw [dif_neg hyexp]
      exact hsecond.trans hself

/-- **Unified short-root vanishing theorem.**  Either of the two integral
branch-closing reflection cases proves the entire coefficient progression
zero in the actual sparse triple product. -/
theorem coeff_tripleQuintupleSpecialized_eq_zero_of_shortRoot
    (p i j k N R : ℕ) (e c : ℤ)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hpodd : Odd (p : ℤ)) (he : e = 1 ∨ e = 2)
    (hroot : ternaryNorm (i : ℤ) j k = e * p)
    (hcoefficient : c * e = 2)
    (hcase :
      (((e * (p : ℤ) : ℤ) : ZMod 3) = 1 ∧
        ∃ h : ℤ, 2 * (R : ℤ) = (i : ℤ) + j + k - 6 * e + p * h) ∨
      (((e * (p : ℤ) : ℤ) : ZMod 3) = 2 ∧
        ∃ h : ℤ, 2 * (R : ℤ) = (i : ℤ) + j + k + p * h)) :
    coeff (p * N + R) (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k) = 0 := by
  rcases hcase with ⟨hep, h, htarget⟩ | ⟨hep, h, htarget⟩
  · exact coeff_tripleQuintupleSpecialized_eq_zero_of_positive_shortRoot
      p i j k N R e c h hi hpi hj hpj hk hpk hpodd he hep hroot
      hcoefficient htarget
  · exact coeff_tripleQuintupleSpecialized_eq_zero_of_negative_shortRoot
      p i j k N R e c h hi hpi hj hpj hk hpk hpodd he hep hroot
      hcoefficient htarget

/-- The direct short root `(1,2,3)` gives a second, reflection-theoretic proof
of the `7n+3` vanishing in the first exact sparse triple. -/
theorem coeff_quintupleSpecialized_p7_three_zero_by_shortRoot (N : ℕ) :
    coeff (7 * N + 3) (quintupleSpecialized 7 1 * quintupleSpecialized 7 2 *
      quintupleSpecialized 7 3) = 0 := by
  apply coeff_tripleQuintupleSpecialized_eq_zero_of_negative_shortRoot
    7 1 2 3 N 3 2 1 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨3, by norm_num⟩
  · exact Or.inr rfl
  · have hthree : (3 : ZMod 3) = 0 := by decide
    change (14 : ZMod 3) = 2
    linear_combination 4 * hthree
  · norm_num [ternaryNorm]
  · norm_num
  · norm_num

end Ramanujan.MultiQuintuple
