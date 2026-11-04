/-
# Four-factor Watson coefficient boxes and exact cancellation

This extends the actual infinite-product coefficient bridge to four factors.
No bounded coefficient scan is used to infer persistent vanishing.
-/
import RamanujanTau.MultiQuintupleProjectiveCancellation

namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

abbrev QuadQuintBranchIndex := TripleQuintBranchIndex × QuintBranchIndex

def quadB1 (x : QuadQuintBranchIndex) : Bool := pointB1 x.1
def quadB2 (x : QuadQuintBranchIndex) : Bool := pointB2 x.1
def quadB3 (x : QuadQuintBranchIndex) : Bool := pointB3 x.1
def quadB4 (x : QuadQuintBranchIndex) : Bool := x.2.1
def quadN1 (x : QuadQuintBranchIndex) : ℤ := pointN1 x.1
def quadN2 (x : QuadQuintBranchIndex) : ℤ := pointN2 x.1
def quadN3 (x : QuadQuintBranchIndex) : ℤ := pointN3 x.1
def quadN4 (x : QuadQuintBranchIndex) : ℤ := x.2.2

def quadExp2 (p i j k l : ℕ) (x : QuadQuintBranchIndex) : ℤ :=
  pointTripleExp2 p i j k x.1 + quintExp2 (quadB4 x) p l (quadN4 x)

def quadWeight (x : QuadQuintBranchIndex) : ℤ :=
  pointBranchWeight x.1 * (-branchSign (quadB4 x))

def quadContribution (p i j k l K : ℕ) (x : QuadQuintBranchIndex) : ℤ :=
  if quadExp2 p i j k l x = 2 * (K : ℤ) then quadWeight x else 0

noncomputable def quadBox (K : ℕ) : Finset QuadQuintBranchIndex :=
  (tripleQuintBranchBox K).product (quintBranchBox K)

lemma sum_quadBox (K : ℕ) (f : QuadQuintBranchIndex → ℤ) :
    (∑ x ∈ quadBox K, f x) =
      ∑ x1 ∈ quintBranchBox K, ∑ x2 ∈ quintBranchBox K,
        ∑ x3 ∈ quintBranchBox K, ∑ x4 ∈ quintBranchBox K,
          f (((x1,x2),x3),x4) := by
  rw [quadBox]
  calc
    _ = ∑ x ∈ tripleQuintBranchBox K, ∑ y ∈ quintBranchBox K, f (x,y) :=
      Finset.sum_product _ _ _
    _ = _ := sum_tripleQuintBranchBox K _

private lemma coeff_four_monomials
    (b1 b2 b3 b4 : Bool) (p i j k l K : ℕ) (n1 n2 n3 n4 : ℤ)
    (hi : 0 < i) (hpi : 2*i < p) (hj : 0 < j) (hpj : 2*j < p)
    (hk : 0 < k) (hpk : 2*k < p) (hl : 0 < l) (hpl : 2*l < p) :
    coeff K (quintBilateralMonomial b1 p i n1 * quintBilateralMonomial b2 p j n2 *
      quintBilateralMonomial b3 p k n3 * quintBilateralMonomial b4 p l n4) =
      quadContribution p i j k l K ((((b1,n1),(b2,n2)),(b3,n3)),(b4,n4)) := by
  have he1 := quintExp2_eq_two_mul_quintExpHalf b1 p i n1 hi hpi
  have he2 := quintExp2_eq_two_mul_quintExpHalf b2 p j n2 hj hpj
  have he3 := quintExp2_eq_two_mul_quintExpHalf b3 p k n3 hk hpk
  have he4 := quintExp2_eq_two_mul_quintExpHalf b4 p l n4 hl hpl
  simp only [quintBilateralMonomial]
  rw [show
    (PowerSeries.C (-branchSign b1) * X ^ quintExpHalf b1 p i n1) *
      (PowerSeries.C (-branchSign b2) * X ^ quintExpHalf b2 p j n2) *
      (PowerSeries.C (-branchSign b3) * X ^ quintExpHalf b3 p k n3) *
      (PowerSeries.C (-branchSign b4) * X ^ quintExpHalf b4 p l n4) =
      PowerSeries.C (branchSign b1 * branchSign b2 * branchSign b3 * branchSign b4) *
        X ^ (quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
          quintExpHalf b3 p k n3 + quintExpHalf b4 p l n4) by
    simp [pow_add]; ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  simp only [quadContribution, quadExp2, quadWeight, pointTripleExp2,
    pointBranchWeight, pointB1, pointB2, pointB3, pointN1, pointN2, pointN3,
    quadB4, quadN4, tripleQuintExp2]
  have he : (K = quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
      quintExpHalf b3 p k n3 + quintExpHalf b4 p l n4) ↔
      quintExp2 b1 p i n1 + quintExp2 b2 p j n2 + quintExp2 b3 p k n3 +
      quintExp2 b4 p l n4 = 2*(K : ℤ) := by
    constructor <;> intro h
    · push_cast at h; nlinarith
    · nlinarith
  by_cases h : K = quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
      quintExpHalf b3 p k n3 + quintExpHalf b4 p l n4
  · rw [if_pos h, if_pos (he.mp h)]; ring
  · rw [if_neg h, if_neg (fun hh => h (he.mpr hh))]; ring

/-- Coefficients of the actual four infinite products are finite Watson sums. -/
theorem coeff_quad_eq_finiteBox (p i j k l K : ℕ)
    (hi : 0 < i) (hpi : 2*i < p) (hj : 0 < j) (hpj : 2*j < p)
    (hk : 0 < k) (hpk : 2*k < p) (hl : 0 < l) (hpl : 2*l < p) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k * quintupleSpecialized p l) =
    ∑ x ∈ quadBox K, quadContribution p i j k l K x := by
  have hc : coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k * quintupleSpecialized p l) =
    coeff K (quintBilateralTrunc p i K * quintBilateralTrunc p j K *
      quintBilateralTrunc p k K * quintBilateralTrunc p l K) := by
    apply coeff_mul_congr_upto
    · intro a ha
      apply coeff_mul_congr_upto
      · intro b hb
        exact coeff_mul_congr_upto
          (fun c hc => coeff_quintupleSpecialized_eq_trunc p i K c hi hpi (hc.trans (hb.trans ha)))
          (fun c hc => coeff_quintupleSpecialized_eq_trunc p j K c hj hpj (hc.trans (hb.trans ha)))
      · intro b hb
        exact coeff_quintupleSpecialized_eq_trunc p k K b hk hpk (hb.trans ha)
    · intro a ha
      exact coeff_quintupleSpecialized_eq_trunc p l K a hl hpl ha
  rw [hc, sum_quadBox]
  simp only [quintBilateralTrunc, quintBranchBox]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum]
  simp_rw [Finset.sum_mul, map_sum]
  simp_rw [coeff_four_monomials _ _ _ _ p i j k l K _ _ _ _ hi hpi hj hpj hk hpk hl hpl]
  apply Finset.sum_congr rfl
  intro x hx
  let s := (Finset.univ : Finset Bool).product (quintBranchInterval K)
  calc
    _ = ∑ y ∈ s, ∑ z ∈ s, ∑ w ∈ s,
        quadContribution p i j k l K (((x,z),w),y) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ z ∈ s, ∑ y ∈ s, ∑ w ∈ s,
        quadContribution p i j k l K (((x,z),w),y) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact Finset.sum_comm

lemma mem_quadBox_of_exp (p i j k l K : ℕ) (x : QuadQuintBranchIndex)
    (hi : 0 < i) (hpi : 2*i < p) (hj : 0 < j) (hpj : 2*j < p)
    (hk : 0 < k) (hpk : 2*k < p) (hl : 0 < l) (hpl : 2*l < p)
    (hexp : quadExp2 p i j k l x = 2*(K : ℤ)) : x ∈ quadBox K := by
  rcases x with ⟨⟨⟨⟨b1,n1⟩,⟨b2,n2⟩⟩,⟨b3,n3⟩⟩,⟨b4,n4⟩⟩
  simp only [quadExp2, pointTripleExp2, pointB1, pointB2, pointB3,
    pointN1, pointN2, pointN3, quadB4, quadN4, tripleQuintExp2] at hexp
  have he1 := quintExp2_eq_two_mul_quintExpHalf b1 p i n1 hi hpi
  have he2 := quintExp2_eq_two_mul_quintExpHalf b2 p j n2 hj hpj
  have he3 := quintExp2_eq_two_mul_quintExpHalf b3 p k n3 hk hpk
  have he4 := quintExp2_eq_two_mul_quintExpHalf b4 p l n4 hl hpl
  have hs : quintExpHalf b1 p i n1 + quintExpHalf b2 p j n2 +
      quintExpHalf b3 p k n3 + quintExpHalf b4 p l n4 = K := by omega
  have hb1 := quintExp2_natAbs_le_add_one b1 p i _ n1 hi hpi he1
  have hb2 := quintExp2_natAbs_le_add_one b2 p j _ n2 hj hpj he2
  have hb3 := quintExp2_natAbs_le_add_one b3 p k _ n3 hk hpk he3
  have hb4 := quintExp2_natAbs_le_add_one b4 p l _ n4 hl hpl he4
  rw [quadBox, tripleQuintBranchBox]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨mem_quintBranchBox_of_natAbs_le K b1 n1 (by omega),
    mem_quintBranchBox_of_natAbs_le K b2 n2 (by omega)⟩,
    mem_quintBranchBox_of_natAbs_le K b3 n3 (by omega)⟩,
    mem_quintBranchBox_of_natAbs_le K b4 n4 (by omega)⟩

theorem coeff_quad_eq_zero_of_expInvolution
    (p i j k l K : ℕ) (partner : QuadQuintBranchIndex → QuadQuintBranchIndex)
    (hi : 0 < i) (hpi : 2 * i < p)
    (hj : 0 < j) (hpj : 2 * j < p)
    (hk : 0 < k) (hpk : 2 * k < p)
    (hl : 0 < l) (hpl : 2 * l < p)
    (hweight : ∀ x, quadExp2 p i j k l x = 2 * (K : ℤ) →
      quadWeight (partner x) = -quadWeight x)
    (hexponent : ∀ x, quadExp2 p i j k l x = 2 * (K : ℤ) →
      quadExp2 p i j k l (partner x) = quadExp2 p i j k l x)
    (hinvolutive : ∀ x, quadExp2 p i j k l x = 2 * (K : ℤ) →
      partner (partner x) = x) :
    coeff K (quintupleSpecialized p i * quintupleSpecialized p j *
      quintupleSpecialized p k * quintupleSpecialized p l) = 0 := by
  rw [coeff_quad_eq_finiteBox p i j k l K
    hi hpi hj hpj hk hpk hl hpl]
  let s := quadBox K
  let partnerOnBox : ∀ x ∈ s, QuadQuintBranchIndex := fun x _ =>
    if hx : quadExp2 p i j k l x = 2 * (K : ℤ) then partner x else x
  have partner_mem : ∀ x (hx : x ∈ s), partnerOnBox x hx ∈ s := by
    intro x hx
    dsimp [partnerOnBox]
    split_ifs with hexp
    · apply mem_quadBox_of_exp p i j k l K
        (partner x) hi hpi hj hpj hk hpk hl hpl
      exact (hexponent x hexp).trans hexp
    · exact hx
  change (∑ x ∈ s, quadContribution p i j k l K x) = 0
  refine Finset.sum_involution partnerOnBox ?_ ?_ partner_mem ?_
  · intro x hx
    by_cases hexp : quadExp2 p i j k l x = 2 * (K : ℤ)
    · have hpartnerExp : quadExp2 p i j k l (partner x) = 2 * (K : ℤ) :=
        (hexponent x hexp).trans hexp
      simp [partnerOnBox, quadContribution, hexp, hpartnerExp, hweight x hexp]
    · simp [partnerOnBox, quadContribution, hexp]
  · intro x hx hnonzero
    have hexp : quadExp2 p i j k l x = 2 * (K : ℤ) := by
      by_contra hne
      rw [quadContribution, if_neg hne] at hnonzero
      exact hnonzero rfl
    have hweightEq := hweight x hexp
    intro heq
    have hzero : quadWeight x = 0 := by
      rw [show partnerOnBox x hx = partner x by simp [partnerOnBox, hexp]] at heq
      rw [heq] at hweightEq
      linarith
    rcases x with ⟨⟨⟨⟨b1, n1⟩, ⟨b2, n2⟩⟩, ⟨b3, n3⟩⟩, ⟨b4, n4⟩⟩
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      norm_num [quadWeight, quadB4, pointBranchWeight, pointB1, pointB2, pointB3, branchSign] at hzero
  · intro x hx
    by_cases hexp : quadExp2 p i j k l x = 2 * (K : ℤ)
    · have hpartnerExp : quadExp2 p i j k l (partner x) = 2 * (K : ℤ) :=
        (hexponent x hexp).trans hexp
      simp [partnerOnBox, hexp, hpartnerExp, hinvolutive x hexp]
    · simp [partnerOnBox, hexp]

end Ramanujan.MultiQuintuple
