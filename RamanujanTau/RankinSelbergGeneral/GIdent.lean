/-
# Identifying the horocycle limit: `L = (3/π)‖Δ‖²`

The same box sandwich that proves convergence also brackets `‖Δ‖² = ∫_𝓕 G dμ`
(`petNormSq`): with `μᵢ = ∫_{boxᵢ} dx dy/y²`,

    ∑ c⁻ᵢ μᵢ ≤ ‖Δ‖² ≤ ∑ c⁺ᵢ μᵢ + M/L,

and the horocycle limit lies in `[(3/π)∑c⁻μ, (3/π)(∑c⁺μ + M/L)]` (`K₀/2 = 3/π`). The gap tends
to `0`, so `L = (3/π)‖Δ‖²`: **Zagier's theorem for `G`**, and hence the Rankin–Selberg asymptotic
with the explicit constant `(3/π)(4π)¹²‖Δ‖²/11!`.
-/
import RamanujanTau.RankinSelbergGeneral.GFinal
import RamanujanTau.EisensteinReal.HoroConst
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinSelbergGeneral.Horo

open RamanujanTau.EisensteinReal.Horo
open HoroFn
variable [HoroFn]

open Finset Real Filter Topology MeasureTheory ModularGroup Set
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-! ### Integrals of `1/y²` over boxes -/

lemma integral_inv_sq_Ico {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in Ico a b, 1 / y ^ 2 = 1 / a - 1 / b := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ y ∈ uIcc a b, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / y ^ 2) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have := (hasDerivAt_inv hy0).neg
    convert this using 1
    · funext t; simp [one_div]
    · field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      (fun y hy => by have : 0 < y := by linarith [hy.1]
                      positivity)

lemma integrableOn_inv_sq_Ici {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ici L) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hL
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := lt_trans hL hy
  rw [Real.rpow_neg hy0.le, Real.rpow_two, one_div]

lemma integral_inv_sq_Ici {L : ℝ} (hL : 0 < L) : ∫ y in Ici L, 1 / y ^ 2 = 1 / L := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hL
  have e : ∫ y in Ioi L, 1 / y ^ 2 = ∫ y in Ioi L, y ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : 0 < y := lt_trans hL hy
    rw [Real.rpow_neg hy0.le, Real.rpow_two, one_div]
  rw [e, h, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

lemma integrableOn_inv_sq_Ico {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ico a b) := by
  rcases le_total a b with hab | hab
  · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ico_subset_Icc_self
    exact ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      (fun y hy => by have : 0 < y := by linarith [hy.1]
                      positivity)
  · rw [Ico_eq_empty_of_le hab]; exact integrableOn_empty

/-- Real box `[α,β) × [a,b)` and real cusp `[α,β) × [L,∞)` in `ℝ²`. -/
def rbox (α β a b : ℝ) : Set (ℝ × ℝ) := Ico α β ×ˢ Ico a b
def rcusp (α β L : ℝ) : Set (ℝ × ℝ) := Ico α β ×ˢ Ici L

lemma integral_rbox {α β a b : ℝ} (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) :
    ∫ p in rbox α β a b, 1 / p.2 ^ 2 = (β - α) * (1 / a - 1 / b) := by
  unfold rbox
  rw [Measure.volume_eq_prod]
  have := setIntegral_prod_mul (μ := volume) (ν := volume) (fun _ : ℝ => (1 : ℝ))
    (fun y : ℝ => 1 / y ^ 2) (Ico α β) (Ico a b)
  simp only [one_mul] at this
  rw [this, integral_inv_sq_Ico ha hab, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

lemma integral_rcusp {α β L : ℝ} (hαβ : α ≤ β) (hL : 0 < L) :
    ∫ p in rcusp α β L, 1 / p.2 ^ 2 = (β - α) * (1 / L) := by
  unfold rcusp
  rw [Measure.volume_eq_prod]
  have := setIntegral_prod_mul (μ := volume) (ν := volume) (fun _ : ℝ => (1 : ℝ))
    (fun y : ℝ => 1 / y ^ 2) (Ico α β) (Ici L)
  simp only [one_mul] at this
  rw [this, integral_inv_sq_Ici hL, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

lemma integrableOn_rbox {α β a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (rbox α β a b) := by
  unfold rbox
  rw [Measure.volume_eq_prod]
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico α β) := integrableOn_const (by simp)
  have := (h1.mul_prod (integrableOn_inv_sq_Ico (b := b) ha))
  rw [IntegrableOn, ← Measure.prod_restrict]
  simpa using this

lemma integrableOn_rcusp {α β L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (rcusp α β L) := by
  unfold rcusp
  rw [Measure.volume_eq_prod]
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico α β) := integrableOn_const (by simp)
  have := (h1.mul_prod (integrableOn_inv_sq_Ici hL))
  rw [IntegrableOn, ← Measure.prod_restrict]
  simpa using this

/-! ### The fundamental domain integral -/

/-- `𝓕 = {|x| ≤ ½, x² + y² ≥ 1, y > 0}` in `ℝ²`. -/
def Freg : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ |p.1| ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2}

/-- `G(x+iy)/y²` (with the harmless cut-off `max y ¼` inside `G`). -/
noncomputable def gR (p : ℝ × ℝ) : ℝ := G (gpt p.1 p.2) / p.2 ^ 2

lemma measurableSet_Freg : MeasurableSet Freg := by
  have h1 : Measurable fun p : ℝ × ℝ => p.2 := measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => |p.1| := measurable_fst.abs
  have h3 : Measurable fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  exact (measurableSet_lt measurable_const h1).inter
    ((measurableSet_le h2 measurable_const).inter (measurableSet_le measurable_const h3))

lemma Freg_im {p : ℝ × ℝ} (hp : p ∈ Freg) : 1 / 2 ≤ p.2 := by
  obtain ⟨h1, h2, h3⟩ := hp
  have : p.1 ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs p.1, abs_nonneg p.1]
  nlinarith

lemma gpt_eq_ofComplex {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    UpperHalfPlane.ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = gpt p.1 p.2 := by
  have hpos : 0 < ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im := by simp; linarith
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  apply UpperHalfPlane.ext
  have hp' : (4 : ℝ)⁻¹ ≤ p.2 := by norm_num; linarith
  simp [gpt, max_eq_left hp, hp']

lemma petNormSq_eq : petNormSq = ∫ p in Freg, gR p := by
  unfold petNormSq
  refine setIntegral_congr_fun measurableSet_Freg (fun p hp => ?_)
  simp only [gR]
  rw [gpt_eq_ofComplex (by linarith [Freg_im hp])]

lemma measurable_gR : Measurable gR := by
  unfold gR
  exact ((continuous_G.comp continuous_gpt).measurable).div (measurable_snd.pow_const 2)

lemma integrableOn_gR {M : ℝ} (hM : ∀ z : ℍ, G z ≤ M) : IntegrableOn gR Freg := by
  have hsub : Freg ⊆ rcusp (-(1 / 2)) 1 (1 / 2) := by
    intro p hp
    have := Freg_im hp
    obtain ⟨-, h2, -⟩ := hp
    exact ⟨⟨(abs_le.1 h2).1, by linarith [(abs_le.1 h2).2]⟩, this⟩
  have hint : IntegrableOn (fun p : ℝ × ℝ => M * (1 / p.2 ^ 2)) Freg :=
    ((integrableOn_rcusp (α := -(1 / 2)) (β := 1) (by norm_num : (0 : ℝ) < 1 / 2)).mono_set
      hsub).const_mul M
  refine Integrable.mono' hint measurable_gR.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Freg]
  refine Filter.Eventually.of_forall fun p hp => ?_
  have hy := Freg_im hp
  unfold gR
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (G_nonneg _) (by positivity))]
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (hM _) (by positivity)

/-! ### The grid in real coordinates -/

section RealGrid
variable (K L : ℕ) (δ M : ℝ)

noncomputable def rb (i : ℕ × ℕ) : Set (ℝ × ℝ) :=
  rbox (xj K i.1) (xj K i.1 + 1 / K) (ajk K i.1 i.2) (ajk K i.1 i.2 + 1 / K)

noncomputable def upW (p : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Idx K L, cUp K δ i * (rb K i).indicator (fun _ => (1 : ℝ)) p +
    M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun _ => (1 : ℝ)) p

noncomputable def loW (p : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Idx K L, cLo K δ i * (rb K i).indicator (fun _ => (1 : ℝ)) p

end RealGrid

lemma measurableSet_rb (K : ℕ) (i : ℕ × ℕ) : MeasurableSet (rb K i) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma measurableSet_rcusp (α β L : ℝ) : MeasurableSet (rcusp α β L) :=
  measurableSet_Ico.prod measurableSet_Ici

lemma indicator_one_nonneg (s : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    0 ≤ s.indicator (fun _ => (1 : ℝ)) p := Set.indicator_nonneg (fun _ _ => zero_le_one) p

lemma bxInd_of_mem' {K : ℕ} {i : ℕ × ℕ} {w : ℍ} (h : w ∈ bx K i) : bxInd K i w = 1 :=
  boxInd_of_mem h

lemma bxInd_gpt (K : ℕ) (i : ℕ × ℕ) {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    bxInd K i (gpt p.1 p.2) = ENNReal.ofReal ((rb K i).indicator (fun _ => (1 : ℝ)) p) := by
  have hiff : gpt p.1 p.2 ∈ bx K i ↔ p ∈ rb K i := by
    unfold bx; simp only [RamanujanTau.EisensteinReal.Horo.box, rb, rbox, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ico, gpt_re, gpt_im,
      max_eq_left hp, and_assoc]
  by_cases h : p ∈ rb K i
  · rw [bxInd_of_mem' (hiff.2 h), Set.indicator_of_mem h, ENNReal.ofReal_one]
  · rw [bxInd_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h, ENNReal.ofReal_zero]

lemma ind_gpt {L : ℕ} {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    ind (-(1 / 2)) (1 / 2) L (gpt p.1 p.2) =
      ENNReal.ofReal ((rcusp (-(1 / 2)) (1 / 2) L).indicator (fun _ => (1 : ℝ)) p) := by
  have hiff : gpt p.1 p.2 ∈ rect (-(1 / 2)) (1 / 2) L ↔ p ∈ rcusp (-(1 / 2)) (1 / 2) L := by
    simp only [rect, rcusp, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ico, Set.mem_Ici, gpt_re,
      gpt_im, max_eq_left hp, and_assoc]
  unfold ind
  by_cases h : p ∈ rcusp (-(1 / 2)) (1 / 2) L
  · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h, ENNReal.ofReal_one]; rfl
  · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h,
      ENNReal.ofReal_zero]

lemma upW_nonneg {K L : ℕ} {δ M : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M) (p : ℝ × ℝ) :
    0 ≤ upW K L δ M p :=
  add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (cUp_nonneg hδ i) (indicator_one_nonneg _ _))
    (mul_nonneg hM0 (indicator_one_nonneg _ _))

lemma loW_nonneg {K L : ℕ} {δ : ℝ} (p : ℝ × ℝ) : 0 ≤ loW K L δ p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (cLo_nonneg i) (indicator_one_nonneg _ _)

lemma ofReal_upW {K L : ℕ} {δ M : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M) {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    ENNReal.ofReal (upW K L δ M p) = up K L δ M (gpt p.1 p.2) := by
  unfold upW up
  rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => mul_nonneg (cUp_nonneg hδ i)
      (indicator_one_nonneg _ _)) (mul_nonneg hM0 (indicator_one_nonneg _ _)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (cUp_nonneg hδ i)
      (indicator_one_nonneg _ _)), ENNReal.ofReal_mul hM0, ind_gpt hp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (cUp_nonneg hδ i), bxInd_gpt K i hp]

lemma ofReal_loW {K L : ℕ} {δ : ℝ} {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    ENNReal.ofReal (loW K L δ p) = lo K L δ (gpt p.1 p.2) := by
  unfold loW lo
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (cLo_nonneg i)
      (indicator_one_nonneg _ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (cLo_nonneg i), bxInd_gpt K i hp]

lemma normSq_gpt {p : ℝ × ℝ} (hp : 1 / 4 ≤ p.2) :
    Complex.normSq ((gpt p.1 p.2 : ℍ) : ℂ) = p.1 ^ 2 + p.2 ^ 2 := by
  rw [Complex.normSq_apply]
  have e1 : ((gpt p.1 p.2 : ℍ) : ℂ).re = p.1 := gpt_re _ _
  have e2 : ((gpt p.1 p.2 : ℍ) : ℂ).im = p.2 := by
    have := gpt_im p.1 p.2; rw [max_eq_left hp] at this; exact this
  rw [e1, e2]; ring

/-! ### Integrals of the grid functions -/

lemma integral_grid (K L : ℕ) (hK : 6 ≤ K) (c : ℕ × ℕ → ℝ) :
    ∫ p, (∑ i ∈ Idx K L, c i * (rb K i).indicator (fun _ => (1 : ℝ)) p) / p.2 ^ 2 =
      ∑ i ∈ Idx K L, c i * mu K i := by
  have hK' := K_pos hK
  have hpos : ∀ i ∈ Idx K L, 0 < ajk K i.1 i.2 := fun i hi =>
    lt_of_lt_of_le (by norm_num) (ajk_ge hK (Finset.mem_range.1 (Finset.mem_product.1 hi).1))
  have e : ∀ p : ℝ × ℝ, (∑ i ∈ Idx K L, c i * (rb K i).indicator (fun _ => (1 : ℝ)) p) / p.2 ^ 2 =
      ∑ i ∈ Idx K L, c i * (rb K i).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p := by
    intro p
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : p ∈ rb K i
    · simp [Set.indicator_of_mem h, div_eq_mul_inv]
    · simp [Set.indicator_of_notMem h]
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, integral_indicator (measurableSet_rb K i)]
    unfold rb mu
    rw [integral_rbox (by linarith [show (0 : ℝ) < 1 / K by positivity]) (hpos i hi)
      (by linarith [show (0 : ℝ) < 1 / K by positivity])]
  · intro i hi
    exact ((integrableOn_rbox (hpos i hi)).integrable_indicator (measurableSet_rb K i)).const_mul _

lemma integrable_grid (K L : ℕ) (hK : 6 ≤ K) (c : ℕ × ℕ → ℝ) :
    Integrable fun p : ℝ × ℝ =>
      (∑ i ∈ Idx K L, c i * (rb K i).indicator (fun _ => (1 : ℝ)) p) / p.2 ^ 2 := by
  have hpos : ∀ i ∈ Idx K L, 0 < ajk K i.1 i.2 := fun i hi =>
    lt_of_lt_of_le (by norm_num) (ajk_ge hK (Finset.mem_range.1 (Finset.mem_product.1 hi).1))
  have e : (fun p : ℝ × ℝ => (∑ i ∈ Idx K L, c i * (rb K i).indicator (fun _ => (1 : ℝ)) p) /
      p.2 ^ 2) = fun p => ∑ i ∈ Idx K L, c i * (rb K i).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p := by
    funext p
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : p ∈ rb K i
    · simp [Set.indicator_of_mem h, div_eq_mul_inv]
    · simp [Set.indicator_of_notMem h]
  rw [e]
  exact integrable_finsetSum _ fun i hi =>
    ((integrableOn_rbox (hpos i hi)).integrable_indicator (measurableSet_rb K i)).const_mul _

lemma cusp_div (L : ℕ) (M : ℝ) (p : ℝ × ℝ) :
    M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun _ => (1 : ℝ)) p / p.2 ^ 2 =
      M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p := by
  by_cases h : p ∈ rcusp (-(1 / 2)) (1 / 2) L
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring

/-! ### Bracketing `‖Δ‖²` -/

section Bracket
variable {K L : ℕ} {δ M : ℝ} (hK : 6 ≤ K) (hL : 1 ≤ L) (hδ : 0 < δ) (hM : ∀ z : ℍ, G z ≤ M)
  (huc : ∀ w w' : ℍ,
    w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
    w.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) → w'.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) →
    |w.re - w'.re| ≤ 1 / K → |w.im - w'.im| ≤ 1 / K → |G w - G w'| ≤ δ)

include hK hL hM huc in
lemma loW_le (p : ℝ × ℝ) : loW K L δ p ≤ Freg.indicator (fun p => G (gpt p.1 p.2)) p := by
  have hR : 0 ≤ Freg.indicator (fun p => G (gpt p.1 p.2)) p :=
    Set.indicator_nonneg (fun p _ => (G_nonneg _)) p
  by_cases hp : 1 / 4 ≤ p.2
  · obtain ⟨h0, hle⟩ := lo_spec (δ := δ) hK hL hM huc
    have hlo := ofReal_loW (K := K) (L := L) (δ := δ) hp
    by_cases hS : gpt p.1 p.2 ∈ Sset
    · have h1 := hle _ hS
      rw [← hlo, ENNReal.ofReal_le_ofReal_iff (G_nonneg _)] at h1
      have hF : p ∈ Freg := by
        obtain ⟨a1, a2, a3⟩ := hS
        rw [gpt_re] at a1 a2
        rw [normSq_gpt hp] at a3
        exact ⟨by linarith, abs_le.2 ⟨a1, a2.le⟩, a3.le⟩
      rw [Set.indicator_of_mem hF]
      exact h1
    · have h1 := h0 _ hS
      rw [← hlo, ENNReal.ofReal_eq_zero] at h1
      linarith
  · have : loW K L δ p = 0 := by
      unfold loW
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Set.indicator_of_notMem, mul_zero]
      intro hm
      have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi).1
      have := ajk_ge hK hjK (k := i.2)
      have := hm.2.1
      push_neg at hp
      linarith
    rw [this]; exact hR

include hK hL hδ hM huc in
lemma gR_le {p : ℝ × ℝ} (hp : p ∈ Freg) (hp1 : p.1 ≠ 1 / 2) :
    gR p ≤ upW K L δ M p / p.2 ^ 2 := by
  have hy := Freg_im hp
  have hy4 : 1 / 4 ≤ p.2 := by linarith
  have hM0 : 0 ≤ M := (G_nonneg (gpt 0 0)).trans (hM _)
  have hU : gpt p.1 p.2 ∈ Uset := by
    obtain ⟨-, h2, h3⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [gpt_re]; exact (abs_le.1 h2).1
    · rw [gpt_re]; exact lt_of_le_of_ne (abs_le.1 h2).2 hp1
    · rw [normSq_gpt hy4]; exact h3
  have h := up_ge hK hL hM huc hU
  rw [← ofReal_upW hδ hM0 hy4, ENNReal.ofReal_le_ofReal_iff (upW_nonneg hδ hM0 p)] at h
  unfold gR
  exact div_le_div_of_nonneg_right h (by positivity)

include hK hL hM huc in
theorem petNormSq_ge : ∑ i ∈ Idx K L, cLo K δ i * mu K i ≤ petNormSq := by
  rw [← integral_grid K L hK, petNormSq_eq, ← integral_indicator measurableSet_Freg]
  refine integral_mono (integrable_grid K L hK _)
    ((integrableOn_gR hM).integrable_indicator measurableSet_Freg) (fun p => ?_)
  have h := loW_le hK hL hM huc (δ := δ) p
  have e : Freg.indicator gR p = Freg.indicator (fun p => G (gpt p.1 p.2)) p / p.2 ^ 2 := by
    by_cases hp : p ∈ Freg
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_div]
  rw [e]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

lemma volume_line : volume {p : ℝ × ℝ | p.1 = 1 / 2} = 0 := by
  have : {p : ℝ × ℝ | p.1 = 1 / 2} = ({1 / 2} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

include hK hL hδ hM huc in
theorem petNormSq_le : petNormSq ≤ ∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L) := by
  have hM0 : 0 ≤ M := (G_nonneg (gpt 0 0)).trans (hM _)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hcusp : ∫ p, M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p
      = M * (1 / L) := by
    rw [integral_const_mul, integral_indicator (measurableSet_rcusp _ _ _),
      integral_rcusp (by norm_num) hLpos]
    ring
  have hicusp : Integrable fun p : ℝ × ℝ =>
      M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p :=
    ((integrableOn_rcusp hLpos).integrable_indicator (measurableSet_rcusp _ _ _)).const_mul _
  have hsplit : ∀ p : ℝ × ℝ, upW K L δ M p / p.2 ^ 2 =
      (∑ i ∈ Idx K L, cUp K δ i * (rb K i).indicator (fun _ => (1 : ℝ)) p) / p.2 ^ 2 +
      M * (rcusp (-(1 / 2)) (1 / 2) L).indicator (fun p : ℝ × ℝ => 1 / p.2 ^ 2) p := by
    intro p; unfold upW; rw [add_div, cusp_div]
  have hint : ∫ p, upW K L δ M p / p.2 ^ 2 = ∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L) := by
    simp_rw [hsplit]
    rw [integral_add (integrable_grid K L hK _) hicusp, integral_grid K L hK, hcusp]
  rw [← hint, petNormSq_eq, ← integral_indicator measurableSet_Freg]
  refine integral_mono_ae ((integrableOn_gR hM).integrable_indicator measurableSet_Freg)
    (by simp_rw [hsplit]; exact (integrable_grid K L hK _).add hicusp) ?_
  have hae : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 1 / 2 := by
    rw [ae_iff]; simpa using volume_line
  filter_upwards [hae] with p hp
  by_cases hF : p ∈ Freg
  · rw [Set.indicator_of_mem hF]; exact gR_le hK hL hδ hM huc hF hp
  · rw [Set.indicator_of_notMem hF]
    exact div_nonneg (upW_nonneg hδ hM0 p) (sq_nonneg _)

end Bracket

/-! ### Choice of parameters and the identification -/

lemma grid_params {M : ℝ} (hM0 : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) : ∃ K L : ℕ, ∃ δ : ℝ,
    6 ≤ K ∧ 1 ≤ L ∧ 0 < δ ∧ (∀ w w' : ℍ,
      w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
      w.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) → w'.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) →
      |w.re - w'.re| ≤ 1 / K → |w.im - w'.im| ≤ 1 / K → |G w - G w'| ≤ δ) ∧
    16 * (M + δ) / K + 8 * δ * L + M / L ≤ ε := by
  obtain ⟨L, hL⟩ := exists_nat_gt (3 * M / ε)
  have hLpos : (0 : ℝ) < L := lt_of_le_of_lt (by positivity) hL
  have hL1 : 1 ≤ L := by exact_mod_cast hLpos
  set δ : ℝ := min 1 (ε / (24 * L)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (24 * L) := min_le_right _ _
  obtain ⟨η, hη, huc0⟩ := exists_uc ((L : ℝ) + 2) δ hδ
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / η + 48 * (M + 1) / ε + 6)
  have hK6 : 6 ≤ K := by
    have : (6 : ℝ) < K := by
      have : 0 ≤ 1 / η + 48 * (M + 1) / ε := by positivity
      linarith
    exact_mod_cast this.le
  have hK' := K_pos hK6
  have hKη : 1 / (K : ℝ) ≤ η := by
    rw [div_le_iff₀ hK']
    have : 1 / η < K := by
      have : 0 ≤ 48 * (M + 1) / ε := by positivity
      linarith
    rw [div_lt_iff₀ hη] at this
    linarith
  have hKε : 48 * (M + 1) / ε < K := by
    have : 0 ≤ 1 / η := by positivity
    linarith
  refine ⟨K, L, δ, hK6, hL1, hδ,
    fun w w' h1 h2 h3 h4 h5 h6 => huc0 w w' h1 h2 h3 h4 (h5.trans hKη) (h6.trans hKη), ?_⟩
  have p1 : 16 * (M + δ) / K ≤ ε / 3 := by
    have h2 : 48 * (M + 1) ≤ ε * K := by rw [div_lt_iff₀ hε] at hKε; linarith
    calc 16 * (M + δ) / K ≤ 16 * (M + 1) / K := by gcongr
      _ = 48 * (M + 1) / (3 * K) := by field_simp; ring
      _ ≤ ε * K / (3 * K) := by gcongr
      _ = ε / 3 := by field_simp
  have p2 : 8 * δ * L ≤ ε / 3 := by
    calc 8 * δ * L ≤ 8 * (ε / (24 * L)) * L := by gcongr
      _ = ε / 3 := by field_simp; ring
  have p3 : M / L ≤ ε / 3 := by
    have : 3 * M < ε * L := by rw [div_lt_iff₀ hε] at hL; linarith
    calc M / L = 3 * M / (3 * L) := by field_simp
      _ ≤ ε * L / (3 * L) := by gcongr
      _ = ε / 3 := by field_simp
  linarith

/-- **Zagier's theorem for `G` (unconditional, axiom-clean):**
`∫₀¹ |Δ(x+iy)|² y¹² dx → (3/π)‖Δ‖²` as `y → 0⁺`. -/
theorem tendsto_Aint_zagier : Tendsto Aint (𝓝[>] 0) (𝓝 (3 / π * petNormSq)) := by
  obtain ⟨Λ, hΛ⟩ := exists_tendsto_Aint
  obtain ⟨M, hM0, hM⟩ := exists_G_le
  suffices h : Λ = 3 / π * petNormSq by rwa [← h]
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hπ := Real.pi_pos
  obtain ⟨K, L, δ, hK, hL1, hδ, huc, hgap⟩ := grid_params hM0 (ε := ε * π / 3) (by positivity)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  -- limits of the two sides
  have hTU : Tendsto (fun y => ∑ i ∈ Idx K L, cUp K δ i * bxR K i y +
      M * horoR (-(1 / 2)) (1 / 2) L y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Idx K L, cUp K δ i * (K0 * mu K i) +
        M * (4 * (1 / 2 - -(1 / 2)) / L * (kappa * Wc)))) :=
    (tendsto_finsetSum _ fun i hi => (tendsto_bxR hK hi).const_mul _).add
      ((tendsto_horoR (by norm_num) hLpos).const_mul _)
  have hTL : Tendsto (fun y => ∑ i ∈ Idx K L, cLo K δ i * bxR K i y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Idx K L, cLo K δ i * (K0 * mu K i))) :=
    tendsto_finsetSum _ fun i hi => (tendsto_bxR hK hi).const_mul _
  have hy2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < 1 / 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  have hup : 2 * Λ ≤ ∑ i ∈ Idx K L, cUp K δ i * (K0 * mu K i) +
      M * (4 * (1 / 2 - -(1 / 2)) / L * (kappa * Wc)) := by
    refine le_of_tendsto_of_tendsto (hΛ.const_mul 2) hTU ?_
    filter_upwards [hy2, self_mem_nhdsWithin] with y h2 h3
    exact upper_real hK hL1 hδ hM huc h3 h2
  have hlo : ∑ i ∈ Idx K L, cLo K δ i * (K0 * mu K i) ≤ 2 * Λ := by
    refine le_of_tendsto_of_tendsto hTL (hΛ.const_mul 2) ?_
    filter_upwards [hy2, self_mem_nhdsWithin] with y h2 h3
    exact lower_real hK hL1 hM huc h3 h2 (δ := δ)
  -- rewrite with `K₀ = 6/π`
  have eU : ∑ i ∈ Idx K L, cUp K δ i * (K0 * mu K i) +
      M * (4 * (1 / 2 - -(1 / 2)) / L * (kappa * Wc)) =
      K0 * (∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · unfold K0; field_simp; ring
  have eL : ∑ i ∈ Idx K L, cLo K δ i * (K0 * mu K i) =
      K0 * ∑ i ∈ Idx K L, cLo K δ i * mu K i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [eU, K0_eq] at hup
  rw [eL, K0_eq] at hlo
  have hP1 := petNormSq_ge hK hL1 hM huc (δ := δ)
  have hP2 := petNormSq_le hK hL1 hδ hM huc
  have hg := gap_le (L := L) hK hδ hM
  have hgap' : ∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L) - ∑ i ∈ Idx K L, cLo K δ i * mu K i
      ≤ ε * π / 3 := by
    have e : ∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L) -
        ∑ i ∈ Idx K L, cLo K δ i * mu K i =
        ∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L := by
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring
    rw [e]; linarith
  set U := ∑ i ∈ Idx K L, cUp K δ i * mu K i + M * (1 / L)
  set V := ∑ i ∈ Idx K L, cLo K δ i * mu K i
  have hΛU : Λ ≤ 3 / π * U := by
    have : 2 * Λ ≤ 6 / π * U := hup
    have e : 6 / π * U = 2 * (3 / π * U) := by ring
    linarith
  have hΛV : 3 / π * V ≤ Λ := by
    have : 6 / π * V ≤ 2 * Λ := hlo
    have e : 6 / π * V = 2 * (3 / π * V) := by ring
    linarith
  have h3π : 0 < 3 / π := by positivity
  have hPU : 3 / π * petNormSq ≤ 3 / π * U := mul_le_mul_of_nonneg_left hP2 h3π.le
  have hPV : 3 / π * V ≤ 3 / π * petNormSq := mul_le_mul_of_nonneg_left hP1 h3π.le
  have hUV : 3 / π * U - 3 / π * V ≤ ε := by
    have : 3 / π * (U - V) ≤ 3 / π * (ε * π / 3) := mul_le_mul_of_nonneg_left hgap' h3π.le
    have e : 3 / π * (ε * π / 3) = ε := by field_simp
    nlinarith
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end RamanujanTau.RankinSelbergGeneral.Horo
