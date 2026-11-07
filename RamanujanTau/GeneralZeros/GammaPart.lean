/-
# The Gamma factor at weight `k`: `∫₀ᵀ Re ψ(k/2+iy) dy = T log T − T + O(log T)`

* `integral_re_digamma_nat`: for every natural `m ≥ 6`,
  `|∫₀ᵀ Re ψ(m+iy) dy − (T log T − T)| ≤ 40 log(T+5) + 30 + 2(m−6)`; from the case `m = 6`
  (`ZeroCountRvM.integral_re_digamma_six`) and `ψ(s+1) = ψ(s) + 1/s`,
  `∫₀ᵀ Re 1/(m+iy) dy = arctan(T/m) ∈ [0, π/2]`.  (`k` is even, so `k/2` is a natural number.)
* `gamma_cauchy_gen`: Cauchy for `ψ` on `[a, σ₁] × [y₀, y₁]`.
* `integral_re_digamma_symm`: `∫_{−T}^{T} Re ψ(a+iy) dy = 2 ∫₀ᵀ Re ψ(a+iy) dy`.
-/
import RamanujanTau.ZeroCountRvM.Decomp

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory
open RamanujanTau.ZeroCountRvM
open scoped ComplexConjugate Real Interval

lemma continuous_re_digamma_vert {a : ℝ} (ha : 0 < a) :
    Continuous fun y : ℝ => (digamma (a + y * I)).re :=
  Complex.continuous_re.comp (continuous_digamma_vert ha)

lemma hasDerivAt_arctan_div {m : ℝ} (hm : 0 < m) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan (y / m)) (m / (m ^ 2 + y ^ 2)) y := by
  have := (Real.hasDerivAt_arctan (y / m)).comp y ((hasDerivAt_id y).div_const m)
  convert this using 1
  field_simp

lemma re_inv_vert {m y : ℝ} : (((m : ℂ) + y * I)⁻¹).re = m / (m ^ 2 + y ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]; simp; ring_nf

lemma integral_re_inv_vert {m : ℝ} (hm : 0 < m) (T : ℝ) :
    ∫ y in (0 : ℝ)..T, (((m : ℂ) + y * I)⁻¹).re = Real.arctan (T / m) := by
  simp only [re_inv_vert]
  rw [integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_arctan_div hm y)]
  · simp
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun y => by positivity)

/-- **Stirling for `arg Γ(m+iT)`**, every natural `m ≥ 6`. -/
theorem integral_re_digamma_nat {m : ℕ} (hm : 6 ≤ m) {T : ℝ} (hT : 1 ≤ T) :
    |(∫ y in (0 : ℝ)..T, (digamma ((m : ℂ) + y * I)).re) - (T * Real.log T - T)| ≤
      40 * Real.log (T + 5) + 30 + 2 * ((m : ℝ) - 6) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have := integral_re_digamma_six hT
    push_cast
    simpa using this
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hrec : ∀ y : ℝ, (digamma (((n + 1 : ℕ) : ℂ) + y * I)).re =
        (digamma ((n : ℂ) + y * I)).re + (((n : ℝ) : ℂ) + y * I)⁻¹.re := by
      intro y
      have hs : ∀ j : ℕ, (n : ℂ) + y * I ≠ -j :=
        ne_neg_nat_of_re_pos (by simp; omega)
      have e : ((n + 1 : ℕ) : ℂ) + y * I = ((n : ℂ) + y * I) + 1 := by push_cast; ring
      rw [e, Complex.digamma_apply_add_one _ hs, add_re]
      norm_cast
    have hc1 : Continuous fun y : ℝ => (digamma ((n : ℂ) + y * I)).re := by
      simpa using continuous_re_digamma_vert (a := (n : ℝ)) hn0
    have hc2 : Continuous fun y : ℝ => (((n : ℝ) : ℂ) + y * I)⁻¹.re := by
      have : (fun y : ℝ => (((n : ℝ) : ℂ) + y * I)⁻¹.re) =
          fun y : ℝ => (n : ℝ) / ((n : ℝ) ^ 2 + y ^ 2) := by
        funext y; exact re_inv_vert
      rw [this]
      exact continuous_const.div (by fun_prop) (fun y => by positivity)
    have hsplit : ∫ y in (0 : ℝ)..T, (digamma (((n + 1 : ℕ) : ℂ) + y * I)).re =
        (∫ y in (0 : ℝ)..T, (digamma ((n : ℂ) + y * I)).re) + Real.arctan (T / n) := by
      rw [← integral_re_inv_vert hn0 T]
      rw [← integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
      apply integral_congr; intro y _
      simp only []
      rw [hrec y]
    rw [hsplit]
    have ha1 := Real.arctan_lt_pi_div_two (T / n)
    have ha2 : 0 ≤ Real.arctan (T / n) := by
      rw [← Real.arctan_zero]
      exact Real.arctan_strictMono.monotone (by positivity)
    have hpi := Real.pi_le_four
    push_cast
    rw [abs_le] at ih ⊢
    constructor <;> nlinarith [ih.1, ih.2]

/-- **Cauchy for `ψ`** on `[a, σ₁] × [y₀, y₁]`, `0 < a ≤ σ₁`. -/
theorem gamma_cauchy_gen {a σ₁ y₀ y₁ : ℝ} (ha : 0 < a) (haσ : a ≤ σ₁) :
    (∫ y in y₀..y₁, digamma (σ₁ + y * I)).re - (∫ x in a..σ₁, digamma (x + y₁ * I)).im +
      (∫ x in a..σ₁, digamma (x + y₀ * I)).im =
      (∫ y in y₀..y₁, digamma (a + y * I)).re := by
  have hC : rectInt digamma a σ₁ y₀ y₁ = 0 := by
    apply rectInt_eq_zero
    intro z hz
    rw [mem_reProdIm, uIcc_of_le haσ] at hz
    exact (differentiableAt_digamma (by linarith [hz.1.1])).differentiableWithinAt
  unfold rectInt at hC
  have hIm := congrArg Complex.im hC
  simp only [sub_im, add_im, smul_eq_mul, mul_im, I_re, I_im, zero_mul, one_mul,
    zero_im, zero_add] at hIm
  linarith

/-- `∫_{−T}^{T} Re ψ(a+iy) dy = 2 ∫₀ᵀ Re ψ(a+iy) dy`. -/
theorem integral_re_digamma_symm {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (∫ y in (-T)..T, digamma (a + y * I)).re = 2 * ∫ y in (0 : ℝ)..T, (digamma (a + y * I)).re := by
  have hc := continuous_re_digamma_vert ha
  have hre : (∫ y in (-T)..T, digamma (a + y * I)).re = ∫ y in (-T)..T, (digamma (a + y * I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm
      ((continuous_digamma_vert (σ := a) ha).intervalIntegrable (μ := volume) (-T) T)
    simp only [Complex.reCLM_apply] at this
    exact this.symm
  rw [hre, ← integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ y in (-T)..0, (digamma (a + y * I)).re = ∫ y in (0 : ℝ)..T, (digamma (a + y * I)).re := by
    have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := T)
      (fun y : ℝ => (digamma (a + y * I)).re)
    simp only [neg_zero] at h1
    rw [← h1]
    apply integral_congr; intro y _
    simp only []
    have e : (a : ℂ) + ((-y : ℝ) : ℂ) * I = conj ((a : ℂ) + y * I) := by
      simp [map_add, conj_ofReal]
    rw [e, digamma_conj (by simp; exact ha), Complex.conj_re]
  rw [hneg]; ring

end RamanujanTau.GeneralZeros
