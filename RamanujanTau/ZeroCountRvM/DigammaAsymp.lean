/-
# Stirling for `arg Γ`: `∫₀ᵀ Re ψ(6+iy) dy = T log T − T + O(log T)`

* `digamma_eq_log_add`: `ψ(s) = log s + Σ_{j≥0} (log(1 + 1/(s+j)) − 1/(s+j))` for `Re s > 0`
  (partial sums of the digamma series against the telescoping `Σ log(1+1/(s+j)) = log(s+N) − log s`).
* `abs_re_digamma_six_sub_log_le`: `|Re ψ(6+iy) − log|6+iy|| ≤ 40/(5+|y|)`.
* `integral_re_digamma_six`: for `T ≥ 1`,
  `|∫₀ᵀ Re ψ(6+iy) dy − (T log T − T)| ≤ 40 log(T+5) + 28`.
-/
import RamanujanTau.ZeroCountRvM.LogGamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Filter Topology Set Metric intervalIntegral MeasureTheory
open scoped Real Nat

lemma re_inv_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w⁻¹).re := by
  rw [inv_re]
  have : 0 < normSq w := normSq_pos.mpr (by intro h; rw [h] at hw; simp at hw)
  positivity

lemma log_add_one_eq {w : ℂ} (hw : 0 < w.re) : log (w + 1) = log w + log (1 + 1 / w) := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have h1 : 0 < (1 + 1 / w).re := by
    rw [add_re, one_re, one_div]; linarith [re_inv_pos hw]
  have h10 : (1 + 1 / w) ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have heq : w + 1 = w * (1 + 1 / w) := by field_simp
  rw [heq, log_mul hw0 h10]
  have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hb := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1))
  constructor <;> linarith

/-- The error terms `e_j(s) = log(1 + 1/(s+j)) − 1/(s+j)`. -/
noncomputable def et (s : ℂ) (j : ℕ) : ℂ := log (1 + 1 / (s + j)) - 1 / (s + j)

lemma re_add_nat_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) : 0 < (s + j).re := by
  simp; linarith [Nat.cast_nonneg (α := ℝ) j]

lemma norm_et_le {s : ℂ} (hs : 0 < s.re) (j : ℕ) : ‖et s j‖ ≤ 20 * ‖1 / (s + j)‖ ^ 2 := by
  have h := norm_sub_log_one_add_le (w := 1 / (s + j))
    (by rw [one_div]; exact (re_inv_pos (re_add_nat_pos hs j)).le)
  rw [et, norm_sub_rev]; exact h

lemma norm_inv_add_nat_le {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    ‖1 / (s + j)‖ ≤ 1 / (s.re + j) := by
  have hpos := re_add_nat_pos hs j
  rw [norm_div, norm_one]
  apply one_div_le_one_div_of_le (by simpa using hpos)
  have := Complex.re_le_norm (s + j)
  simpa using this

lemma summable_inv_sq_add {a : ℝ} (ha : 0 < a) : Summable (fun j : ℕ => 1 / (a + j) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_inv_jp_sq.mul_left ((1 + 1 / a) ^ 2))
  have hj := jp_pos j
  have hle : (j : ℝ) + 1 ≤ (1 + 1 / a) * (a + j) := by
    have : (1 + 1 / a) * (a + j) = a + j + 1 + j / a := by field_simp; ring
    rw [this]; have : 0 ≤ (j : ℝ) / a := by positivity
    linarith
  have hpos : 0 < a + j := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h2 : ((j : ℝ) + 1) ^ 2 ≤ ((1 + 1 / a) * (a + j)) ^ 2 := pow_le_pow_left₀ hj.le hle 2
  calc 1 = ((1 + 1 / a) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2)) * ((j : ℝ) + 1) ^ 2 / (1 + 1 / a) ^ 2 := by
        field_simp
    _ ≤ ((1 + 1 / a) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2)) * ((1 + 1 / a) * (a + j)) ^ 2 / (1 + 1 / a) ^ 2 := by
        gcongr
    _ = (1 + 1 / a) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) * (a + j) ^ 2 := by
        field_simp

lemma summable_et {s : ℂ} (hs : 0 < s.re) : Summable (et s) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => 20 * (1 / (s.re + j) ^ 2))
    ((summable_inv_sq_add hs).mul_left _) (fun j => ?_)
  refine (norm_et_le hs j).trans ?_
  have h := norm_inv_add_nat_le hs j
  have h0 : 0 ≤ ‖1 / (s + j)‖ := norm_nonneg _
  have : ‖1 / (s + j)‖ ^ 2 ≤ (1 / (s.re + j)) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [one_div_pow] at this
  show 20 * ‖1 / (s + j)‖ ^ 2 ≤ 20 * (1 / (s.re + j) ^ 2)
  linarith

lemma summable_psi_terms {s : ℂ} (hs : 0 < s.re) :
    Summable (fun j : ℕ => 1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1))) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => ‖s‖ * (1 / ((j : ℝ) + 1) ^ 2))
    (summable_inv_jp_sq.mul_left _) (fun j => ?_)
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (jp_pos j).ne'
  have hpos : 0 < (s + ((j : ℂ) + 1)).re := by
    simp; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hne : s + ((j : ℂ) + 1) ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have heq : 1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1)) = s / (((j : ℂ) + 1) * (s + ((j : ℂ) + 1))) := by
    field_simp; ring
  rw [heq, norm_div, norm_mul]
  have h1 : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
    have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jp_pos j)]
  have h2 : (j : ℝ) + 1 ≤ ‖s + ((j : ℂ) + 1)‖ := by
    have := Complex.re_le_norm (s + ((j : ℂ) + 1))
    simp at this; linarith
  rw [h1, div_le_iff₀ (by positivity)]
  have := jp_pos j
  calc ‖s‖ = ‖s‖ * (1 / ((j : ℝ) + 1) ^ 2) * (((j : ℝ) + 1) * ((j : ℝ) + 1)) := by
        field_simp
    _ ≤ ‖s‖ * (1 / ((j : ℝ) + 1) ^ 2) * (((j : ℝ) + 1) * ‖s + ((j : ℂ) + 1)‖) := by
        gcongr

lemma telescope_log {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    ∑ j ∈ Finset.range M, log (1 + 1 / (s + j)) = log (s + M) - log s := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have := log_add_one_eq (re_add_nat_pos hs M)
    push_cast
    rw [← add_assoc, this]; ring

lemma tendsto_log_sub_log {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => (Real.log N : ℂ) - log (s + ((N : ℂ) + 1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => 1 + (s + 1) * ((N : ℂ))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (s + 1)
    simpa using this.const_add 1
  have h2 : Tendsto (fun N : ℕ => log (1 + (s + 1) * ((N : ℂ))⁻¹)) atTop (𝓝 0) := by
    have hc : ContinuousAt log 1 := continuousAt_clog (by simp)
    simpa using hc.tendsto.comp h1
  refine (h2.neg.congr' ?_).trans (by simp)
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hx : (1 + (s + 1) * ((N : ℂ))⁻¹) ≠ 0 := by
    intro h
    have : s + ((N : ℂ) + 1) = 0 := by
      have : s + ((N : ℂ) + 1) = (N : ℂ) * (1 + (s + 1) * ((N : ℂ))⁻¹) := by field_simp; ring
      rw [this, h, mul_zero]
    have hre : 0 < (s + ((N : ℂ) + 1)).re := by
      simp; linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [this] at hre; simp at hre
  have : s + ((N : ℂ) + 1) = ((N : ℝ) : ℂ) * (1 + (s + 1) * ((N : ℂ))⁻¹) := by
    push_cast; field_simp; ring
  rw [this, log_ofReal_mul hNpos hx]
  ring

/-- **`ψ(s) = log s + Σ_j e_j(s)`** on `Re s > 0`. -/
theorem digamma_eq_log_add {s : ℂ} (hs : 0 < s.re) : digamma s = log s + ∑' j, et s j := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  set A : ℕ → ℂ := fun N => -(Real.eulerMascheroniConstant : ℂ) - 1 / s +
    ∑ j ∈ Finset.range N, (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1))) with hA
  set B : ℕ → ℂ := fun N => log s + ∑ j ∈ Finset.range (N + 1), et s j with hB
  have hAt : Tendsto A atTop (𝓝 (digamma s)) := by
    rw [digamma_eq_series hs]
    exact ((summable_psi_terms hs).hasSum.tendsto_sum_nat).const_add _
  have hBt : Tendsto B atTop (𝓝 (log s + ∑' j, et s j)) :=
    (((summable_et hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).const_add _
  have hid : ∀ N : ℕ, A N - B N = ((((harmonic N : ℝ) - Real.log N : ℝ) : ℂ) -
      (Real.eulerMascheroniConstant : ℂ)) + ((Real.log N : ℂ) - log (s + ((N : ℂ) + 1))) := by
    intro N
    have h1 : ∑ j ∈ Finset.range (N + 1), et s j =
        (log (s + ((N : ℂ) + 1)) - log s) - ∑ j ∈ Finset.range (N + 1), 1 / (s + j) := by
      unfold et
      rw [Finset.sum_sub_distrib, telescope_log hs]
      push_cast; ring
    have h2 : ∑ j ∈ Finset.range (N + 1), 1 / (s + (j : ℂ)) =
        ∑ j ∈ Finset.range N, 1 / (s + ((j : ℂ) + 1)) + 1 / s := by
      rw [Finset.sum_range_succ']; push_cast; simp
    have h3 : ∑ j ∈ Finset.range N, (1 / ((j : ℂ) + 1) - 1 / (s + ((j : ℂ) + 1))) =
        (harmonic N : ℂ) - ∑ j ∈ Finset.range N, 1 / (s + ((j : ℂ) + 1)) := by
      rw [Finset.sum_sub_distrib]
      unfold harmonic; push_cast
      congr 1
      apply Finset.sum_congr rfl; intro j _; rw [one_div]
    simp only [hA, hB]
    rw [h1, h2, h3]
    have : (((harmonic N : ℝ) : ℂ)) = (harmonic N : ℂ) := by push_cast; rfl
    push_cast
    ring
  have hlim : Tendsto (fun N => A N - B N) atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => (((harmonic N : ℝ) - Real.log N : ℝ) : ℂ) -
        (Real.eulerMascheroniConstant : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
      simpa using this.sub_const (Real.eulerMascheroniConstant : ℂ)
    simpa [hid] using hh.add (tendsto_log_sub_log hs)
  have := tendsto_nhds_unique (hAt.sub hBt) hlim
  exact (sub_eq_zero.mp this)

lemma sum_inv_sq_le {a : ℝ} (ha : 1 < a) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / (a + j) ^ 2 ≤ 1 / (a - 1) - 1 / (a - 1 + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < a - 1 + N := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    have key : 1 / (a + N) ^ 2 ≤ 1 / (a - 1 + N) - 1 / (a - 1 + ((N + 1 : ℕ) : ℝ)) := by
      push_cast
      have h2 : a - 1 + ((N : ℝ) + 1) = a + N := by ring
      rw [h2]
      have h3 : 0 < a + N := by linarith
      rw [div_sub_div _ _ h1.ne' h3.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma tsum_inv_sq_le {a : ℝ} (ha : 1 < a) :
    HasSum (fun j : ℕ => 1 / (a + j) ^ 2) (∑' j : ℕ, 1 / (a + j) ^ 2) ∧
      ∑' j : ℕ, 1 / (a + j) ^ 2 ≤ 1 / (a - 1) := by
  refine ⟨(summable_inv_sq_add (by linarith)).hasSum, ?_⟩
  apply Real.tsum_le_of_sum_range_le (fun j => by positivity)
  intro N
  refine (sum_inv_sq_le ha N).trans ?_
  have : 0 < a - 1 + N := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have : 0 < 1 / (a - 1 + N) := by positivity
  linarith

/-- `‖ψ(6+iy) − log(6+iy)‖ ≤ 40/(5+|y|)`. -/
theorem norm_digamma_six_sub_log_le (y : ℝ) :
    ‖digamma (6 + y * I) - log (6 + y * I)‖ ≤ 40 / (5 + |y|) := by
  set s : ℂ := 6 + y * I with hsdef
  have hs : 0 < s.re := by simp [hsdef]
  rw [digamma_eq_log_add hs, add_sub_cancel_left]
  set a : ℝ := 6 + |y| with ha
  have ha1 : 1 < a := by have := abs_nonneg y; linarith
  have hb : ∀ j : ℕ, ‖et s j‖ ≤ 40 * (1 / (a + j) ^ 2) := by
    intro j
    refine (norm_et_le hs j).trans ?_
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hn2 : ‖s + j‖ ^ 2 = (6 + j) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [hsdef]; ring
    have hpos : 0 < ‖s + j‖ := by
      rw [norm_pos_iff]; intro h
      have := congrArg Complex.re h; simp [hsdef] at this; linarith
    rw [norm_div, norm_one, div_pow, one_pow, hn2]
    have hyy : |y| ^ 2 = y ^ 2 := sq_abs y
    have hkey : (a + j) ^ 2 ≤ 2 * ((6 + j) ^ 2 + y ^ 2) := by
      rw [ha]; nlinarith [sq_nonneg ((6 : ℝ) + j - |y|), abs_nonneg y]
    have hp1 : 0 < (6 + (j : ℝ)) ^ 2 + y ^ 2 := by positivity
    have hp2 : 0 < (a + j) ^ 2 := by positivity
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ hp1 hp2]
    nlinarith
  obtain ⟨hsum, hle⟩ := tsum_inv_sq_le ha1
  have := tsum_of_norm_bounded (hsum.mul_left 40) hb
  calc ‖∑' j, et s j‖ ≤ 40 * ∑' j : ℕ, 1 / (a + j) ^ 2 := this
    _ ≤ 40 * (1 / (a - 1)) := by gcongr
    _ = 40 / (5 + |y|) := by rw [ha]; ring_nf

lemma abs_re_digamma_six_sub_log_le (y : ℝ) :
    |(digamma (6 + y * I)).re - Real.log ‖(6 : ℂ) + y * I‖| ≤ 40 / (5 + |y|) := by
  have h := norm_digamma_six_sub_log_le y
  rw [← log_re, ← sub_re]
  exact (abs_re_le_norm _).trans h

lemma continuousAt_digamma {s : ℂ} (hs : 0 < s.re) : ContinuousAt digamma s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    apply (differentiableAt_Gamma w _).differentiableWithinAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) < w.re := hw
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have han : AnalyticAt ℂ Gamma s := hd.analyticAt (hopen.mem_nhds hs)
  show ContinuousAt (fun w => deriv Gamma w / Gamma w) s
  exact han.deriv.continuousAt.div han.continuousAt (Gamma_ne_zero_of_re_pos hs)

lemma continuous_re_digamma_six : Continuous fun y : ℝ => (digamma (6 + y * I)).re := by
  apply Complex.continuous_re.comp
  rw [continuous_iff_continuousAt]
  intro y
  apply ContinuousAt.comp (g := digamma) (continuousAt_digamma (by simp)) (by fun_prop)

/-- The explicit antiderivative of `½ log(36 + y²)`. -/
noncomputable def Fsix (y : ℝ) : ℝ := y / 2 * Real.log (36 + y ^ 2) - y + 6 * Real.arctan (y / 6)

lemma hasDerivAt_Fsix (y : ℝ) : HasDerivAt Fsix (1 / 2 * Real.log (36 + y ^ 2)) y := by
  have hp : (0 : ℝ) < 36 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => 36 + y ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_pow 2 y).const_add 36)
  have h2 := h1.log hp.ne'
  have h3 := ((hasDerivAt_id y).div_const 2).mul h2
  have h4 : HasDerivAt (fun y : ℝ => Real.arctan (y / 6)) (1 / (1 + (y / 6) ^ 2) * (1 / 6)) y := by
    have := (Real.hasDerivAt_arctan (y / 6)).comp y ((hasDerivAt_id y).div_const 6)
    simpa using this
  have h5 := (h3.sub (hasDerivAt_id y)).add (h4.const_mul 6)
  unfold Fsix
  convert h5 using 1
  simp only [id]
  field_simp
  ring

lemma integral_half_log (T : ℝ) :
    ∫ y in (0 : ℝ)..T, 1 / 2 * Real.log (36 + y ^ 2) = Fsix T - Fsix 0 := by
  apply integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_Fsix y)
  apply Continuous.intervalIntegrable
  have : Continuous fun y : ℝ => Real.log (36 + y ^ 2) :=
    Continuous.log (by fun_prop) (fun y => by positivity)
  fun_prop

lemma log_norm_six (y : ℝ) : Real.log ‖(6 : ℂ) + y * I‖ = 1 / 2 * Real.log (36 + y ^ 2) := by
  have h : ‖(6 : ℂ) + y * I‖ ^ 2 = 36 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [← h, Real.log_pow]; push_cast; ring

/-- **Stirling for `arg Γ(6+iT)`**: `|∫₀ᵀ Re ψ(6+iy) dy − (T log T − T)| ≤ 40 log(T+5) + 30`. -/
theorem integral_re_digamma_six {T : ℝ} (hT : 1 ≤ T) :
    |(∫ y in (0 : ℝ)..T, (digamma (6 + y * I)).re) - (T * Real.log T - T)| ≤
      40 * Real.log (T + 5) + 30 := by
  have hT0 : 0 ≤ T := by linarith
  set f : ℝ → ℝ := fun y => (digamma (6 + y * I)).re
  set g : ℝ → ℝ := fun y => 1 / 2 * Real.log (36 + y ^ 2)
  have hfc : Continuous f := continuous_re_digamma_six
  have hgc : Continuous g := by
    have : Continuous fun y : ℝ => Real.log (36 + y ^ 2) :=
      Continuous.log (by fun_prop) (fun y => by positivity)
    exact continuous_const.mul this
  have hsplit : ∫ y in (0 : ℝ)..T, f y = (∫ y in (0 : ℝ)..T, (f y - g y)) + ∫ y in (0 : ℝ)..T, g y := by
    rw [← integral_add ((hfc.sub hgc).intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
    congr 1; funext y; ring
  -- the error integral
  have herr : |∫ y in (0 : ℝ)..T, (f y - g y)| ≤ 40 * Real.log (T + 5) := by
    have hbd : ∀ y ∈ Set.Ioc 0 T, ‖f y - g y‖ ≤ 40 / (5 + y) := by
      intro y hy
      have := abs_re_digamma_six_sub_log_le y
      rw [log_norm_six, abs_of_pos hy.1] at this
      rw [Real.norm_eq_abs]; exact this
    have hint : ∫ y in (0 : ℝ)..T, 40 / (5 + y) = 40 * (Real.log (5 + T) - Real.log 5) := by
      have : ∀ y ∈ Set.uIcc 0 T, HasDerivAt (fun y => 40 * Real.log (5 + y)) (40 / (5 + y)) y := by
        intro y hy
        have hy0 : 0 ≤ y := by
          rw [Set.uIcc_of_le hT0] at hy; exact hy.1
        have := (((hasDerivAt_id y).const_add 5).log (by simp; linarith)).const_mul 40
        convert this using 1; simp [div_eq_mul_inv]
      rw [integral_eq_sub_of_hasDerivAt this]
      · simp; ring
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro y hy; rw [Set.uIcc_of_le hT0] at hy; linarith [hy.1]
    have h1 := norm_integral_le_of_norm_le (μ := volume) hT0 (ae_of_all _ hbd) (by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro y hy; rw [Set.uIcc_of_le hT0] at hy; linarith [hy.1])
    rw [hint, Real.norm_eq_abs] at h1
    have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have : Real.log (5 + T) = Real.log (T + 5) := by ring_nf
    linarith
  -- the main integral
  have hmain : |(∫ y in (0 : ℝ)..T, g y) - (T * Real.log T - T)| ≤ 30 := by
    rw [integral_half_log, Fsix, Fsix]
    simp only [zero_div, zero_mul, sub_zero, Real.arctan_zero, mul_zero, add_zero]
    have hTpos : 0 < T := by linarith
    have hlog1 : Real.log (36 + T ^ 2) - 2 * Real.log T ≤ 36 / T ^ 2 := by
      have : Real.log (36 + T ^ 2) - 2 * Real.log T = Real.log ((36 + T ^ 2) / T ^ 2) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      rw [this]
      have := Real.log_le_sub_one_of_pos (x := (36 + T ^ 2) / T ^ 2) (by positivity)
      have h2 : (36 + T ^ 2) / T ^ 2 - 1 = 36 / T ^ 2 := by field_simp; ring
      linarith
    have hlog2 : 0 ≤ Real.log (36 + T ^ 2) - 2 * Real.log T := by
      have : 2 * Real.log T = Real.log (T ^ 2) := by rw [Real.log_pow]; push_cast; ring
      rw [this, sub_nonneg]
      exact Real.log_le_log (by positivity) (by linarith)
    have hT2 : T * (36 / T ^ 2) ≤ 36 := by
      rw [show T * (36 / T ^ 2) = 36 / T by field_simp]
      rw [div_le_iff₀ hTpos]; linarith
    have harc1 := Real.arctan_lt_pi_div_two (T / 6)
    have harc2 := Real.neg_pi_div_two_lt_arctan (T / 6)
    have hpi := Real.pi_le_four
    have hA : T / 2 * Real.log (36 + T ^ 2) - T * Real.log T =
        T / 2 * (Real.log (36 + T ^ 2) - 2 * Real.log T) := by ring
    rw [abs_le]
    constructor <;> nlinarith
  rw [hsplit]
  have := abs_add_le (∫ y in (0 : ℝ)..T, (f y - g y)) ((∫ y in (0 : ℝ)..T, g y) - (T * Real.log T - T))
  rw [show (∫ y in (0 : ℝ)..T, (f y - g y)) + (∫ y in (0 : ℝ)..T, g y) - (T * Real.log T - T) =
    (∫ y in (0 : ℝ)..T, (f y - g y)) + ((∫ y in (0 : ℝ)..T, g y) - (T * Real.log T - T)) by ring]
  linarith

end RamanujanTau.ZeroCountRvM
