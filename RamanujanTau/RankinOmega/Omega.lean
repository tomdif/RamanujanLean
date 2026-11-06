/-
# The Ω-theorem `R(x) = Ω(x^{3/8})` for Rankin–Selberg data

Landau–Mellin–Plancherel. Suppose `‖R(x)‖ ≤ c₀ x^{3/8}` for `x ≥ X₀`. For `σ = 3/8 + δ`:

* `∫ |h_σ|² ≤ c₀²/(2δ) + S² log X₀`                                  (`hfun_L1L2`);
* `∫ |h_σ|² = ∫ |𝓕 h_σ|² = ∫ |M(σ − 2πiξ)|² dξ`        (`plancherel_of_integrable`, `fourier_hfun`);
* `M` satisfies the functional-equation identity on the line (`Lam_eq_mellin`), so each dyadic block
  `[2^jΞ₀, 2^{j+1}Ξ₀]`, `j < ⌈1/(8δ)⌉`, contributes `≥ K₂` (`block_lower`, `dyadic_weight8`).

Hence `K₂/(8δ) ≤ c₀²/(2δ) + S² log X₀` for every small `δ`, impossible when `c₀² = K₂/16`.
-/
import RamanujanTau.RankinOmega.Block

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open scoped Real Interval FourierTransform

/-- `(2^{j+1} Ξ₀)^{−8δ} ≥ 1/(4Ξ₀)` for `j < ⌈1/(8δ)⌉`. -/
lemma dyadic_weight8 {Ξ0 δ : ℝ} (hΞ0 : 1 ≤ Ξ0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) {j : ℕ}
    (hj : j < ⌈1 / (8 * δ)⌉₊) :
    1 / (4 * Ξ0) ≤ (2 * (2 ^ j * Ξ0)) ^ (-(8 * δ)) := by
  set J := ⌈1 / (8 * δ)⌉₊ with hJ
  have hJlt : (J : ℝ) < 1 / (8 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj1 : ((j + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hj
  have h4 : (8 * δ) * ((j + 1 : ℕ) : ℝ) ≤ 2 := by
    have : (8 * δ) * (J : ℝ) < (8 * δ) * (1 / (8 * δ) + 1) := by gcongr
    have e : (8 * δ) * (1 / (8 * δ) + 1) = 1 + 8 * δ := by field_simp
    have : (8 * δ) * ((j + 1 : ℕ) : ℝ) ≤ (8 * δ) * J := by gcongr
    linarith
  have e1 : (2 * (2 ^ j * Ξ0)) = (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) * Ξ0 := by
    rw [Real.rpow_natCast, pow_succ]; ring
  rw [e1, Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num)]
  have h2 : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * -(8 * δ)) := by
    have : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * -(8 * δ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have e : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [e] at this; exact this
  have h3 : 1 / Ξ0 ≤ Ξ0 ^ (-(8 * δ)) := by
    have : Ξ0 ^ (-1 : ℝ) ≤ Ξ0 ^ (-(8 * δ)) :=
      Real.rpow_le_rpow_of_exponent_le hΞ0 (by linarith)
    rw [Real.rpow_neg_one] at this; rw [one_div]; exact this
  have : 1 / (4 * Ξ0) = (1 / 4) * (1 / Ξ0) := by field_simp
  rw [this]
  exact mul_le_mul h2 h3 (by positivity) (by positivity)

section Core

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include d habs in
/-- **The Ω-theorem for Rankin–Selberg data** (any real constant `c`):
`‖A(x) − c x‖ ≥ c' x^{3/8}` for arbitrarily large `x`. -/
theorem rs_omega_core (hm : 1 ≤ m) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) (c : ℝ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ c' * x ^ ((3 : ℝ) / 8) ≤ ‖Rf a c x‖ := by
  obtain ⟨K1, hK1, Ξ0, hΞ0, hblock⟩ := block_lower d habs hm hn0 hlow ha0 c
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = K1 / (4 * Ξ0) := ⟨_, rfl⟩
  have hK20 : 0 < K2 := by rw [hK2]; positivity
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = Real.sqrt K2 / 4 := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; positivity
  have hc'2 : c' ^ 2 = K2 / 16 := by
    rw [hc', div_pow, Real.sq_sqrt hK20.le]; norm_num
  refine ⟨c', hc'0, fun X => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, X0 = max X 1 := ⟨_, rfl⟩
  have hX01 : 1 ≤ X0 := by rw [hX0]; exact le_max_right _ _
  have hX : ∀ x ≥ X0, ‖Rf a c x‖ ≤ c' * x ^ ((3 : ℝ) / 8) := fun x hx =>
    (hcon x (le_trans (by rw [hX0]; exact le_max_left _ _) hx)).le
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Sb a c X0 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hX01
  have hSL : 0 ≤ S ^ 2 * L := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (1 / 16) (K2 / (16 * (S ^ 2 * L + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 16 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ K2 / (16 * (S ^ 2 * L + 1)) := by rw [hδ]; exact min_le_right _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 3 / 8 + δ := ⟨_, rfl⟩
  have hσθ : (3 : ℝ) / 8 < σ := by linarith
  -- upper bound
  obtain ⟨hi, hmem, hup⟩ := hfun_L1L2 a c (θ := 3 / 8) (by norm_num) hc'0.le hX01 hX hσθ
  rw [show σ - 3 / 8 = δ by rw [hσ]; ring, ← hS, ← hL] at hup
  -- Plancherel
  obtain ⟨hF2, hpl⟩ := TauOmegaPartial.plancherel_of_integrable hi hmem
  set F : ℝ → ℂ := fun ξ => mellin (Rf a c) (-((σ : ℂ) - 2 * π * ξ * I)) with hF
  have hFeq : 𝓕 (hfun a c σ) = F := by
    funext ξ; exact fourier_hfun a c σ ξ
  rw [hFeq] at hF2 hpl
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun ξ => ?_
    have hre : (3 : ℝ) / 8 < ((σ : ℂ) - 2 * π * ξ * I).re := by simpa using hσθ
    exact (differentiableAt_mellin_Rf c hX hre).continuousAt.comp
      (f := fun ξ : ℝ => (σ : ℂ) - 2 * π * ξ * I) (x := ξ) (by fun_prop)
  have hFi : Integrable (fun ξ => ‖F ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).1 hF2
  -- the functional-equation identity on the line
  have hMid : ∀ ξ : ℝ, 1 ≤ ξ →
      Lam d (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) *
          invGamM m (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) =
        riemannZeta (2 * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) *
          ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) *
              (fun s => mellin (Rf a c) (-s)) (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) +
            c * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) /
              ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) - 1)) := by
    intro ξ hξ
    rw [← hσ]
    have hre : (3 : ℝ) / 8 < ((σ : ℂ) - 2 * π * ξ * I).re := by simpa using hσθ
    have him : ((σ : ℂ) - 2 * π * ξ * I).im < 0 := by
      have : 0 < 2 * π * ξ := by have := Real.pi_pos; positivity
      simpa using this
    exact Lam_eq_mellin c habs d (by norm_num) hX hre him
  have hMc : Continuous (fun ξ : ℝ =>
      (fun s => mellin (Rf a c) (-s)) (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) := by
    rw [← hσ]; exact hFc
  have hb := hblock δ hδ0 hδ1 (fun s => mellin (Rf a c) (-s)) hMid hMc
  simp only [← hσ] at hb
  -- dyadic blocks
  set J : ℕ := ⌈1 / (8 * δ)⌉₊ with hJ
  set b : ℕ → ℝ := fun j => 2 ^ j * Ξ0 with hbdef
  have hsum : ∑ j ∈ Finset.range J, ∫ ξ in b j..b (j + 1), ‖F ξ‖ ^ 2 =
      ∫ ξ in b 0..b J, ‖F ξ‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
      (hFc.norm.pow 2).intervalIntegrable _ _
  have hle : ∫ ξ in b 0..b J, ‖F ξ‖ ^ 2 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := by
    have h0J : b 0 ≤ b J := by
      simp only [hbdef, pow_zero, one_mul]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    rw [intervalIntegral.integral_of_le h0J]
    exact setIntegral_le_integral hFi (Eventually.of_forall fun _ => by positivity)
  have hblocks : ∀ j ∈ Finset.range J, K2 ≤ ∫ ξ in b j..b (j + 1), ‖F ξ‖ ^ 2 := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    have hbj : Ξ0 ≤ b j := by
      simp only [hbdef]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    have hbb := hb (b j) hbj
    have hnext : b (j + 1) = 2 * b j := by simp only [hbdef]; rw [pow_succ]; ring
    rw [hnext]
    have hw := dyadic_weight8 hΞ0 hδ0 hδ1 hjJ
    have : K2 ≤ K1 * (2 * b j) ^ (-(8 * δ)) := by
      rw [hK2, div_eq_mul_one_div]
      simp only [hbdef]
      exact mul_le_mul_of_nonneg_left hw hK1.le
    exact this.trans hbb
  have hlow' : (J : ℝ) * K2 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := by
    have := Finset.sum_le_sum hblocks
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at this
    exact this.trans hle
  have hJge : 1 / (8 * δ) ≤ (J : ℝ) := Nat.le_ceil _
  -- combine
  rw [hpl] at hlow'
  have hmain : K2 / (8 * δ) ≤ c' ^ 2 / (2 * δ) + S ^ 2 * L := by
    have : K2 / (8 * δ) ≤ (J : ℝ) * K2 := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hJge hK20.le
    linarith
  rw [hc'2] at hmain
  have hmul : K2 / 8 ≤ K2 / 32 + δ * (S ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hmain hδ0.le
    have e1 : δ * (K2 / (8 * δ)) = K2 / 8 := by field_simp
    have e2 : δ * (K2 / 16 / (2 * δ) + S ^ 2 * L) = K2 / 32 + δ * (S ^ 2 * L) := by
      field_simp; ring
    linarith
  have hsmall : δ * (S ^ 2 * L) ≤ K2 / 16 := by
    have h8 : 0 < 16 * (S ^ 2 * L + 1) := by positivity
    calc δ * (S ^ 2 * L) ≤ K2 / (16 * (S ^ 2 * L + 1)) * (S ^ 2 * L) := by gcongr
      _ ≤ K2 / (16 * (S ^ 2 * L + 1)) * (S ^ 2 * L + 1) := by gcongr; linarith
      _ = K2 / 16 := by field_simp
  linarith

end Core

end RamanujanTau.RankinOmega
