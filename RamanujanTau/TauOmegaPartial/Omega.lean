/-
# The Ω-theorem `∑_{n≤x} a_f(n) = Ω(x^{(k−1)/2 + 1/4})`

Landau–Mellin–Plancherel argument. Suppose `‖A(x)‖ ≤ c₀ x^α` for `x ≥ X₀`, `α = (2k−1)/4`. For
`σ = α + δ`:

* `∫ |h_σ|² ≤ c₀²/(2δ) + S² log X₀`          (`hfun_L1L2`);
* `∫ |h_σ|² = ∫ |𝓕 h_σ|² = ∫ |L(σ−2πiξ)/(σ−2πiξ)|² dξ`   (`plancherel_of_integrable`, `fourier_hfun`);
* the right side is `≥ ∑_{j < ⌈1/(4δ)⌉} K₁ (2^{j+1}Ξ₀)^{−4δ} ≥ K₂/(4δ)`   (`block_lower`).

Hence `K₂/4 ≤ c₀²/2 + δ S² log X₀` for all small `δ`, impossible when `c₀² < K₂/2`.
-/
import RamanujanTau.TauOmegaPartial.Block
import RamanujanTau.RankinSelbergGeneral.Positive

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real Interval FourierTransform

variable {k : ℕ}

/-- The least index with a nonzero coefficient. -/
lemma exists_first_coef (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ n < m, coef f n = 0) ∧ coef f m ≠ 0 := by
  classical
  have hex : ∃ n, coef f n ≠ 0 := by
    obtain ⟨n, _, hn⟩ := RankinSelbergGeneral.exists_coeff_ne_zero f hf hk
    refine ⟨n, fun h => hn ?_⟩
    rw [coeffSq_eq, h, norm_zero]; norm_num
  refine ⟨Nat.find hex, ?_, fun n hn => ?_, Nat.find_spec hex⟩
  · by_contra h
    push Not at h
    have h0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [h0, coef_zero] at this
    exact this rfl
  · have := Nat.find_min hex hn
    push Not at this
    exact this

/-- Lower bound for each dyadic block: `(2^{j+1} Ξ₀)^{−4δ} ≥ 1/(4Ξ₀)` when `j < J = ⌈1/(4δ)⌉`. -/
lemma dyadic_weight {Ξ0 δ : ℝ} (hΞ0 : 1 ≤ Ξ0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) {j : ℕ}
    (hj : j < ⌈1 / (4 * δ)⌉₊) :
    1 / (4 * Ξ0) ≤ (2 * (2 ^ j * Ξ0)) ^ (-(4 * δ)) := by
  set J := ⌈1 / (4 * δ)⌉₊ with hJ
  have hJlt : (J : ℝ) < 1 / (4 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj1 : ((j + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hj
  have h4 : (4 * δ) * ((j + 1 : ℕ) : ℝ) ≤ 2 := by
    have : (4 * δ) * (J : ℝ) < (4 * δ) * (1 / (4 * δ) + 1) := by gcongr
    have e : (4 * δ) * (1 / (4 * δ) + 1) = 1 + 4 * δ := by field_simp
    have : (4 * δ) * ((j + 1 : ℕ) : ℝ) ≤ (4 * δ) * J := by gcongr
    linarith
  have e1 : (2 * (2 ^ j * Ξ0)) = (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) * Ξ0 := by
    rw [Real.rpow_natCast, pow_succ]; ring
  rw [e1, Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num)]
  have h2 : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * -(4 * δ)) := by
    have : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * -(4 * δ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have e : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [e] at this; exact this
  have h3 : 1 / Ξ0 ≤ Ξ0 ^ (-(4 * δ)) := by
    have : Ξ0 ^ (-1 : ℝ) ≤ Ξ0 ^ (-(4 * δ)) :=
      Real.rpow_le_rpow_of_exponent_le hΞ0 (by linarith)
    rw [Real.rpow_neg_one] at this; rw [one_div]; exact this
  have : 1 / (4 * Ξ0) = (1 / 4) * (1 / Ξ0) := by field_simp
  rw [this]
  exact mul_le_mul h2 h3 (by positivity) (by positivity)

/-- **Ω-theorem for partial sums of a level-one cusp form**: for `f ≠ 0` of weight `k`,
`|∑_{n≤x} a_f(n)| ≥ c x^{(k−1)/2+1/4}` for arbitrarily large `x`. -/
theorem cuspForm_partial_sum_omega (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) ≤ ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (eq_zero_of_lt_twelve f (by omega))
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨m, hm, hlow, hm0⟩ := exists_first_coef f hf (by omega)
  obtain ⟨K1, hK1, Ξ0, hΞ0, hblock⟩ := block_lower f hk hm hlow hm0
  set K2 : ℝ := K1 / (4 * Ξ0) with hK2
  have hK20 : 0 < K2 := by positivity
  set α : ℝ := ((k : ℝ) - 1) / 2 + 1 / 4 with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  set c : ℝ := Real.sqrt K2 / 4 with hc
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = K2 / 16 := by
    rw [hc, div_pow, Real.sq_sqrt hK20.le]; norm_num
  refine ⟨c, hc0, fun X => ?_⟩
  by_contra hcon
  push Not at hcon
  set X0 : ℝ := max X 1 with hX0
  have hX01 : 1 ≤ X0 := le_max_right _ _
  have hX : ∀ x ≥ X0, ‖A f x‖ ≤ c * x ^ α := fun x hx =>
    (hcon x (le_trans (le_max_left _ _) hx)).le
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ n ∈ Finset.Icc 1 ⌊X0⌋₊, ‖coef f n‖ := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hX01
  have hSL : 0 ≤ S ^ 2 * L := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (1 / 16) (K2 / (8 * (S ^ 2 * L + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 16 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ K2 / (8 * (S ^ 2 * L + 1)) := by rw [hδ]; exact min_le_right _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = α + δ := ⟨_, rfl⟩
  have hσα : α < σ := by linarith
  -- upper bound
  obtain ⟨hi, hmem, hup⟩ := hfun_L1L2 f hα0 hc0.le hX01 hX hσα
  rw [show σ - α = δ by rw [hσ]; ring, ← hS, ← hL] at hup
  -- Plancherel
  obtain ⟨hF2, hpl⟩ := plancherel_of_integrable hi hmem
  have hFeq : 𝓕 (hfun f σ) = Fs f σ := by
    funext ξ; exact fourier_hfun f (by omega) hα0 hX hσα ξ
  rw [hFeq] at hF2 hpl
  have hσ0 : 0 < σ := by linarith
  have hFc := continuous_Fs f (by omega) hσ0
  have hFi : Integrable (fun ξ => ‖Fs f σ ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).1 hF2
  -- dyadic blocks
  set J : ℕ := ⌈1 / (4 * δ)⌉₊ with hJ
  set a : ℕ → ℝ := fun j => 2 ^ j * Ξ0 with ha
  have hsum : ∑ j ∈ Finset.range J, ∫ ξ in a j..a (j + 1), ‖Fs f σ ξ‖ ^ 2 =
      ∫ ξ in a 0..a J, ‖Fs f σ ξ‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
      (hFc.norm.pow 2).intervalIntegrable _ _
  have hle : ∫ ξ in a 0..a J, ‖Fs f σ ξ‖ ^ 2 ≤ ∫ ξ, ‖Fs f σ ξ‖ ^ 2 := by
    have h0J : a 0 ≤ a J := by
      simp only [ha, pow_zero, one_mul]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    rw [intervalIntegral.integral_of_le h0J]
    exact setIntegral_le_integral hFi (Eventually.of_forall fun _ => by positivity)
  have hblocks : ∀ j ∈ Finset.range J, K2 ≤ ∫ ξ in a j..a (j + 1), ‖Fs f σ ξ‖ ^ 2 := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    have haj : Ξ0 ≤ a j := by
      simp only [ha]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    have hb := hblock δ hδ0 hδ1 (a j) haj
    rw [← hσ] at hb
    have hnext : a (j + 1) = 2 * a j := by simp only [ha]; rw [pow_succ]; ring
    rw [hnext]
    have hw := dyadic_weight hΞ0 hδ0 hδ1 hjJ
    have : K2 ≤ K1 * (2 * a j) ^ (-(4 * δ)) := by
      rw [hK2, div_eq_mul_one_div]
      simp only [ha]
      exact mul_le_mul_of_nonneg_left hw hK1.le
    exact this.trans hb
  have hlow' : (J : ℝ) * K2 ≤ ∫ ξ, ‖Fs f σ ξ‖ ^ 2 := by
    have := Finset.sum_le_sum hblocks
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at this
    exact this.trans hle
  have hJge : 1 / (4 * δ) ≤ (J : ℝ) := Nat.le_ceil _
  -- combine
  rw [hpl] at hlow'
  have hmain : K2 / (4 * δ) ≤ c ^ 2 / (2 * δ) + S ^ 2 * L := by
    have : K2 / (4 * δ) ≤ (J : ℝ) * K2 := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hJge hK20.le
    linarith
  rw [hc2] at hmain
  have hmul : K2 / 4 ≤ K2 / 32 + δ * (S ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hmain hδ0.le
    have e1 : δ * (K2 / (4 * δ)) = K2 / 4 := by field_simp
    have e2 : δ * (K2 / 16 / (2 * δ) + S ^ 2 * L) = K2 / 32 + δ * (S ^ 2 * L) := by
      field_simp; ring
    linarith
  have hsmall : δ * (S ^ 2 * L) ≤ K2 / 8 := by
    have h8 : 0 < 8 * (S ^ 2 * L + 1) := by positivity
    calc δ * (S ^ 2 * L) ≤ K2 / (8 * (S ^ 2 * L + 1)) * (S ^ 2 * L) := by gcongr
      _ ≤ K2 / (8 * (S ^ 2 * L + 1)) * (S ^ 2 * L + 1) := by gcongr; linarith
      _ = K2 / 8 := by field_simp
  linarith

end RamanujanTau.TauOmegaPartial
