/-
# `SKQFHyp θ ⇐ SvStripHyp c'` (level 1 reduction)

`skqfHyp_of_strip`: for `0 < θ`, `8(c'+1)θ ≤ 1`, the strip hypothesis implies Selberg's
arithmetic lemma `SKQFHyp θ`, with `B = 1` and
`D = 1 + 24|r₀|C/θ + |r₀|(1 + 2048C/θ + 32C/θ)` (`C` the constant of `SvStripHyp`).
`skqfHyp_small_of_strip`: hence `∃ θ₁ > 0, ∀ θ ∈ (0, θ₁], SKQFHyp θ`.
-/
import RamanujanTau.SKQFProof.Bound
import RamanujanTau.SKQFProof.Final

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

open Complex Set
open RamanujanTau.SelbergKey

/-- Floor bookkeeping for `y = ⌊T^θ⌋₊`. -/
lemma floor_facts {θ T : ℝ} (hθ : 0 < θ) (hT : 0 < T) (h2 : 2 ≤ θ * Real.log T) :
    2 ≤ ⌊T ^ θ⌋₊ ∧ θ * Real.log T / 2 ≤ Real.log (⌊T ^ θ⌋₊ : ℝ) ∧
      Real.log (⌊T ^ θ⌋₊ : ℝ) ≤ θ * Real.log T := by
  have hTθ : T ^ θ = Real.exp (θ * Real.log T) := by
    rw [Real.rpow_def_of_pos hT]; ring_nf
  have hE : 3 ≤ T ^ θ := by
    rw [hTθ]; have := Real.add_one_le_exp (θ * Real.log T); linarith
  have hlt := Nat.lt_floor_add_one (T ^ θ)
  have hle := Nat.floor_le (by linarith : (0:ℝ) ≤ T ^ θ)
  have hy2 : (2 : ℝ) < ⌊T ^ θ⌋₊ := by linarith
  have hy2' : 2 ≤ ⌊T ^ θ⌋₊ := by exact_mod_cast hy2.le
  have hypos : (0 : ℝ) < ⌊T ^ θ⌋₊ := by linarith
  refine ⟨hy2', ?_, ?_⟩
  · have hhalf : T ^ θ / 2 ≤ (⌊T ^ θ⌋₊ : ℝ) := by linarith
    have := Real.log_le_log (by positivity) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hT] at this
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  · have := Real.log_le_log hypos hle
    rwa [Real.log_rpow hT] at this

set_option maxHeartbeats 2000000 in
theorem skqfHyp_of_strip {θ c' : ℝ} (hθ : 0 < θ) (hc' : 0 ≤ c') (hθc : 8 * (c' + 1) * θ ≤ 1)
    (H : SvStripHyp c') : SKQFHyp θ := by
  obtain ⟨C, δ₀, hC, hδ₀, hH⟩ := H
  set G := |GoodSecondTerm.gammaD|
  set R := |HafnerBridge.r0|
  have hG : 0 ≤ G := abs_nonneg _
  have hR : 0 ≤ R := abs_nonneg _
  refine ⟨1, 1 + 24 * R * C / θ + R * (1 + 2048 * C / θ + 32 * C / θ), by positivity, fun K hK => ?_⟩
  set Λ₀ := K + 2 * Real.log (4 * Real.pi) + 2 / θ + 4 * G * C * (1 + K) ^ 3 / θ +
    128 * (1 + δ₀) * (C + 1) * (1 + K) ^ 3 / δ₀ ^ 3 + 2 * C * (1 + K) ^ 2 / θ with hΛ₀
  have hlog4pi : 0 ≤ Real.log (4 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hK0 : 0 ≤ K := by linarith
  have t1 : 0 ≤ 2 / θ := by positivity
  have t2 : 0 ≤ 4 * G * C * (1 + K) ^ 3 / θ := by positivity
  have t3 : 0 ≤ 128 * (1 + δ₀) * (C + 1) * (1 + K) ^ 3 / δ₀ ^ 3 := by positivity
  have t4 : 0 ≤ 2 * C * (1 + K) ^ 2 / θ := by positivity
  refine ⟨Real.exp Λ₀, fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hΛ : Λ₀ ≤ Real.log T := by rw [Real.le_log_iff_exp_le hT0]; exact hT
  rw [hΛ₀] at hΛ
  set Λ := Real.log T with hΛdef
  have hKΛ : K ≤ Λ := by linarith
  have hΛpos : 0 < Λ := by linarith
  have hθΛ2 : 2 ≤ θ * Λ := by
    have : 2 / θ ≤ Λ := by linarith
    rwa [div_le_iff₀ hθ, mul_comm] at this
  obtain ⟨hy2, hℓlo, hℓhi⟩ := floor_facts hθ hT0 hθΛ2
  set y := ⌊T ^ θ⌋₊ with hydef
  set ℓ := Real.log (y : ℝ) with hℓdef
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨F, U, hU, hRU, hFd, hFS, hFb⟩ := hH y hy2
  set h := K / Λ with hhdef
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hΛpos]; exact hKΛ
  have hθ8 : θ ≤ 1 / 8 := by nlinarith
  have hℓΛ : ℓ ≤ Λ := by nlinarith
  have hhℓ : h * ℓ ≤ K := by
    rw [hhdef, div_mul_eq_mul_div, div_le_iff₀ hΛpos]
    exact mul_le_mul_of_nonneg_left hℓΛ hK0
  refine ⟨fun v hv => ?_, fun L hL => ?_⟩
  · -- clause (i)
    have hv1 : |v| ≤ h := abs_le.2 ⟨hv.1, hv.2⟩
    have hz : (v : ℂ) ∈ stripR δ₀ := ⟨by simp; linarith, by simp; linarith, by simp⟩
    rw [← hFS v (hv1.trans hh1)]
    refine (hFb _ hz).trans ?_
    simp only [ofReal_re, ofReal_im, abs_zero, mul_zero, zero_mul, Real.exp_zero, mul_one]
    rw [div_le_one hℓ0]
    have h1 : |v| * ℓ ≤ K := (mul_le_mul_of_nonneg_right hv1 hℓ0.le).trans hhℓ
    have h2 : C * (1 + |v| * ℓ) ^ 2 ≤ C * (1 + K) ^ 2 := by
      have : 0 ≤ |v| * ℓ := by positivity
      gcongr
    have h3 : C * (1 + K) ^ 2 ≤ ℓ := by
      have : 2 * C * (1 + K) ^ 2 / θ ≤ Λ := by linarith
      rw [div_le_iff₀ hθ] at this; nlinarith
    linarith
  · -- clause (ii)
    have hLlo : Λ / 2 ≤ L := by
      have := hL.1
      rw [Real.log_div hT0.ne' (by positivity)] at this
      linarith
    have hLhi : L ≤ Λ := hL.2
    have hc'θ : c' * θ ≤ 1 / 8 := by nlinarith
    have hb : 0 < L - c' * ℓ := by nlinarith
    have hIB := int_bound hc' hC hδ₀ hy2 F U hU hRU hFd hFS hFb hh0 hh1 (by linarith) hb
    refine hIB.trans ?_
    have hℓG : 2 * G * C * (1 + K) ^ 3 ≤ ℓ := by
      have : 4 * G * C * (1 + K) ^ 3 / θ ≤ Λ := by linarith
      rw [div_le_iff₀ hθ] at this; nlinarith
    have hΛN : 128 * (1 + δ₀) * (C + 1) * (1 + K) ^ 3 / δ₀ ^ 3 ≤ Λ := by linarith
    exact final_real hθ hc' hθc hC hδ₀ hK hKΛ hℓlo hℓhi hℓ1 hLlo hLhi hG hR hℓG hΛN

/-- **Headline (conditional).** The strip hypothesis gives `SKQFHyp θ` for all small `θ`. -/
theorem skqfHyp_small_of_strip {c' : ℝ} (hc' : 0 ≤ c') (H : SvStripHyp c') :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₁ → SKQFHyp θ :=
  ⟨1 / (8 * (c' + 1)), by positivity, fun θ hθ hθ₁ => skqfHyp_of_strip hθ hc'
    (by rw [le_div_iff₀ (by positivity)] at hθ₁; linarith) H⟩

end RamanujanTau.SKQFProof
