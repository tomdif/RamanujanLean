/-
# The final real inequality: the `int_bound` right-hand side is `≤ (D/√K) h²` (level 1)
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

lemma log_one_add_le_sqrt {K : ℝ} (hK : 1 ≤ K) : Real.log (1 + K) ≤ 3 * Real.sqrt K := by
  have hs := Real.sqrt_nonneg K
  have hsK := Real.sq_sqrt (by linarith : (0:ℝ) ≤ K)
  have h1 : Real.sqrt (1 + K) ≤ 3 / 2 * Real.sqrt K := by
    rw [Real.sqrt_le_iff]; constructor
    · positivity
    · nlinarith
  have h2 : Real.log (Real.sqrt (1 + K)) ≤ Real.sqrt (1 + K) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
  rw [Real.log_sqrt (by linarith)] at h2
  linarith

set_option maxHeartbeats 2000000 in
theorem final_real {θ c' C δ₀ K Λ ℓ L G R : ℝ} (hθ : 0 < θ) (hc' : 0 ≤ c')
    (hθc : 8 * (c' + 1) * θ ≤ 1) (hC : 0 ≤ C) (hδ₀ : 0 < δ₀) (hK : 1 ≤ K) (hKΛ : K ≤ Λ)
    (hℓlo : θ * Λ / 2 ≤ ℓ) (hℓhi : ℓ ≤ θ * Λ) (hℓ1 : 1 ≤ ℓ) (hLlo : Λ / 2 ≤ L) (hLhi : L ≤ Λ)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hℓG : 2 * G * C * (1 + K) ^ 3 ≤ ℓ)
    (hΛN : 128 * (1 + δ₀) * (C + 1) * (1 + K) ^ 3 / δ₀ ^ 3 ≤ Λ) :
    2 * G * (K / Λ) ^ 2 * (C * (1 + K / Λ * ℓ) ^ 2 / ℓ) +
      4 * R * (C / ℓ) * (K / Λ) * Real.log (1 + K / Λ * L) +
      R * (4 * (K / Λ) * (K / Λ + δ₀) * (C * (1 + K / Λ * ℓ) ^ 2 / ℓ) *
          Real.exp (-((L - c' * ℓ) * δ₀)) / δ₀ +
        16 * (C * (1 + K / Λ * ℓ) ^ 2 / ℓ) / (K / Λ * (L - c' * ℓ) ^ 2) +
        4 * (C / ℓ) / (L - c' * ℓ)) ≤
    (1 + 24 * R * C / θ + R * (1 + 2048 * C / θ + 32 * C / θ)) / Real.sqrt K * (K / Λ) ^ 2 := by
  set s := Real.sqrt K with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hK
  have hsK : s ^ 2 = K := Real.sq_sqrt (by linarith)
  clear_value s
  have hΛ : 0 < Λ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set h := K / Λ with hhdef
  clear_value h
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hΛ]; exact hKΛ
  have hθ8 : θ ≤ 1 / 8 := by nlinarith
  have hc'θ : c' * θ ≤ 1 / 8 := by nlinarith
  have hℓΛ : ℓ ≤ Λ := by nlinarith
  have hhℓ : h * ℓ ≤ K := by
    rw [hhdef, div_mul_eq_mul_div, div_le_iff₀ hΛ]; nlinarith
  have hhL : h * L ≤ K := by
    rw [hhdef, div_mul_eq_mul_div, div_le_iff₀ hΛ]; nlinarith
  set b := L - c' * ℓ with hbdef
  clear_value b
  have hb : Λ / 4 ≤ b := by rw [hbdef]; nlinarith
  have hb0 : 0 < b := by linarith
  have hM1 : C * (1 + h * ℓ) ^ 2 / ℓ ≤ C * (1 + K) ^ 2 / ℓ := by
    have : 0 ≤ h * ℓ := by positivity
    gcongr
  have hinvℓ : 1 / ℓ ≤ 2 / (θ * Λ) := by
    rw [div_le_div_iff₀ hℓ0 (by positivity)]; linarith
  have hh2s : h ^ 2 / s = s ^ 3 / Λ ^ 2 := by
    rw [hhdef, ← hsK]; field_simp
  -- T1
  have T1 : 2 * G * h ^ 2 * (C * (1 + h * ℓ) ^ 2 / ℓ) ≤ h ^ 2 / s := by
    have hsK1 : s ≤ 1 + K := by nlinarith
    have k1 : 2 * G * C * (1 + K) ^ 2 / ℓ ≤ 1 / s := by
      rw [div_le_div_iff₀ hℓ0 (by positivity)]
      have : 2 * G * C * (1 + K) ^ 2 * s ≤ 2 * G * C * (1 + K) ^ 2 * (1 + K) :=
        mul_le_mul_of_nonneg_left hsK1 (by positivity)
      nlinarith
    calc 2 * G * h ^ 2 * (C * (1 + h * ℓ) ^ 2 / ℓ) ≤ 2 * G * h ^ 2 * (C * (1 + K) ^ 2 / ℓ) :=
          mul_le_mul_of_nonneg_left hM1 (by positivity)
      _ = h ^ 2 * (2 * G * C * (1 + K) ^ 2 / ℓ) := by ring
      _ ≤ h ^ 2 * (1 / s) := mul_le_mul_of_nonneg_left k1 (by positivity)
      _ = h ^ 2 / s := by ring
  -- T2
  have T2 : 4 * R * (C / ℓ) * h * Real.log (1 + h * L) ≤ 24 * R * C / θ * (h ^ 2 / s) := by
    have hlog : Real.log (1 + h * L) ≤ 3 * s := by
      have hL00 : 0 ≤ L := by linarith
      have hL0 : 0 ≤ h * L := by positivity
      exact (Real.log_le_log (x := 1 + h * L) (y := 1 + K) (by linarith) (by linarith)).trans (hs ▸ log_one_add_le_sqrt hK)
    have hlog0 : 0 ≤ Real.log (1 + h * L) := Real.log_nonneg (by
      have : 0 ≤ L := by linarith
      have : 0 ≤ h * L := by positivity
      linarith)
    have hCl : C / ℓ ≤ 2 * C / (θ * Λ) := by
      rw [show C / ℓ = C * (1 / ℓ) by ring, show 2 * C / (θ * Λ) = C * (2 / (θ * Λ)) by ring]
      exact mul_le_mul_of_nonneg_left hinvℓ hC
    calc 4 * R * (C / ℓ) * h * Real.log (1 + h * L) ≤ 4 * R * (2 * C / (θ * Λ)) * h * (3 * s) := by
          gcongr
      _ = 24 * R * C / θ * (h ^ 2 / s) := by
          rw [hh2s, hhdef, ← hsK]; field_simp; ring
  -- T3a
  have T3a : 4 * h * (h + δ₀) * (C * (1 + h * ℓ) ^ 2 / ℓ) * Real.exp (-(b * δ₀)) / δ₀ ≤ h ^ 2 / s := by
    set x := Λ * δ₀ / 4 with hx
    have hx0 : 0 < x := by positivity
    have hexp : Real.exp (-(b * δ₀)) ≤ 2 / x ^ 2 := by
      have h1 : Real.exp (-(b * δ₀)) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by rw [hx]; nlinarith)
      have h2 := Real.quadratic_le_exp_of_nonneg hx0.le
      refine h1.trans ?_
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      nlinarith
    have hM1' : C * (1 + h * ℓ) ^ 2 / ℓ ≤ C * (1 + K) ^ 2 := by
      refine hM1.trans ?_
      rw [div_le_iff₀ hℓ0]; nlinarith [show 0 ≤ C * (1 + K) ^ 2 by positivity]
    have hN : 128 * (1 + δ₀) * C * (1 + K) ^ 2 ≤ Λ * δ₀ ^ 3 := by
      rw [div_le_iff₀ (by positivity)] at hΛN
      have : (1 + K) ^ 2 ≤ (1 + K) ^ 3 := by nlinarith [show 0 ≤ (1+K)^2 by positivity]
      have h3 : 128 * (1 + δ₀) * C * (1 + K) ^ 2 ≤ 128 * (1 + δ₀) * (C + 1) * (1 + K) ^ 3 := by
        have : C * (1 + K) ^ 2 ≤ (C + 1) * (1 + K) ^ 3 := by nlinarith [show 0 ≤ (1+K)^2 by positivity]
        nlinarith
      linarith
    calc 4 * h * (h + δ₀) * (C * (1 + h * ℓ) ^ 2 / ℓ) * Real.exp (-(b * δ₀)) / δ₀
        ≤ 4 * h * (1 + δ₀) * (C * (1 + K) ^ 2) * (2 / x ^ 2) / δ₀ := by
          gcongr
      _ = h * (128 * (1 + δ₀) * C * (1 + K) ^ 2) / (Λ ^ 2 * δ₀ ^ 3) := by
          rw [hx]; field_simp; ring
      _ ≤ h * (Λ * δ₀ ^ 3) / (Λ ^ 2 * δ₀ ^ 3) := by gcongr
      _ = h / Λ := by field_simp
      _ ≤ h ^ 2 / s := by
          rw [hh2s, hhdef, ← hsK, show s ^ 2 / Λ / Λ = s ^ 2 / Λ ^ 2 by ring]
          exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  -- T3b
  have T3b : 16 * (C * (1 + h * ℓ) ^ 2 / ℓ) / (h * b ^ 2) ≤ 2048 * C / θ * (h ^ 2 / s) := by
    have hb2 : Λ ^ 2 / 16 ≤ b ^ 2 := by nlinarith
    have hCl : C * (1 + K) ^ 2 / ℓ ≤ 2 * C * (1 + K) ^ 2 / (θ * Λ) := by
      rw [show C * (1 + K) ^ 2 / ℓ = C * (1 + K) ^ 2 * (1 / ℓ) by ring,
        show 2 * C * (1 + K) ^ 2 / (θ * Λ) = C * (1 + K) ^ 2 * (2 / (θ * Λ)) by ring]
      exact mul_le_mul_of_nonneg_left hinvℓ (by positivity)
    have hpoly : (1 + K) ^ 2 ≤ 4 * s ^ 5 := by
      rw [← hsK]; nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) hs1 4]
    calc 16 * (C * (1 + h * ℓ) ^ 2 / ℓ) / (h * b ^ 2)
        ≤ 16 * (2 * C * (1 + K) ^ 2 / (θ * Λ)) / (h * (Λ ^ 2 / 16)) :=
          div_le_div₀ (by positivity) (by linarith [hM1.trans hCl]) (by positivity)
            (mul_le_mul_of_nonneg_left hb2 hh0.le)
      _ = 512 * C * (1 + K) ^ 2 / (θ * s ^ 2 * Λ ^ 2) := by
          rw [hhdef, ← hsK]; field_simp; ring
      _ ≤ 512 * C * (4 * s ^ 5) / (θ * s ^ 2 * Λ ^ 2) := by gcongr
      _ = 2048 * C / θ * (h ^ 2 / s) := by
          rw [hh2s]; field_simp; ring
  -- T3c
  have T3c : 4 * (C / ℓ) / b ≤ 32 * C / θ * (h ^ 2 / s) := by
    have hCl : C / ℓ ≤ 2 * C / (θ * Λ) := by
      rw [show C / ℓ = C * (1 / ℓ) by ring, show 2 * C / (θ * Λ) = C * (2 / (θ * Λ)) by ring]
      exact mul_le_mul_of_nonneg_left hinvℓ hC
    calc 4 * (C / ℓ) / b ≤ 4 * (2 * C / (θ * Λ)) / (Λ / 4) := by gcongr
      _ = 32 * C / θ * (1 / Λ ^ 2) := by field_simp; ring
      _ ≤ 32 * C / θ * (h ^ 2 / s) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hh2s]; exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  calc _ ≤ h ^ 2 / s + 24 * R * C / θ * (h ^ 2 / s) +
        R * (h ^ 2 / s + 2048 * C / θ * (h ^ 2 / s) + 32 * C / θ * (h ^ 2 / s)) := by
        gcongr
    _ = _ := by ring

end RamanujanTau.SKQFProof
