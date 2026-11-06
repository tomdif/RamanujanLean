/-
# Pointwise bound for `G_h`, part 3: the bound in terms of `Y` and `t = Y^{1/40}`
-/
import RamanujanTau.SCSProof.Point2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal Real ComplexConjugate

set_option maxHeartbeats 2000000 in
/-- **Pointwise bound** for parameters with `ε = t⁴/2`, `t = Y^{1/40}`. -/
theorem pointwise_par : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : Par, 1 ≤ P.h →
    P.ε = (P.Y ^ (1 / 40 : ℝ)) ^ 4 / 2 → P.h * (4 * π * P.Y) ≤ 1 →
      ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
        K * P.h * Aθ P ^ 32 * (P.Y ^ (1 / 40 : ℝ)) ^ 3 * (1 / P.Y ^ 12) := by
  obtain ⟨M, hM0, hM⟩ := norm_Psi_le
  obtain ⟨CB, hCB0, hCB⟩ := norm_tsum_Iγ_le (1 / 40) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_le
  refine ⟨2 ^ 11 * M ^ 2 + CB + 16 * C₀, by positivity, fun P hh hεt hhY => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  set t := P.Y ^ (1 / 40 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  have hYt : P.Y = t ^ 40 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have hA := Aθ_ge P
  set A := Aθ P
  set R := Rθ P
  have hRA : R = 2 * A ^ 2 := by simp only [R, A, Rθ, Aθ]
  -- `‖Σ I(γ)‖`
  have hSig := hCB P hh
  have hYpow : P.Y ^ (-(3 / 2 : ℝ) - 2 * (1 / 40)) = 1 / t ^ 62 := by
    rw [hYt, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have e : ((40 : ℕ) : ℝ) * (-(3 / 2) - 2 * (1 / 40)) = -((62 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_neg ht0.le, Real.rpow_natCast, one_div]
  rw [hYpow, hεt] at hSig
  have hb : 2 * ‖∑' γ, Iγ P γ‖ ≤ CB * P.h / (4 * t ^ 50) := by
    have e : CB * P.h * ((t ^ 4 / 2) ^ 3) * (1 / t ^ 62) = CB * P.h / (8 * t ^ 50) := by
      field_simp; ring
    rw [e] at hSig
    have : CB * P.h / (4 * t ^ 50) = 2 * (CB * P.h / (8 * t ^ 50)) := by ring
    linarith
  -- `‖Q‖`
  have hQ0 := norm_Q_le P hM0 hM
  have hQ : ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ ≤
      (8 * M ^ 2 * R ^ 16 + CB * P.h / 4) / (4 * t ^ 25) := by
    have hab := sqrt_mul_sqrt_le (a := (M * R ^ 6) ^ 2 * (8 * R ^ 4))
      (b := 2 * ‖∑' γ, Iγ P γ‖) (l := 1 / t ^ 25) (by positivity) (by positivity) (by positivity)
    have e : (M * R ^ 6) ^ 2 * (8 * R ^ 4) = 8 * M ^ 2 * R ^ 16 := by ring
    rw [e] at hab
    have hbl : 2 * ‖∑' γ, Iγ P γ‖ / (1 / t ^ 25) ≤ CB * P.h / 4 / t ^ 25 := by
      rw [div_div_eq_mul_div, div_one]
      calc 2 * ‖∑' γ, Iγ P γ‖ * t ^ 25 ≤ CB * P.h / (4 * t ^ 50) * t ^ 25 := by gcongr
        _ = CB * P.h / 4 / t ^ 25 := by field_simp
    calc ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖
        ≤ 1 / 2 * Real.sqrt ((M * R ^ 6) ^ 2 * (8 * R ^ 4)) * Real.sqrt (2 * ‖∑' γ, Iγ P γ‖) := hQ0
      _ = 1 / 2 * (Real.sqrt (8 * M ^ 2 * R ^ 16) * Real.sqrt (2 * ‖∑' γ, Iγ P γ‖)) := by
          rw [e]; ring
      _ ≤ 1 / 2 * ((1 / t ^ 25 * (8 * M ^ 2 * R ^ 16) + CB * P.h / 4 / t ^ 25) / 2) := by
          gcongr; linarith
      _ = _ := by field_simp; ring
  -- `W`
  have hmI := mI_ge P
  have hmB := mB_ge P
  have hW : 1 / (32 * t ^ 28) ≤ mI P * mB P := by
    have h1 : P.ε / (4 * P.Y) * P.ε ^ 2 ≤ mI P * mB P := by
      have : 0 ≤ P.ε / (4 * P.Y) := by positivity
      exact mul_le_mul hmI hmB (by positivity) (le_trans this hmI)
    have e : P.ε / (4 * P.Y) * P.ε ^ 2 = 1 / (32 * t ^ 28) := by
      rw [hεt, hYt]; field_simp; ring
    linarith
  have hWpos : 0 < mI P * mB P := lt_of_lt_of_le (by positivity) hW
  -- the Lipschitz error
  have hsπ : 0 < π * P.Y := by positivity
  obtain ⟨hs1, hb1⟩ := hT P.h (π * P.Y) hsπ
  obtain ⟨hs2, hb2⟩ := hT P.h (2 * π * P.Y) (by positivity)
  obtain ⟨hs4, hb4⟩ := hT P.h (4 * π * P.Y) (by positivity)
  have hhs1 : (P.h : ℝ) * (π * P.Y) ≤ 1 := by nlinarith [Real.pi_pos]
  have hhs4 : (P.h : ℝ) * (4 * π * P.Y) ≤ 1 := hhY
  have hT1 := laplace_le_of hC₀ P.h hsπ hhs1 hb1
  have hT4 := laplace_le_of hC₀ P.h (by positivity) hhs4 hb4
  have hs1' : Summable (fun n : ℕ => aabs P.h n * Real.exp (-n * ((2 * π * P.Y) / 2))) := by
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; exact hs1
  obtain ⟨hnS, hnB⟩ := n_laplace P.h (by positivity : 0 < 2 * π * P.Y) hs1'
  have hE := cf_sub_le P hhY hnS hs2 hs4
  set S1 := ∑' n : ℕ, n * aabs P.h n * Real.exp (-n * (2 * π * P.Y))
  set T0 := ∑' n : ℕ, aabs P.h n * Real.exp (-n * (4 * π * P.Y))
  have hS1b : S1 ≤ 2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ 12)) := by
    refine hnB.trans ?_
    have e : (2 * π * P.Y) / 2 = π * P.Y := by ring
    rw [e]; gcongr
  have hT0b : T0 ≤ 2 * C₀ * (1 / (π * P.Y) ^ 12) := by
    refine hT4.trans ?_
    gcongr; nlinarith
  set E := (2 * P.Y * A) ^ 12 * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
    13 * (2 * P.Y * A) ^ 12 * P.ε * T0
  have hEb : E ≤ (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A) := by
    have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabs_nonneg _ _)) (Real.exp_pos _).le
    have k1 : (2 * π * P.Y * P.ε * (A + 2)) * S1 ≤ P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12)) := by
      calc (2 * π * P.Y * P.ε * (A + 2)) * S1
          ≤ (2 * π * P.Y * P.ε * (A + 2)) * (2 / (2 * π * P.Y) * (2 * C₀ * (1 / (π * P.Y) ^ 12))) := by
            gcongr
        _ = P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12)) := by field_simp; ring
    have hpos : 0 ≤ (2 * P.Y * A) ^ 12 := by positivity
    have hq : 0 ≤ C₀ * (1 / (π * P.Y) ^ 12) := by positivity
    calc E = (2 * P.Y * A) ^ 12 * ((2 * π * P.Y * P.ε * (A + 2)) * S1) +
          13 * (2 * P.Y * A) ^ 12 * P.ε * T0 := by
          show (2 * P.Y * A) ^ 12 * (2 * π * P.Y * P.ε * (A + 2)) * S1 +
            13 * (2 * P.Y * A) ^ 12 * P.ε * T0 = _
          ring
      _ ≤ (2 * P.Y * A) ^ 12 * (P.ε * (A + 2) * (4 * C₀ * (1 / (π * P.Y) ^ 12))) +
          13 * (2 * P.Y * A) ^ 12 * P.ε * (2 * C₀ * (1 / (π * P.Y) ^ 12)) := by gcongr
      _ = (2 * P.Y * A) ^ 12 * P.ε * (C₀ * (1 / (π * P.Y) ^ 12)) * (4 * A + 34) := by ring
      _ ≤ (2 * P.Y * A) ^ 12 * P.ε * (C₀ * (1 / (π * P.Y) ^ 12)) * (16 * A) := by
          gcongr; linarith
      _ = _ := by ring
  -- main-term comparison
  have hmain := main_term_le P hM0 hM (cf P P.Y (zeta0 P)) E hE
  have hc0 : ‖cf P P.Y (zeta0 P)‖ ≤ ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E := by
    have : ‖cf P P.Y (zeta0 P)‖ * (mI P * mB P) ≤
        (‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) + E) * (mI P * mB P) := by
      rw [add_mul, div_mul_cancel₀ _ hWpos.ne']; linarith
    exact le_of_mul_le_mul_right this hWpos
  have hG := norm_G0_le P hhY
  -- final arithmetic
  have hQW : ‖∫ p, Psi p.1 p.2 * conj (ft P p)‖ / (mI P * mB P) ≤
      (8 * M ^ 2 * R ^ 16 + CB * P.h / 4) * 8 * t ^ 3 := by
    rw [div_le_iff₀ hWpos]
    refine hQ.trans ?_
    have hX : 0 ≤ (8 * M ^ 2 * R ^ 16 + CB * P.h / 4) * 8 * t ^ 3 := by positivity
    calc (8 * M ^ 2 * R ^ 16 + CB * P.h / 4) / (4 * t ^ 25)
        = (8 * M ^ 2 * R ^ 16 + CB * P.h / 4) * 8 * t ^ 3 * (1 / (32 * t ^ 28)) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  have hfinal : ‖Gh P.h (2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ)))‖ ≤
      2 / (2 * P.Y) ^ 12 * ((8 * M ^ 2 * R ^ 16 + CB * P.h / 4) * 8 * t ^ 3 +
        (2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A)) := by
    refine hG.trans ?_
    gcongr
    linarith
  refine hfinal.trans ?_
  -- simplify the right-hand side
  have hpi : (1 : ℝ) ≤ π ^ 12 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hA13 : A ^ 13 ≤ A ^ 32 := pow_le_pow_right₀ hA1 (by norm_num)
  have e1 : 2 / (2 * P.Y) ^ 12 * ((8 * M ^ 2 * R ^ 16 + CB * P.h / 4) * 8 * t ^ 3) =
      (2 ^ 11 * M ^ 2 * A ^ 32 + CB * P.h / 2 ^ 10) * t ^ 3 * (1 / P.Y ^ 12) := by
    rw [hRA]; field_simp; ring
  have e2 : 2 / (2 * P.Y) ^ 12 * ((2 * P.Y * A) ^ 12 * P.ε * C₀ * (1 / (π * P.Y) ^ 12) * (16 * A)) =
      16 * C₀ * A ^ 13 * t ^ 4 / π ^ 12 * (1 / P.Y ^ 12) := by
    rw [hεt]; field_simp
  rw [mul_add, e1, e2]
  have hY12 : 0 < 1 / P.Y ^ 12 := by positivity
  have k2 : 16 * C₀ * A ^ 13 * t ^ 4 / π ^ 12 ≤ 16 * C₀ * P.h * A ^ 32 * t ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : t ^ 4 ≤ t ^ 3 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
    have : 16 * C₀ * A ^ 13 * t ^ 4 ≤ 16 * C₀ * P.h * A ^ 32 * t ^ 3 * 1 := by
      have hh' : A ^ 13 * t ^ 4 ≤ P.h * A ^ 32 * t ^ 3 := by
        calc A ^ 13 * t ^ 4 ≤ A ^ 32 * t ^ 3 := by gcongr
          _ = 1 * A ^ 32 * t ^ 3 := by ring
          _ ≤ P.h * A ^ 32 * t ^ 3 := by gcongr
      nlinarith
    calc 16 * C₀ * A ^ 13 * t ^ 4 ≤ 16 * C₀ * P.h * A ^ 32 * t ^ 3 * 1 := this
      _ ≤ 16 * C₀ * P.h * A ^ 32 * t ^ 3 * π ^ 12 := by gcongr
  have k1 : (2 ^ 11 * M ^ 2 * A ^ 32 + CB * P.h / 2 ^ 10) * t ^ 3 ≤
      (2 ^ 11 * M ^ 2 + CB) * P.h * A ^ 32 * t ^ 3 := by
    have hA32 : (1 : ℝ) ≤ A ^ 32 := one_le_pow₀ hA1
    have : 2 ^ 11 * M ^ 2 * A ^ 32 + CB * P.h / 2 ^ 10 ≤ (2 ^ 11 * M ^ 2 + CB) * P.h * A ^ 32 := by
      have h1 : 2 ^ 11 * M ^ 2 * A ^ 32 ≤ 2 ^ 11 * M ^ 2 * P.h * A ^ 32 := by
        have : 0 ≤ 2 ^ 11 * M ^ 2 * A ^ 32 := by positivity
        nlinarith
      have h2 : CB * P.h / 2 ^ 10 ≤ CB * P.h * A ^ 32 := by
        have : 0 ≤ CB * P.h := by positivity
        calc CB * P.h / 2 ^ 10 ≤ CB * P.h * 1 := by
              rw [div_le_iff₀ (by norm_num)]; nlinarith
          _ ≤ CB * P.h * A ^ 32 := by gcongr
      nlinarith
    gcongr
  have := add_le_add (mul_le_mul_of_nonneg_right k1 hY12.le) (mul_le_mul_of_nonneg_right k2 hY12.le)
  calc _ ≤ _ := this
    _ = (2 ^ 11 * M ^ 2 + CB + 16 * C₀) * P.h * A ^ 32 * t ^ 3 * (1 / P.Y ^ 12) := by ring

end RamanujanTau.SCSProof
