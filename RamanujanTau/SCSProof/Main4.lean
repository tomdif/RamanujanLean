/-
# Lipschitz bound for `cf` (part 2)
-/
import RamanujanTau.SCSProof.Main3

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

lemma re_W (y : ℝ) (ζ : ℍ) : (2 * π * y * (1 + I * conj (ζ : ℂ)) : ℂ).re = 2 * π * y * (1 + (ζ : ℂ).im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem cf_sub_le (hhσ : P.h * (4 * π * P.Y) ≤ 1)
    (hS1 : Summable (fun n : ℕ => n * aabs P.h n * Real.exp (-n * (2 * π * P.Y))))
    (hT1 : Summable (fun n : ℕ => aabs P.h n * Real.exp (-n * (2 * π * P.Y))))
    (hT0 : Summable (fun n : ℕ => aabs P.h n * Real.exp (-n * (4 * π * P.Y)))) :
    ∀ y ∈ Icc P.Y (P.Y * (1 + P.ε)), ∀ ζ : ℍ, inB P (ζ : ℂ) →
      ‖cf P y ζ - cf P P.Y (zeta0 P)‖ ≤
        (2 * P.Y * Aθ P) ^ 12 * (2 * π * P.Y * P.ε * (Aθ P + 2)) *
            ∑' n : ℕ, n * aabs P.h n * Real.exp (-n * (2 * π * P.Y)) +
          13 * (2 * P.Y * Aθ P) ^ 12 * P.ε *
            ∑' n : ℕ, aabs P.h n * Real.exp (-n * (4 * π * P.Y)) := by
  intro y hy ζ hζ
  have hY := P.hY; have hε := P.hε; have hε1 := P.hε1
  have hA := Aθ_ge P
  have hy0 : 0 < y := hY.trans_le hy.1
  have hy2 : y ≤ 2 * P.Y := hy.2.trans (Y_mul_le P)
  have hyY : |y - P.Y| ≤ P.Y * P.ε := by
    rw [abs_of_nonneg (by linarith [hy.1])]; nlinarith [hy.2]
  obtain ⟨hb1, hb2, hb3⟩ := inB_bounds P hζ
  set S1 := ∑' n : ℕ, n * aabs P.h n * Real.exp (-n * (2 * π * P.Y))
  set T0 := ∑' n : ℕ, aabs P.h n * Real.exp (-n * (4 * π * P.Y))
  have hS1n : 0 ≤ S1 := tsum_nonneg fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabs_nonneg _ _)) (Real.exp_pos _).le
  have hT0n : 0 ≤ T0 := tsum_nonneg fun n => mul_nonneg (aabs_nonneg _ _) (Real.exp_pos _).le
  set u : ℂ := (y : ℂ) * (I - conj (ζ : ℂ))
  set u0 : ℂ := (P.Y : ℂ) * (I - conj ((zeta0 P : ℍ) : ℂ))
  set Wv : ℂ := 2 * π * y * (1 + I * conj (ζ : ℂ))
  set W0 : ℂ := 2 * π * P.Y * (1 + I * conj ((zeta0 P : ℍ) : ℂ))
  set e : ℝ := Real.exp (-2 * π * P.h * y)
  set e0 : ℝ := Real.exp (-2 * π * P.h * P.Y)
  have hcf : cf P y ζ = u ^ 12 * (e : ℂ) * Gh P.h Wv := rfl
  have hc0 : cf P P.Y (zeta0 P) = u0 ^ 12 * (e0 : ℂ) * Gh P.h W0 := rfl
  have hu : ‖u‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    calc y * ‖I - conj (ζ : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr; exact norm_I_sub_conj P hζ
      _ = _ := by ring
  have hu0 : ‖u0‖ ≤ 2 * P.Y * Aθ P := by
    simp only [u0]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc P.Y * ‖I - conj ((zeta0 P : ℍ) : ℂ)‖ ≤ (2 * P.Y) * Aθ P := by
          gcongr
          · linarith
          · exact norm_I_sub_conj P (inB_zeta0 P)
      _ = _ := by ring
  have huu : ‖u - u0‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
    have e1 : u - u0 = ((y - P.Y : ℝ) : ℂ) * (I - conj (ζ : ℂ)) +
        (P.Y : ℂ) * conj ((zeta0 P : ℍ) - (ζ : ℂ)) := by
      simp only [u, u0, map_sub]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_of_nonneg hY.le]
    have h1 := norm_I_sub_conj P hζ
    have h2 : ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖ ≤ 2 * P.ε := by
      rw [norm_sub_rev]; exact norm_sub_zeta0 P hζ
    calc |y - P.Y| * ‖I - conj (ζ : ℂ)‖ + P.Y * ‖((zeta0 P : ℍ) : ℂ) - (ζ : ℂ)‖
        ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
      _ = _ := by ring
  have hWW : ‖Wv - W0‖ ≤ 2 * π * P.Y * P.ε * (Aθ P + 2) := by
    have e1 : Wv - W0 = 2 * π * ((((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ))) +
        (P.Y : ℂ) * (I * conj ((ζ : ℂ) - (zeta0 P : ℂ)))) := by
      simp only [Wv, W0, map_sub]; push_cast; ring
    rw [e1, norm_mul]
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h2π]
    have : ‖((y - P.Y : ℝ) : ℂ) * (1 + I * conj (ζ : ℂ)) + (P.Y : ℂ) * (I * conj ((ζ : ℂ) -
        (zeta0 P : ℂ)))‖ ≤ P.Y * P.ε * (Aθ P + 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        Complex.norm_conj, Real.norm_eq_abs, Real.norm_of_nonneg hY.le, one_mul]
      have h1 := norm_one_add_I_conj P hζ
      have h2 := norm_sub_zeta0 P hζ
      calc |y - P.Y| * ‖1 + I * conj (ζ : ℂ)‖ + P.Y * ‖(ζ : ℂ) - (zeta0 P : ℂ)‖
          ≤ (P.Y * P.ε) * Aθ P + P.Y * (2 * P.ε) := by gcongr
        _ = _ := by ring
    calc 2 * π * ‖_‖ ≤ 2 * π * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
      _ = _ := by ring
  have hReW : 2 * π * P.Y ≤ Wv.re := by
    simp only [Wv]; rw [re_W]
    have : 2 * π * P.Y * 1 ≤ 2 * π * y * (1 + (ζ : ℂ).im) := by
      gcongr
      · linarith [hy.1]
      · linarith
    linarith
  have hReW0 : W0.re = 4 * π * P.Y := by
    simp only [W0]; rw [re_W, coe_zeta0]; simp; ring
  have hG := norm_Gh_sub_le P.h (by positivity : 0 < 2 * π * P.Y) hReW (by rw [hReW0]; nlinarith
    [Real.pi_pos]) hS1 hT1
  have hG0 : ‖Gh P.h W0‖ ≤ T0 := by
    have := norm_Gh_le P.h W0 (by rw [hReW0]; exact hT0)
    rwa [hReW0] at this
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hh) hy0.le
    linarith)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hee : |e - e0| ≤ P.ε / 2 := by
    have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
    have := real_exp_sub_le (a := 2 * π * P.h * y) (b := 2 * π * P.h * P.Y) (by positivity)
      (by positivity)
    simp only [e, e0]
    rw [show -2 * π * P.h * y = -(2 * π * P.h * y) by ring,
      show -2 * π * P.h * P.Y = -(2 * π * P.h * P.Y) by ring]
    refine this.trans ?_
    rw [show 2 * π * P.h * y - 2 * π * P.h * P.Y = 2 * π * P.h * (y - P.Y) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    calc 2 * π * P.h * |y - P.Y| ≤ 2 * π * P.h * (P.Y * P.ε) := by gcongr
      _ = (P.h * (4 * π * P.Y)) * (P.ε / 2) := by ring
      _ ≤ 1 * (P.ε / 2) := by gcongr
      _ = _ := one_mul _
  -- the decomposition
  rw [hcf, hc0]
  have hsplit : u ^ 12 * (e : ℂ) * Gh P.h Wv - u0 ^ 12 * (e0 : ℂ) * Gh P.h W0 =
      u ^ 12 * (e : ℂ) * (Gh P.h Wv - Gh P.h W0) +
        ((u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)) * Gh P.h W0 := by
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hm : 0 ≤ 2 * P.Y * Aθ P := by positivity
  have hpow := pow12_sub_le u u0 hu hu0
  have t1 : ‖u ^ 12 * (e : ℂ) * (Gh P.h Wv - Gh P.h W0)‖ ≤
      (2 * P.Y * Aθ P) ^ 12 * (2 * π * P.Y * P.ε * (Aθ P + 2)) * S1 := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg he0]
    calc ‖u‖ ^ 12 * e * ‖Gh P.h Wv - Gh P.h W0‖ ≤ (2 * P.Y * Aθ P) ^ 12 * 1 *
          (‖Wv - W0‖ * S1) := by gcongr
      _ ≤ (2 * P.Y * Aθ P) ^ 12 * 1 * ((2 * π * P.Y * P.ε * (Aθ P + 2)) * S1) := by gcongr
      _ = _ := by ring
  have t2 : ‖((u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)) * Gh P.h W0‖ ≤
      13 * (2 * P.Y * Aθ P) ^ 12 * P.ε * T0 := by
    rw [norm_mul]
    have hin : ‖(u ^ 12 - u0 ^ 12) * (e : ℂ) + u0 ^ 12 * ((e - e0 : ℝ) : ℂ)‖ ≤
        13 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg he0, Real.norm_eq_abs]
      have hk : 12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖ ≤ 12 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by
        calc 12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖
            ≤ 12 * (2 * P.Y * Aθ P) ^ 11 * (P.Y * P.ε * (Aθ P + 2)) := by gcongr
          _ ≤ 12 * (2 * P.Y * Aθ P) ^ 11 * ((2 * P.Y * Aθ P) * P.ε) := by
              have : P.Y * P.ε * (Aθ P + 2) ≤ (2 * P.Y * Aθ P) * P.ε := by
                nlinarith [mul_pos hY hε]
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      calc ‖u ^ 12 - u0 ^ 12‖ * e + ‖u0‖ ^ 12 * |e - e0|
          ≤ (12 * (2 * P.Y * Aθ P) ^ 11 * ‖u - u0‖) * 1 + (2 * P.Y * Aθ P) ^ 12 * (P.ε / 2) := by
            gcongr
        _ ≤ 12 * (2 * P.Y * Aθ P) ^ 12 * P.ε + (2 * P.Y * Aθ P) ^ 12 * P.ε := by
            have : 0 ≤ (2 * P.Y * Aθ P) ^ 12 * P.ε := by positivity
            nlinarith
        _ = 13 * (2 * P.Y * Aθ P) ^ 12 * P.ε := by ring
    calc _ ≤ 13 * (2 * P.Y * Aθ P) ^ 12 * P.ε * T0 := by gcongr
      _ = _ := rfl
  linarith

end RamanujanTau.SCSProof
