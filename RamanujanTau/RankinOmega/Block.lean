/-
# Dyadic-block lower bound for `|M(σ − 2πiξ)|²`, `σ = 3/8 + δ`

Let `M` satisfy, on the line `s = σ − 2πiξ` (`ξ ≥ 1`),

    Lam(s) γₘ(s)⁻¹ = ζ(2s) (s M(s) + c s/(s−1))          (this is `Lam_eq_mellin`).

Then for `0 < δ ≤ 1/16`, `Ξ ≥ Ξ₀`:

    ∫_Ξ^{2Ξ} |M(σ − 2πiξ)|² dξ ≥ K₁ (2Ξ)^{−8δ},

with `K₁ > 0`, `Ξ₀` independent of `δ` and of `M`. Proof: with `w = 1 − s` (so `Lam(w) = Lam(s)`),
`c_g ξ^{2−4σ} |Z(w)| ≤ |ζ(2s)| |s M(s) + c s/(s−1)|` (`gamma_ratio_lower`); integrate against
`∫|Z(w)| ≫ Ξ` (`Zf_first_moment`) and `∫|ζ(2s)|² ≪ Ξ` (`zeta_mean_sq`) with an optimized AM–GM. The
exponent: `Ξ^{2(2−4σ)+1}/Ξ² = Ξ^{−8δ}` — degree `4` doubled, exactly as `(d−1)/(2d) = 3/8`.
-/
import RamanujanTau.RankinOmega.Mellin
import RamanujanTau.RankinOmega.ZetaMean

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open scoped Real Interval

section Block

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

lemma amgm_aux {g X lam : ℝ} (hl : 0 < lam) : g * X ≤ (lam ^ 2 * g ^ 2 + X ^ 2) / (2 * lam) := by
  rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (lam * g - X)]

lemma sq_add_le_aux (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

lemma final_alg {K B Ξ I2 c e δ : ℝ} (hK : 0 < K) (hB : 0 < B) (hΞ : 1 ≤ Ξ) (he : 2 * e = 1 - 8 * δ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16) (hq : (16 * c ^ 2 / K) ^ 2 ≤ Ξ)
    (hkey : K * Ξ ^ (2 * e) * Ξ ≤ 2 * B ^ 2 * Ξ ^ 2 * I2 + 8 * c ^ 2 * Ξ) :
    K / (4 * B ^ 2) * (2 * Ξ) ^ (-(8 * δ)) ≤ I2 := by
  have hΞ0 : 0 < Ξ := by linarith
  have h1 : K * Ξ ^ (2 * e) ≤ 2 * B ^ 2 * Ξ * I2 + 8 * c ^ 2 := by
    have : (K * Ξ ^ (2 * e)) * Ξ ≤ (2 * B ^ 2 * Ξ * I2 + 8 * c ^ 2) * Ξ := by nlinarith
    exact le_of_mul_le_mul_right this hΞ0
  have hsq : 16 * c ^ 2 / K ≤ Ξ ^ (2 * e) := by
    have h0 : 0 ≤ 16 * c ^ 2 / K := by positivity
    have hs : 16 * c ^ 2 / K ≤ Real.sqrt Ξ := by
      rw [← Real.sqrt_sq h0]; exact Real.sqrt_le_sqrt hq
    rw [Real.sqrt_eq_rpow] at hs
    exact hs.trans (Real.rpow_le_rpow_of_exponent_le hΞ (by linarith))
  have h2 : 8 * c ^ 2 ≤ K * Ξ ^ (2 * e) / 2 := by
    have := mul_le_mul_of_nonneg_left hsq hK.le
    rw [mul_div_cancel₀ _ hK.ne'] at this; linarith
  have h3 : K * Ξ ^ (2 * e) ≤ 4 * B ^ 2 * Ξ * I2 := by linarith
  have h4 : Ξ ^ (2 * e) = Ξ ^ (-(8 * δ)) * Ξ := by
    rw [he, ← Real.rpow_add_one hΞ0.ne']; ring_nf
  have h5 : (2 * Ξ) ^ (-(8 * δ)) ≤ Ξ ^ (-(8 * δ)) :=
    Real.rpow_le_rpow_of_nonpos hΞ0 (by linarith) (by linarith)
  have hp : 0 ≤ Ξ ^ (-(8 * δ)) := by positivity
  rw [h4] at h3
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h6 : K * Ξ ^ (-(8 * δ)) ≤ 4 * B ^ 2 * I2 := by
    have : (K * Ξ ^ (-(8 * δ))) * Ξ ≤ (4 * B ^ 2 * I2) * Ξ := by linarith
    exact le_of_mul_le_mul_right this hΞ0
  calc K * (2 * Ξ) ^ (-(8 * δ)) ≤ K * Ξ ^ (-(8 * δ)) := by gcongr
    _ ≤ 4 * B ^ 2 * I2 := h6
    _ = I2 * (4 * B ^ 2) := by ring

/-- The first moment in the `ξ`-variable (`y = 2πξ`). -/
lemma g1_lower {c3 Y0 : ℝ}
    (hfm : ∀ σ' : ℝ, 9 / 16 ≤ σ' → σ' ≤ 5 / 8 → ∀ Y : ℝ, Y0 ≤ Y →
      c3 * Y ≤ ∫ y in Y..2 * Y, ‖Zf d ((σ' : ℂ) + y * I)‖)
    {σ' : ℝ} (h1 : 9 / 16 ≤ σ') (h2 : σ' ≤ 5 / 8) {Ξ : ℝ} (hY : Y0 ≤ 2 * π * Ξ) :
    c3 * Ξ ≤ ∫ ξ in Ξ..2 * Ξ, ‖Zf d ((σ' : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ := by
  have hpi : 0 < 2 * π := by positivity
  have hsub := intervalIntegral.integral_comp_mul_left (a := Ξ) (b := 2 * Ξ)
    (fun y : ℝ => ‖Zf d ((σ' : ℂ) + (y : ℂ) * I)‖) (show (2 * π : ℝ) ≠ 0 by positivity)
  have e2 : (2 * π) * (2 * Ξ) = 2 * (2 * π * Ξ) := by ring
  simp only [e2, smul_eq_mul] at hsub
  rw [hsub]
  have hfm' := hfm σ' h1 h2 (2 * π * Ξ) hY
  calc c3 * Ξ = (2 * π)⁻¹ * (c3 * (2 * π * Ξ)) := by field_simp
    _ ≤ _ := by gcongr

/-- The mean square of `ζ(2s)` in the `ξ`-variable (`t = 4πξ`). -/
lemma g2_upper {Cz0 : ℝ}
    (hζ : ∀ u : ℝ, 3 / 4 ≤ u → u ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      ∫ t in T..2 * T, ‖riemannZeta ((u : ℂ) - t * I)‖ ^ 2 ≤ Cz0 * T)
    {σ : ℝ} (h1 : 3 / 8 ≤ σ) (h2 : σ ≤ 1 / 2) {Ξ : ℝ} (hΞ : 1 ≤ Ξ) :
    ∫ ξ in Ξ..2 * Ξ, ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2 ≤ Cz0 * Ξ := by
  have h4 : 0 < 4 * π := by positivity
  have e : ∀ ξ : ℝ, ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2 =
      ‖riemannZeta (((2 * σ : ℝ) : ℂ) - (((4 * π) * ξ : ℝ) : ℂ) * I)‖ ^ 2 := by
    intro ξ; congr 3; push_cast; ring
  simp_rw [e]
  have hsub := intervalIntegral.integral_comp_mul_left (a := Ξ) (b := 2 * Ξ)
    (fun t : ℝ => ‖riemannZeta (((2 * σ : ℝ) : ℂ) - (t : ℂ) * I)‖ ^ 2)
    (show (4 * π : ℝ) ≠ 0 by positivity)
  have e2 : (4 * π) * (2 * Ξ) = 2 * (4 * π * Ξ) := by ring
  simp only [e2, smul_eq_mul] at hsub
  rw [hsub]
  have hz := hζ (2 * σ) (by linarith) (by linarith) (4 * π * Ξ) (by nlinarith [Real.pi_gt_three])
  calc (4 * π)⁻¹ * ∫ t in 4 * π * Ξ..2 * (4 * π * Ξ), ‖riemannZeta (((2 * σ : ℝ) : ℂ) - (t : ℂ) * I)‖ ^ 2
      ≤ (4 * π)⁻¹ * (Cz0 * (4 * π * Ξ)) := by gcongr
    _ = Cz0 * Ξ := by field_simp

/-- **The pointwise inequality** on the block. -/
lemma block_pt {cg : ℝ}
    (hΓ : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 1 / 2 → 1 ≤ y →
      cg * y ^ (2 - 4 * σ) * ‖invGamM m (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
        ‖invGamM m ((σ : ℂ) - y * I)‖)
    (hcg : 0 < cg) {σ : ℝ} (h1 : 3 / 8 ≤ σ) (h2 : σ ≤ 7 / 16) (c : ℝ) {Ξ ξ : ℝ} (hΞ : 1 ≤ Ξ)
    (hξ : ξ ∈ Icc Ξ (2 * Ξ)) (M : ℂ → ℂ)
    (hid : Lam d ((σ : ℂ) - 2 * π * ξ * I) * invGamM m ((σ : ℂ) - 2 * π * ξ * I) =
      riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I)) *
        (((σ : ℂ) - 2 * π * ξ * I) * M ((σ : ℂ) - 2 * π * ξ * I) +
          c * ((σ : ℂ) - 2 * π * ξ * I) / (((σ : ℂ) - 2 * π * ξ * I) - 1))) :
    cg * Ξ ^ (2 - 4 * σ) * ‖Zf d (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ ≤
      ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ *
        ((1 + 4 * π) * Ξ * ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ + 2 * |c|) := by
  have hπ : 3 < π := Real.pi_gt_three
  have hξ1 : 1 ≤ ξ := le_trans hΞ hξ.1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 2 * π * ξ := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy]; nlinarith
  have hyξ : ξ ≤ y := by rw [hy]; nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) - 2 * π * ξ * I := ⟨_, rfl⟩
  have hsy : s = (σ : ℂ) - y * I := by rw [hs, hy]; push_cast; ring
  rw [← hs] at hid ⊢
  rw [← hy]
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((1 - σ : ℝ) : ℂ) + y * I := ⟨_, rfl⟩
  rw [← hw]
  have hw1s : w = 1 - s := by rw [hw, hsy]; push_cast; ring
  have hG := hΓ σ y h1 (by linarith) hy1
  rw [← hsy, ← hw] at hG
  have hLam : Lam d w = Lam d s := by rw [hw1s]; exact Lam_fe d s
  obtain ⟨X, hX⟩ : ∃ X : ℂ, X = s * M s + c * s / (s - 1) := ⟨_, rfl⟩
  rw [← hX] at hid
  have hZ : Zf d w * invGamM m s = riemannZeta (2 * s) * X * invGamM m w := by
    rw [Zf, hLam, ← hid]; ring
  have hnorm := congrArg norm hZ
  simp only [norm_mul] at hnorm
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  have hiw : 0 < ‖invGamM m w‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := gamM_mul_invGamM m hwre
    rw [h, mul_zero] at this; exact zero_ne_one this
  have hsre : s.re = σ := by rw [hsy]; simp
  have hsim : s.im = -y := by rw [hsy]; simp
  have hZ1 : cg * y ^ (2 - 4 * σ) * ‖Zf d w‖ ≤ ‖riemannZeta (2 * s)‖ * ‖X‖ := by
    have : (cg * y ^ (2 - 4 * σ) * ‖Zf d w‖) * ‖invGamM m w‖ ≤
        (‖riemannZeta (2 * s)‖ * ‖X‖) * ‖invGamM m w‖ := by
      calc (cg * y ^ (2 - 4 * σ) * ‖Zf d w‖) * ‖invGamM m w‖
          = ‖Zf d w‖ * (cg * y ^ (2 - 4 * σ) * ‖invGamM m w‖) := by ring
        _ ≤ ‖Zf d w‖ * ‖invGamM m s‖ := by gcongr
        _ = _ := by rw [hnorm]
    exact le_of_mul_le_mul_right this hiw
  have hsn : ‖s‖ ≤ (1 + 4 * π) * Ξ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim, abs_neg, abs_of_pos (by linarith), abs_of_pos (by linarith), hy]
    nlinarith [hξ.2]
  have hs1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = -y := by simp [hsim]
    rw [him, abs_neg, abs_of_pos (by linarith)] at this; linarith
  have hcs : ‖c * s / (s - 1)‖ ≤ 2 * |c| := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by linarith)]
    have : ‖s‖ ≤ ‖s - 1‖ + 1 := by
      have := norm_add_le (s - 1) 1; simp at this; linarith
    have := abs_nonneg c
    nlinarith
  have hXn : ‖X‖ ≤ (1 + 4 * π) * Ξ * ‖M s‖ + 2 * |c| := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have : ‖s‖ * ‖M s‖ ≤ (1 + 4 * π) * Ξ * ‖M s‖ := by gcongr
    linarith
  have hyΞ : Ξ ^ (2 - 4 * σ) ≤ y ^ (2 - 4 * σ) :=
    Real.rpow_le_rpow (by linarith) (le_trans hξ.1 hyξ) (by linarith)
  calc cg * Ξ ^ (2 - 4 * σ) * ‖Zf d w‖ ≤ cg * y ^ (2 - 4 * σ) * ‖Zf d w‖ := by gcongr
    _ ≤ ‖riemannZeta (2 * s)‖ * ‖X‖ := hZ1
    _ ≤ _ := by gcongr

include habs in
theorem block_lower (hm : 1 ≤ m) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) (c : ℝ) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∃ Ξ0 : ℝ, 1 ≤ Ξ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 → ∀ M : ℂ → ℂ,
      (∀ ξ : ℝ, 1 ≤ ξ →
        Lam d (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) *
            invGamM m (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) =
          riemannZeta (2 * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) *
            ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) * M (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) +
              c * (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) /
                ((((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I) - 1))) →
      Continuous (fun ξ : ℝ => M (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)) →
      ∀ Ξ : ℝ, Ξ0 ≤ Ξ → K1 * (2 * Ξ) ^ (-(8 * δ)) ≤
        ∫ ξ in Ξ..2 * Ξ, ‖M (((3 / 8 + δ : ℝ) : ℂ) - 2 * π * ξ * I)‖ ^ 2 := by
  obtain ⟨cg, hcg, hΓ⟩ := gamma_ratio_lower m hm
  obtain ⟨c3, hc3, Y0, hY0, hfm⟩ := Zf_first_moment d habs hm hn0 hlow ha0
  obtain ⟨Cz0, hCz0, hζ⟩ := zeta_mean_sq
  obtain ⟨Cz, hCz⟩ : ∃ Cz : ℝ, Cz = Cz0 + 1 := ⟨_, rfl⟩
  have hCzp : 0 < Cz := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + 4 * π := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (cg * c3) ^ 2 / Cz := ⟨_, rfl⟩
  have hKp : 0 < K := by rw [hK]; positivity
  refine ⟨K / (4 * B ^ 2), by positivity, max (max 1 (Y0 / (2 * π))) ((16 * c ^ 2 / K) ^ 2),
    le_trans (le_max_left _ _) (le_max_left _ _), fun δ hδ0 hδ1 M hM hMc Ξ hΞ => ?_⟩
  have hΞ1 : 1 ≤ Ξ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΞ
  have hΞY : Y0 / (2 * π) ≤ Ξ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΞ
  have hΞq : (16 * c ^ 2 / K) ^ 2 ≤ Ξ := le_trans (le_max_right _ _) hΞ
  have hΞ0 : 0 < Ξ := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 3 / 8 + δ := ⟨_, rfl⟩
  rw [← hσ] at hM hMc ⊢
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 - 4 * σ := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he, hσ]; linarith
  -- the three functions
  have hsc : Continuous fun ξ : ℝ => (σ : ℂ) - 2 * π * ξ * I := by fun_prop
  have hgMc : Continuous fun ξ : ℝ => ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ := hMc.norm
  have hg1c : ContinuousOn (fun ξ : ℝ => ‖Zf d (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖)
      (uIcc Ξ (2 * Ξ)) := by
    intro ξ hξ
    rw [uIcc_of_le (by linarith)] at hξ
    have hpos : (0 : ℝ) < 2 * π * ξ := mul_pos (by positivity) (by linarith [hξ.1])
    have him : 0 < (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I).im := by simpa using hpos
    have h0 : ((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I ≠ 0 := by
      intro h; rw [h] at him; simp at him
    have h1 : ((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I ≠ 1 := by
      intro h; rw [h] at him; simp at him
    exact ((differentiableAt_Zf d h0 h1).continuousAt.comp
      (f := fun ξ : ℝ => ((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) (x := ξ)
      (by fun_prop)).norm.continuousWithinAt
  have hg2c : ContinuousOn (fun ξ : ℝ => ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2)
      (uIcc Ξ (2 * Ξ)) := by
    intro ξ hξ
    rw [uIcc_of_le (by linarith)] at hξ
    have hne : 2 * ((σ : ℂ) - 2 * π * ξ * I) ≠ 1 := by
      have hpos : (0 : ℝ) < 4 * π * ξ := mul_pos (by positivity) (by linarith [hξ.1])
      have him : (2 * ((σ : ℂ) - 2 * π * ξ * I)).im = -(4 * π * ξ) := by simp; ring
      intro h; rw [h, Complex.one_im] at him; linarith only [him, hpos]
    exact ((((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun ξ : ℝ => 2 * ((σ : ℂ) - 2 * π * ξ * I)) (x := ξ) (by fun_prop)).norm).pow 2).continuousWithinAt
  -- first moment and ζ mean square
  have hpi : 0 < 2 * π := by positivity
  have hYb : Y0 ≤ 2 * π * Ξ := by have := (div_le_iff₀ hpi).1 hΞY; linarith
  have hg1_ge := g1_lower d hfm (σ' := 1 - σ) (by rw [hσ]; linarith) (by rw [hσ]; linarith) hYb
  have hg2_le := g2_upper hζ (σ := σ) (by rw [hσ]; linarith) (by rw [hσ]; linarith) hΞ1
  -- AM–GM with the optimal parameter
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = cg * c3 * Ξ ^ e * Ξ := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = A / (Cz * Ξ) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hpt2 : ∀ ξ ∈ Icc Ξ (2 * Ξ),
      cg * Ξ ^ e * ‖Zf d (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ ≤
        lam / 2 * ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2 +
          B ^ 2 * Ξ ^ 2 / lam * ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ ^ 2 + 4 * c ^ 2 / lam := by
    intro ξ hξ
    have h := block_pt d hΓ hcg (σ := σ) (by rw [hσ]; linarith) (by rw [hσ]; linarith) c hΞ1 hξ M
      (hM ξ (le_trans hΞ1 hξ.1))
    rw [← he, ← hB] at h
    obtain ⟨g2, hg2⟩ : ∃ g2 : ℝ, g2 = ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ := ⟨_, rfl⟩
    obtain ⟨gM, hgM⟩ : ∃ gM : ℝ, gM = ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ := ⟨_, rfl⟩
    rw [← hg2, ← hgM] at h ⊢
    have hXb2 : (B * Ξ * gM + 2 * |c|) ^ 2 ≤ 2 * B ^ 2 * Ξ ^ 2 * gM ^ 2 + 8 * c ^ 2 := by
      have := sq_add_le_aux (B * Ξ * gM) (2 * |c|)
      have e : 2 * (B * Ξ * gM) ^ 2 + 2 * (2 * |c|) ^ 2 = 2 * B ^ 2 * Ξ ^ 2 * gM ^ 2 + 8 * c ^ 2 := by
        rw [show (2 * |c|) ^ 2 = 4 * c ^ 2 by rw [mul_pow, sq_abs]; norm_num]; ring
      linarith
    have hamgm := amgm_aux (g := g2) (X := B * Ξ * gM + 2 * |c|) hlam0
    have e1 : (lam ^ 2 * g2 ^ 2 + (2 * B ^ 2 * Ξ ^ 2 * gM ^ 2 + 8 * c ^ 2)) / (2 * lam) =
        lam / 2 * g2 ^ 2 + B ^ 2 * Ξ ^ 2 / lam * gM ^ 2 + 4 * c ^ 2 / lam := by
      field_simp; ring
    have h3 : (lam ^ 2 * g2 ^ 2 + (B * Ξ * gM + 2 * |c|) ^ 2) / (2 * lam) ≤
        (lam ^ 2 * g2 ^ 2 + (2 * B ^ 2 * Ξ ^ 2 * gM ^ 2 + 8 * c ^ 2)) / (2 * lam) := by
      gcongr
    linarith
  have hI2i : IntervalIntegrable (fun ξ : ℝ => ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ ^ 2) volume Ξ (2 * Ξ) :=
    (hgMc.pow 2).intervalIntegrable _ _
  have hg2i : IntervalIntegrable (fun ξ : ℝ => ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2)
      volume Ξ (2 * Ξ) := hg2c.intervalIntegrable
  have hint1 : cg * Ξ ^ e * ∫ ξ in Ξ..2 * Ξ, ‖Zf d (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ ≤
      ∫ ξ in Ξ..2 * Ξ, (lam / 2 * ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2 +
          B ^ 2 * Ξ ^ 2 / lam * ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ ^ 2 + 4 * c ^ 2 / lam) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ hpt2
    · exact (hg1c.const_smul (cg * Ξ ^ e)).intervalIntegrable
    · exact (((hg2i.const_mul _).add (hI2i.const_mul _)).add intervalIntegrable_const)
  rw [intervalIntegral.integral_add ((hg2i.const_mul _).add (hI2i.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_add (hg2i.const_mul _) (hI2i.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at hint1
  obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ, I2 = ∫ ξ in Ξ..2 * Ξ, ‖M ((σ : ℂ) - 2 * π * ξ * I)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hI2] at hint1 ⊢
  have hAle : A ≤ cg * Ξ ^ e *
      ∫ ξ in Ξ..2 * Ξ, ‖Zf d (((1 - σ : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ := by
    rw [hA]
    have : 0 ≤ cg * Ξ ^ e := by positivity
    calc cg * c3 * Ξ ^ e * Ξ = cg * Ξ ^ e * (c3 * Ξ) := by ring
      _ ≤ _ := by gcongr
  have hz2 : lam / 2 * (∫ ξ in Ξ..2 * Ξ, ‖riemannZeta (2 * ((σ : ℂ) - 2 * π * ξ * I))‖ ^ 2) ≤
      lam / 2 * (Cz * Ξ) := by
    have : Cz0 * Ξ ≤ Cz * Ξ := by rw [hCz]; nlinarith
    gcongr; linarith
  have hlamCz : lam / 2 * (Cz * Ξ) = A / 2 := by rw [hlam]; field_simp
  have hmain : A ≤ A / 2 + B ^ 2 * Ξ ^ 2 / lam * I2 + 4 * c ^ 2 / lam * (2 * Ξ - Ξ) := by
    linarith
  have hkey : A * lam ≤ 2 * B ^ 2 * Ξ ^ 2 * I2 + 8 * c ^ 2 * Ξ := by
    have h := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 * lam by positivity)
    have e1 : 2 * lam * (A / 2 + B ^ 2 * Ξ ^ 2 / lam * I2 + 4 * c ^ 2 / lam * (2 * Ξ - Ξ)) =
        lam * A + 2 * B ^ 2 * Ξ ^ 2 * I2 + 8 * c ^ 2 * Ξ := by field_simp; ring
    rw [e1] at h; nlinarith
  have hAlam : A * lam = K * Ξ ^ (2 * e) * Ξ := by
    rw [hlam, hA, hK, show 2 * e = e * 2 by ring, Real.rpow_mul hΞ0.le, Real.rpow_two]
    field_simp
  rw [hAlam] at hkey
  exact final_alg hKp hBp hΞ1 (by rw [he, hσ]; ring) hδ0 hδ1 hΞq hkey

end Block

end RamanujanTau.RankinOmega
