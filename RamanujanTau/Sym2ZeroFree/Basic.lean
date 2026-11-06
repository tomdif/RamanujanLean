/-
# Inputs for the zero-free region of `H(s) = ζ(2s)R(s) = ζ(s)L(Sym²Δ,s)`

`HH`, `KK = (s−1)HH` are the continuations of `TauPNTUncond.Edge` (via `RankinSelbergFE`);
`Rt`, `R1` are the Abel continuations of `ZeroFreeRegion.Continuation` (`Re s > 3/5`).

* `KK_eq_zeta_R1`: `KK(s) = ζ(2s)·R1(s)` on `Re s > 3/5` (identity theorem);
* `HH_eq_zeta_Rt`: `HH(s) = ζ(2s)·Rt(s)` on `Re s > 3/5`, `s ≠ 1`;
* `norm_HH_le`: `‖HH(w)‖ ≤ C‖w‖` for `3/4 ≤ Re w ≤ 2`, `|Im w| ≥ 1/2`;
* `norm_FS_antitone`: `σ ↦ ‖HH(σ)³ HH(σ+iγ)⁴ HH(σ+2iγ)‖` is non-increasing on `σ > 1`
  (`log HH = Σ cR(n) n^{−s}` with `cR ≥ 0`, and `Re(3 + 4w + w²) ≥ 0` on `|w| = 1`).
-/
import RamanujanTau.ZeroFreeRegion.Region
import RamanujanTau.TauPNTUncond.Edge

set_option autoImplicit false

namespace RamanujanTau.Sym2ZeroFree

open Complex Metric Set Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.ZeroFreeRegion

/-- `KK(s) = ζ(2s)·R1(s)` on `Re s > 3/5`. -/
theorem KK_eq_zeta_R1 {s : ℂ} (hs : 3 / 5 < s.re) : KK s = riemannZeta (2 * s) * R1 s := by
  set U : Set ℂ := {z : ℂ | 3 / 5 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (3 / 5 : ℝ)).isPreconnected
  have hf : AnalyticOnNhd ℂ KK U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz' : 3 / 5 < z.re := hz
    have : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
    exact (differentiableAt_KK this).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z => riemannZeta (2 * z) * R1 z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz' : 3 / 5 < z.re := hz
    have h2 : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hz2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
      (differentiableAt_riemannZeta h2).comp z (differentiableAt_id.const_mul 2)
    exact (hz2.mul (differentiableAt_R1 hz')).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp only [hU, mem_setOf_eq]; norm_num
  have hev : KK =ᶠ[𝓝 (2 : ℂ)] fun z => riemannZeta (2 * z) * R1 z := by
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with z hz
    have hz' : 1 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
    rw [KK_eq hz0 hz1, HH_eq hz', R1_eq hz']; ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2U hev hs

lemma R1_eq_mul_Rt {s : ℂ} (h1 : s ≠ 1) : R1 s = (s - 1) * Rt s := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold R1 Rt
  field_simp

/-- `HH(s) = ζ(2s)·Rt(s)` on `Re s > 3/5`, `s ≠ 1`. -/
theorem HH_eq_zeta_Rt {s : ℂ} (hs : 3 / 5 < s.re) (h1 : s ≠ 1) :
    HH s = riemannZeta (2 * s) * Rt s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e := KK_eq_zeta_R1 hs
  rw [KK_eq hs0 h1, R1_eq_mul_Rt h1] at e
  have : (s - 1) * (HH s - riemannZeta (2 * s) * Rt s) = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h1'
  · linear_combination h

/-- `‖HH(w)‖ ≤ C‖w‖` for `3/4 ≤ Re w ≤ 2`, `|Im w| ≥ 1/2`. -/
theorem norm_HH_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 3 / 4 ≤ w.re → 1 / 2 ≤ |w.im| →
    ‖HH w‖ ≤ C * ‖w‖ := by
  obtain ⟨K, hK0, hK⟩ := norm_Rt_le
  set Zb : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ ((3 : ℝ) / 2) with hZb
  have hZb0 : 0 ≤ Zb := tsum_nonneg fun n => by positivity
  refine ⟨Zb * (2 * |rsc| + 7 * K), by positivity, fun w hw1 hw2 => ?_⟩
  have hw1' : w ≠ 1 := by
    intro h; rw [h] at hw2; simp at hw2; linarith
  rw [HH_eq_zeta_Rt (by linarith) hw1', norm_mul]
  have hz : ‖riemannZeta (2 * w)‖ ≤ Zb := norm_zeta_le_of_re (by simp; linarith)
  have hwm : 1 / 2 ≤ ‖w - 1‖ := by
    have h := Complex.abs_im_le_norm (w - 1)
    simp only [sub_im, one_im, sub_zero] at h
    linarith
  have hb := hK w (by linarith)
  have hd1 : |rsc| * ‖w‖ / ‖w - 1‖ ≤ 2 * |rsc| * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |rsc| * ‖w‖ := by positivity
    nlinarith
  have hd2 : K / (w.re - 3 / 5) ≤ 7 * K := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hR : ‖Rt w‖ ≤ (2 * |rsc| + 7 * K) * ‖w‖ := by
    have := mul_le_mul_of_nonneg_left hd2 (norm_nonneg w)
    nlinarith
  calc ‖riemannZeta (2 * w)‖ * ‖Rt w‖ ≤ Zb * ((2 * |rsc| + 7 * K) * ‖w‖) := by
        gcongr
    _ = Zb * (2 * |rsc| + 7 * K) * ‖w‖ := by ring

/-! ### Positivity: the 3–4–1 product is norm-antitone -/

/-- The 3–4–1 product `F(σ) = HH(σ)³ HH(σ+iγ)⁴ HH(σ+2iγ)`. -/
noncomputable def FS (σ γ : ℝ) : ℂ :=
  HH σ ^ 3 * HH ((σ : ℂ) + (γ : ℂ) * I) ^ 4 * HH ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)

/-- The real coefficients of `log ‖F(σ)‖`. -/
noncomputable def aS (σ γ : ℝ) (n : ℕ) : ℝ :=
  cR n * ((n : ℝ) ^ σ)⁻¹ *
    (3 + 4 * (n : ℂ) ^ (-((γ : ℂ) * I)) + ((n : ℂ) ^ (-((γ : ℂ) * I))) ^ 2).re

lemma cR_zero : cR 0 = 0 := cR_of_not not_isPrimePow_zero

lemma norm_FS_eq {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    ∃ S : ℝ, HasSum (aS σ γ) S ∧ ‖FS σ γ‖ = Real.exp S := by
  set f : ℕ → ℂ := fun n => (cR n : ℂ)
  set s1 : ℂ := (σ : ℂ) + (γ : ℂ) * I
  set s2 : ℂ := (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I
  have hre0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hre1 : 1 < s1.re := by simp [s1]; linarith
  have hre2 : 1 < s2.re := by simp [s2]; linarith
  have h0 := (LSeriesSummable_cR hre0).LSeriesHasSum
  have h1 := (LSeriesSummable_cR hre1).LSeriesHasSum
  have h2 := (LSeriesSummable_cR hre2).LSeriesHasSum
  set Z := 3 * LSeries f σ + 4 * LSeries f s1 + LSeries f s2
  have hZ : HasSum (fun n => 3 * term f σ n + 4 * term f s1 n + term f s2 n) Z :=
    ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have hZre := Complex.hasSum_re hZ
  have hcoef : ∀ n, (3 * term f σ n + 4 * term f s1 n + term f s2 n).re = aS σ γ n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [aS, cR_zero]
    rw [term_shift f σ γ hn, term_shift f σ (2 * γ) hn, npow_two_shift]
    set w := (n : ℂ) ^ (-((γ : ℂ) * I))
    have hT : term f σ n = ((cR n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn]
      simp only [f]
      rw [show ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl]
      push_cast; ring
    have e : 3 * term f σ n + 4 * (term f σ n * w) + term f σ n * w ^ 2 =
        ((cR n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) * (3 + 4 * w + w ^ 2) := by rw [hT]; ring
    rw [e, Complex.re_ofReal_mul]
    rfl
  simp_rw [hcoef] at hZre
  refine ⟨Z.re, hZre, ?_⟩
  have hprod : FS σ γ = cexp Z := by
    rw [FS, HH_exp hre0, HH_exp hre1, HH_exp hre2]
    simp only [Z, Complex.exp_add]
    rw [show (3 : ℂ) * LSeries f σ = ((3 : ℕ) : ℂ) * LSeries f σ by norm_num,
      show (4 : ℂ) * LSeries f s1 = ((4 : ℕ) : ℂ) * LSeries f s1 by norm_num,
      Complex.exp_nat_mul, Complex.exp_nat_mul]
  rw [hprod, Complex.norm_exp]

lemma aS_anti (γ : ℝ) {σ₁ σ₂ : ℝ} (h12 : σ₁ ≤ σ₂) (n : ℕ) :
    aS σ₂ γ n ≤ aS σ₁ γ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aS, cR_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hw : ‖(n : ℂ) ^ (-((γ : ℂ) * I))‖ = 1 := by
    rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  have hc := re_comb_nonneg _ hw
  have hp : ((n : ℝ) ^ σ₂)⁻¹ ≤ ((n : ℝ) ^ σ₁)⁻¹ :=
    inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hn1 h12)
  unfold aS
  have := cR_nonneg n
  gcongr

/-- **`σ ↦ ‖HH(σ)³HH(σ+iγ)⁴HH(σ+2iγ)‖` is non-increasing on `σ > 1`.** -/
theorem norm_FS_antitone (γ : ℝ) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁) (h12 : σ₁ ≤ σ₂) :
    ‖FS σ₂ γ‖ ≤ ‖FS σ₁ γ‖ := by
  obtain ⟨S1, hS1, e1⟩ := norm_FS_eq h1 γ
  obtain ⟨S2, hS2, e2⟩ := norm_FS_eq (lt_of_lt_of_le h1 h12) γ
  rw [e1, e2, Real.exp_le_exp]
  exact hasSum_le (aS_anti γ h12) hS2 hS1

/-- `‖F(σ)‖ ≥ 1` (reproved from the coefficient form). -/
theorem one_le_norm_FS {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) : 1 ≤ ‖FS σ γ‖ := by
  obtain ⟨S, hS, e⟩ := norm_FS_eq hσ γ
  rw [e]
  refine Real.one_le_exp (hS.nonneg fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aS, cR_zero]
  have hw : ‖(n : ℂ) ^ (-((γ : ℂ) * I))‖ = 1 := by
    rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  have hc := re_comb_nonneg _ hw
  unfold aS
  exact mul_nonneg (mul_nonneg (cR_nonneg n) (by positivity)) hc

end RamanujanTau.Sym2ZeroFree
