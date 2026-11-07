/-
# The approximation `ζ(s) ≈ ∑_{n≤N} n^{−s}` in mean square, `N = ⌈T⌉`

For `1/2 ≤ σ ≤ 1`, `T ≥ 1`, `N = ⌈T⌉`, `s = σ − it`:

    ∫_1^T |ζ(s) − ∑_{n≤N} n^{−s}|² dt ≤ (4 + 16π) T^{2−2σ}.

Pointwise (`zeta_formula`) the error is `N^{1−s}/(s−1) − s I_N(s)`; the first part is `≤ N^{1−σ}/t`,
the second is controlled in `L²` by Plancherel (`tail_L2`), with `|s| ≤ 2T`.
-/
import RamanujanTau.ZetaMeanSquare.Tail

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.RankinOmega

/-- The Dirichlet polynomial `∑_{n≤N} n^{−s}`. -/
noncomputable def Pz (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

lemma continuous_Pz_line (N : ℕ) (σ : ℝ) : Continuous fun t : ℝ => Pz N ((σ : ℂ) - t * I) := by
  unfold Pz
  refine continuous_finsetSum _ fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)

lemma continuousAt_zeta_line (σ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun t : ℝ => riemannZeta ((σ : ℂ) - t * I)) t := by
  have hne : (σ : ℂ) - t * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht this
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) - t * I) (x := t) (by fun_prop)

lemma continuousAt_IN_line (N : ℕ) (hN : 1 ≤ N) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ContinuousAt (fun t : ℝ => IN N ((σ : ℂ) - t * I)) t := by
  have hre : 0 < ((σ : ℂ) - t * I).re := by simpa using hσ
  exact (differentiableAt_IN N hN hre).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) - t * I) (x := t) (by fun_prop)

/-- **Pointwise error.** -/
lemma err_pt (N : ℕ) (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    ‖riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I)‖ ≤
      (N : ℝ) ^ (1 - σ) / t + ‖(σ : ℂ) - t * I‖ * ‖IN N ((σ : ℂ) - t * I)‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set s : ℂ := (σ : ℂ) - t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = -t := by simp [hs]
  unfold Pz
  rw [zeta_formula N hN (by rw [hsre]; exact hσ) (by rw [hsim]; linarith)]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_mul]
  have e : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    simp [hsre]
  rw [e]
  have hts : t ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = -t := by simp [hsim]
    rw [him, abs_neg, abs_of_pos ht] at this; exact this
  have h1 : (N : ℝ) ^ (1 - σ) / ‖s - 1‖ ≤ (N : ℝ) ^ (1 - σ) / t :=
    div_le_div_of_nonneg_left (by positivity) ht hts
  linarith

lemma ceil_bounds {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ ⌈T⌉₊ ∧ T ≤ (⌈T⌉₊ : ℝ) ∧ (⌈T⌉₊ : ℝ) ≤ 2 * T := by
  have h1 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T by linarith)
  refine ⟨?_, h1, by linarith⟩
  have : (1 : ℝ) ≤ ⌈T⌉₊ := le_trans hT h1
  exact_mod_cast this

/-- **Mean-square error of the approximation.** -/
theorem err_L2 {σ T : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) - t * I) - Pz ⌈T⌉₊ ((σ : ℂ) - t * I)‖ ^ 2 ≤
      (4 + 16 * Real.pi) * T ^ (2 - 2 * σ) := by
  obtain ⟨hN1, hTN, hNT⟩ := ceil_bounds hT
  set N : ℕ := ⌈T⌉₊ with hN
  have hσ0 : 0 < σ := by linarith
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  set A : ℝ := (N : ℝ) ^ (2 - 2 * σ) with hA
  set B : ℝ → ℝ := fun t => 2 * A * t ^ (-2 : ℤ) + 8 * T ^ 2 * ‖IN N ((σ : ℂ) - t * I)‖ ^ 2 with hB
  have hpt : ∀ t ∈ Icc (1 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I)‖ ^ 2 ≤ B t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hE := err_pt N hN1 hσ0 ht0
    have hsn : ‖(σ : ℂ) - t * I‖ ≤ 2 * T := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, mul_im]
      rw [show σ - (t * 0 - 0 * 1) = σ by ring, show (0 : ℝ) - (t * 1 + 0 * 0) = -t by ring,
        abs_neg, abs_of_pos hσ0, abs_of_pos ht0]
      linarith [ht.2]
    set x := (N : ℝ) ^ (1 - σ) / t with hx
    set J := ‖IN N ((σ : ℂ) - t * I)‖ with hJ
    have hx2 : x ^ 2 = A * t ^ (-2 : ℤ) := by
      rw [hx, div_pow, hA, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, zpow_neg, zpow_ofNat]
      push_cast; ring_nf
    have hJ0 : 0 ≤ J := norm_nonneg _
    have hy : ‖(σ : ℂ) - t * I‖ * J ≤ 2 * T * J := by gcongr
    have hx0 : 0 ≤ x := by positivity
    have h0 := norm_nonneg (riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I))
    have hEle : ‖riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I)‖ ≤ x + 2 * T * J := by
      linarith
    have hsq := pow_le_pow_left₀ h0 hEle 2
    simp only [hB]
    nlinarith [sq_nonneg (x - 2 * T * J)]
  -- continuity
  have hcE : ContinuousOn (fun t : ℝ =>
      ‖riemannZeta ((σ : ℂ) - t * I) - Pz N ((σ : ℂ) - t * I)‖ ^ 2) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (((continuousAt_zeta_line σ ht0).sub (continuous_Pz_line N σ).continuousAt).norm.pow
      2).continuousWithinAt
  have hcB1 : ContinuousOn (fun t : ℝ => 2 * A * t ^ (-2 : ℤ)) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuousAt_zpow₀ t (-2) (Or.inl ht0)).const_mul _).continuousWithinAt
  have hcB2 : Continuous (fun t : ℝ => 8 * T ^ 2 * ‖IN N ((σ : ℂ) - t * I)‖ ^ 2) :=
    continuous_const.mul (continuous_iff_continuousAt.2
      (fun t => (continuousAt_IN_line N hN1 hσ0 t).norm.pow 2))
  have hB2i : IntervalIntegrable (fun t : ℝ => 8 * T ^ 2 * ‖IN N ((σ : ℂ) - t * I)‖ ^ 2)
      volume 1 T := hcB2.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hT hcE.intervalIntegrable
    (hcB1.intervalIntegrable.add hB2i) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add hcB1.intervalIntegrable hB2i,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hz : ∫ t in (1 : ℝ)..T, t ^ (-2 : ℤ) ≤ 1 := by
    rw [integral_zpow (Or.inr ⟨by norm_num, by
      rw [uIcc_of_le hT]; intro h; linarith [h.1]⟩)]
    have : 0 < T ^ ((-2 : ℤ) + 1) := zpow_pos hT0 _
    norm_num
    have : 0 < T⁻¹ := inv_pos.2 hT0
    linarith
  have htail := tail_L2 N hN1 hσ0 hT
  have hA2 : A ≤ 2 * T ^ (2 - 2 * σ) := by
    calc A ≤ (2 * T) ^ (2 - 2 * σ) := Real.rpow_le_rpow hN0.le hNT (by linarith)
      _ = 2 ^ (2 - 2 * σ) * T ^ (2 - 2 * σ) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 ^ (1 : ℝ) * T ^ (2 - 2 * σ) := by
          gcongr
          · norm_num
          · linarith
      _ = 2 * T ^ (2 - 2 * σ) := by rw [Real.rpow_one]
  have hT2 : T ^ 2 * (N : ℝ) ^ (-(2 * σ)) ≤ T ^ (2 - 2 * σ) := by
    have h1 : (N : ℝ) ^ (-(2 * σ)) ≤ T ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith)
    have e : T ^ 2 * T ^ (-(2 * σ)) = T ^ (2 - 2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hT0]; push_cast; ring_nf
    rw [← e]; gcongr
  have hA0 : 0 ≤ A := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hiσ : 1 / σ ≤ 2 := by rw [div_le_iff₀ hσ0]; linarith
  have hT2' : 8 * T ^ 2 * (Real.pi * (N : ℝ) ^ (-(2 * σ)) / σ) ≤ 16 * Real.pi * T ^ (2 - 2 * σ) := by
    have e : 8 * T ^ 2 * (Real.pi * (N : ℝ) ^ (-(2 * σ)) / σ) =
        8 * Real.pi * (T ^ 2 * (N : ℝ) ^ (-(2 * σ))) * (1 / σ) := by field_simp
    rw [e]
    have h0 : 0 ≤ T ^ 2 * (N : ℝ) ^ (-(2 * σ)) := by positivity
    calc 8 * Real.pi * (T ^ 2 * (N : ℝ) ^ (-(2 * σ))) * (1 / σ)
        ≤ 8 * Real.pi * T ^ (2 - 2 * σ) * 2 := by gcongr
      _ = 16 * Real.pi * T ^ (2 - 2 * σ) := by ring
  have hTp : 0 ≤ T ^ (2 - 2 * σ) := by positivity
  calc 2 * A * (∫ t in (1 : ℝ)..T, t ^ (-2 : ℤ)) +
        8 * T ^ 2 * ∫ t in (1 : ℝ)..T, ‖IN N ((σ : ℂ) - t * I)‖ ^ 2
      ≤ 2 * A * 1 + 8 * T ^ 2 * (Real.pi * (N : ℝ) ^ (-(2 * σ)) / σ) := by
        gcongr
    _ ≤ 2 * (2 * T ^ (2 - 2 * σ)) + 16 * Real.pi * T ^ (2 - 2 * σ) := by linarith
    _ = (4 + 16 * Real.pi) * T ^ (2 - 2 * σ) := by ring

end RamanujanTau.ZetaMeanSquare
