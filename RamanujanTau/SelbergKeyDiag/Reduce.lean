/-
# M4: the diagonal clause of `SKSplitHyp'` from `SKQFHyp` and the diagonal evaluation

`DiagApproxHyp θ` is the **M3 output** stated as a named hypothesis (pure analysis, no zeros,
no averages): for `y = ⌊T^θ⌋`, `u ∈ [T/2, 4T]`, `0 < |v| ≤ 1`,

    |DiagLag(u, v) − 2 Re 𝒜(v, log(u/2π))| ≤ C (|v|·|𝒮(v)| + T^{−δ}).

(The `|v|·|𝒮(v)|` term is the Laurent remainder `(R(1−iv) + r₀/(iv) − γ_R)·𝒮(v)`; the
`T^{−δ}` term collects the shifted contour, the phase errors `U ≈ (u/2π)^{−iv}`,
`U·G(iv/2) ≈ (2π)^{iv}` and `W̃ − 1`; see `docs/SELBERG_KEY.md` §3.)

* `abs_reAv_sub_le`: `|Re 𝒜(v,L₁) − Re 𝒜(v,L₂)| ≤ |L₁−L₂|·|𝒮(v)|·(|γ_R||v| + r₀)` (exact algebra);
* `diagLag_bound_of_SKQF`: `SKQFHyp θ ∧ DiagApproxHyp θ ⟹` for every continuous window `0 ≤ φ ≤ 1`
  on `[A,B] ⊆ [T/2, 3T]`, `lagInt DiagLag φ A B h ≤ (D/√K) T h²`;
* `diagLag_bound_phiT`: the same for the fixed window `φ_T` of `SelbergKey4.Window` on `[T/2, 3T]`.
Level 2 on `SKQFHyp θ ∧ DiagApproxHyp θ`; the reduction itself is level 1.
-/
import RamanujanTau.SelbergKeyDiag.Generic
import RamanujanTau.SelbergKeyDiag.Meas
import RamanujanTau.SelbergKey2.Cont
import RamanujanTau.SelbergKey4.Window

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.SelbergKey
open scoped Real

/-- **The diagonal evaluation (M3 output), as a named hypothesis.** -/
def DiagApproxHyp (θ : ℝ) : Prop :=
  ∃ C δ T₁ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ u ∈ Icc (T / 2) (4 * T), ∀ v : ℝ, v ≠ 0 →
    |v| ≤ 1 →
      |DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ u v -
          2 * (Av ⌊T ^ θ⌋₊ v (Real.log (u / (2 * π)))).re| ≤
        C * (|v| * ‖Sv ⌊T ^ θ⌋₊ v‖ + T ^ (-δ))

lemma norm_cexp_sub_le (a b : ℝ) :
    ‖cexp (-((a : ℝ) : ℂ) * I) - cexp (-((b : ℝ) : ℂ) * I)‖ ≤ |a - b| := by
  have e : cexp (-((a : ℝ) : ℂ) * I) - cexp (-((b : ℝ) : ℂ) * I) =
      cexp (((-b : ℝ) : ℂ) * I) * (cexp (I * ((b - a : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2 <;> push_cast <;> ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_sub_comm]

/-- **Moving the frequency `L`** (exact): only the `e^{−ivL}𝒮` terms depend on `L`. -/
theorem abs_reAv_sub_le (y : ℕ) {v : ℝ} (hv : v ≠ 0) (L₁ L₂ : ℝ) :
    |(Av y v L₁).re - (Av y v L₂).re| ≤
      |L₁ - L₂| * ‖Sv y v‖ * (|GoodSecondTerm.gammaD| * |v| + HafnerBridge.r0) := by
  have hr0 := HafnerBridge2.r0_pos
  have e : Av y v L₁ - Av y v L₂ =
      (cexp (-((v * L₁ : ℝ) : ℂ) * I) - cexp (-((v * L₂ : ℝ) : ℂ) * I)) * Sv y v *
        ((GoodSecondTerm.gammaD : ℂ) - (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I)) := by
    unfold Av; ring
  have hvpos : 0 < |v| := abs_pos.2 hv
  have h1 : ‖cexp (-((v * L₁ : ℝ) : ℂ) * I) - cexp (-((v * L₂ : ℝ) : ℂ) * I)‖ ≤ |v| * |L₁ - L₂| := by
    refine (norm_cexp_sub_le _ _).trans (le_of_eq ?_)
    rw [← mul_sub, abs_mul]
  have h2 : ‖(GoodSecondTerm.gammaD : ℂ) - (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I)‖ ≤
      |GoodSecondTerm.gammaD| + HafnerBridge.r0 / |v| := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0]
  calc |(Av y v L₁).re - (Av y v L₂).re| = |(Av y v L₁ - Av y v L₂).re| := by rw [Complex.sub_re]
    _ ≤ ‖Av y v L₁ - Av y v L₂‖ := Complex.abs_re_le_norm _
    _ = ‖cexp (-((v * L₁ : ℝ) : ℂ) * I) - cexp (-((v * L₂ : ℝ) : ℂ) * I)‖ * ‖Sv y v‖ *
          ‖(GoodSecondTerm.gammaD : ℂ) - (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I)‖ := by
        rw [e, norm_mul, norm_mul]
    _ ≤ (|v| * |L₁ - L₂|) * ‖Sv y v‖ * (|GoodSecondTerm.gammaD| + HafnerBridge.r0 / |v|) := by
        gcongr
    _ = |L₁ - L₂| * ‖Sv y v‖ * (|GoodSecondTerm.gammaD| * |v| + HafnerBridge.r0) := by
        field_simp

lemma log_shift_le {t x T : ℝ} (hT : 0 < T) (ht : T / 2 ≤ t) (hx : 0 ≤ x) :
    |Real.log ((t + x) / (2 * π)) - Real.log (t / (2 * π))| ≤ 2 * x / T := by
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < t + x := by linarith
  have hπ : (2 * π) ≠ 0 := by positivity
  rw [Real.log_div hu0.ne' hπ, Real.log_div ht0.ne' hπ,
    show Real.log (t + x) - Real.log (2 * π) - (Real.log t - Real.log (2 * π)) =
      Real.log ((t + x) / t) by rw [Real.log_div hu0.ne' ht0.ne']; ring]
  have h1 : 1 ≤ (t + x) / t := by rw [le_div_iff₀ ht0]; linarith
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [show (t + x) / t - 1 = x / t by field_simp; ring]
  rw [div_le_div_iff₀ ht0 hT]
  nlinarith

/-- **M4: the diagonal clause from `SKQFHyp θ` and the diagonal evaluation** (level 2),
for every continuous window `0 ≤ φ ≤ 1` on `[A, B] ⊆ [T/2, 3T]`. -/
theorem diagLag_bound_of_SKQF {θ : ℝ} (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (φ : ℝ → ℝ) (A B : ℝ), Continuous φ → (∀ t, 0 ≤ φ t) → (∀ t, φ t ≤ 1) →
        T / 2 ≤ A → A ≤ B → B ≤ 3 * T →
        lagInt (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / Real.log T) ≤
          D / Real.sqrt K * T * (K / Real.log T) ^ 2 := by
  obtain ⟨B₀, D₀, hD₀, hSK⟩ := hS
  obtain ⟨C, δ, T₁, hC, hδ, hDA⟩ := hD
  refine ⟨6 * D₀ + 3, by positivity, fun K hK => ?_⟩
  obtain ⟨T₂, hT₂⟩ := hSK K hK
  have hr0 := HafnerBridge2.r0_pos
  set γ := GoodSecondTerm.gammaD
  set r0 := HafnerBridge.r0
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  -- the error `ε(T)` tends to `0`
  set ε : ℝ → ℝ := fun T => C * (K / Real.log T * |B₀| + T ^ (-δ)) +
    4 * (K / Real.log T * T⁻¹) * |B₀| * (r0 + |γ|) with hεdef
  have hlog : Tendsto (fun T : ℝ => K / Real.log T) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul K
    simpa [div_eq_mul_inv] using this
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h1 := (((hlog.mul_const |B₀|).add (tendsto_rpow_neg_atTop hδ)).const_mul C).add
      ((((hlog.mul tendsto_inv_atTop_zero).const_mul 4).mul_const |B₀|).mul_const (r0 + |γ|))
    rw [show C * (0 * |B₀| + 0) + 4 * (0 * 0) * |B₀| * (r0 + |γ|) = (0:ℝ) by ring] at h1
    exact h1
  have hev := (((hεt.eventually_lt_const (show (0:ℝ) < 1 / Real.sqrt K by positivity)).and
    (hlog.eventually_lt_const (show (0:ℝ) < 1 by norm_num))).and
    ((eventually_ge_atTop T₂).and ((eventually_ge_atTop T₁).and (eventually_ge_atTop 3))))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hev
  refine ⟨T₀, fun T hT φ A B hφ hφ0 hφ1 hA hAB hB => ?_⟩
  obtain ⟨⟨hεT, hh1⟩, hTT₂, hTT₁, hT3⟩ := hT₀ T hT
  set y := ⌊T ^ θ⌋₊
  set h := K / Real.log T with hhdef
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hlogT.le
  obtain ⟨hSi, hSii⟩ := hT₂ T hTT₂
  have hB0 : ‖Sv y 0‖ ≤ B₀ := hSi 0 ⟨by linarith, hh0⟩
  have hB₀ : 0 ≤ B₀ := (norm_nonneg _).trans hB0
  have habsB : |B₀| = B₀ := abs_of_nonneg hB₀
  have hε0 : 0 ≤ ε T := by
    simp only [hεdef]
    have : 0 ≤ T ^ (-δ) := Real.rpow_nonneg hT0.le _
    have : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
    positivity
  have hmain := lagInt_le_of_approx (G := DiagLag (HafnerMV2.βSel y) y)
    (SelbergKey2.continuous_DiagLag _ _) (a := fun v L => 2 * (Av y v L).re)
    (fun L => (measurable_reAv y L).const_mul 2) (fun t => Real.log (t / (2 * π)))
    hφ hφ0 hφ1 hAB hh0 hε0 (M := 2 * (D₀ / Real.sqrt K * h ^ 2)) ?happ ?hM
  case happ =>
    intro t ht x hx x' hx' hne
    set v := x' - x
    have hv0 : v ≠ 0 := sub_ne_zero.2 hne
    have hvh : |v| ≤ h := abs_le.2 ⟨by linarith [hx.2, hx'.1], by linarith [hx.1, hx'.2]⟩
    have hv1 : |v| ≤ 1 := hvh.trans hh1.le
    have hSv : ‖Sv y v‖ ≤ B₀ := hSi v ⟨by linarith [(abs_le.1 hvh).1], (abs_le.1 hvh).2⟩
    have hu : t + x ∈ Icc (T / 2) (4 * T) :=
      ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hx.2, hh1]⟩
    have e1 := hDA T hTT₁ (t + x) hu v hv0 hv1
    have e2 := abs_reAv_sub_le y hv0 (Real.log ((t + x) / (2 * π))) (Real.log (t / (2 * π)))
    have e3 := log_shift_le hT0 (hA.trans ht.1) hx.1
    have hxh : 2 * x / T ≤ 2 * h / T := by
      rw [div_le_div_iff_of_pos_right hT0]; linarith [hx.2]
    have b1 : C * (|v| * ‖Sv y v‖ + T ^ (-δ)) ≤ C * (h * |B₀| + T ^ (-δ)) := by
      rw [habsB]; gcongr
    have b2 : |Real.log ((t + x) / (2 * π)) - Real.log (t / (2 * π))| * ‖Sv y v‖ *
        (|γ| * |v| + r0) ≤ (2 * h / T) * |B₀| * (|γ| + r0) := by
      rw [habsB]
      have : |γ| * |v| ≤ |γ| := by
        calc |γ| * |v| ≤ |γ| * 1 := mul_le_mul_of_nonneg_left hv1 (abs_nonneg _)
          _ = |γ| := mul_one _
      gcongr
      exact e3.trans hxh
    have hεe : ε T = C * (h * |B₀| + T ^ (-δ)) + 2 * ((2 * h / T) * |B₀| * (|γ| + r0)) := by
      simp only [hεdef, hhdef]; ring
    rw [hεe]
    calc |DiagLag (HafnerMV2.βSel y) y (t + x) v - 2 * (Av y v (Real.log (t / (2 * π)))).re|
        = |(DiagLag (HafnerMV2.βSel y) y (t + x) v - 2 * (Av y v (Real.log ((t + x) / (2 * π)))).re) +
            2 * ((Av y v (Real.log ((t + x) / (2 * π)))).re - (Av y v (Real.log (t / (2 * π)))).re)| := by
          ring_nf
      _ ≤ |DiagLag (HafnerMV2.βSel y) y (t + x) v - 2 * (Av y v (Real.log ((t + x) / (2 * π)))).re| +
            2 * |(Av y v (Real.log ((t + x) / (2 * π)))).re - (Av y v (Real.log (t / (2 * π)))).re| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_two]
      _ ≤ C * (h * |B₀| + T ^ (-δ)) + 2 * ((2 * h / T) * |B₀| * (|γ| + r0)) := by
          gcongr
          · exact e1.trans b1
          · exact e2.trans b2
  case hM =>
    intro t ht
    have hL : Real.log (t / (2 * π)) ∈ Icc (Real.log (T / (4 * π))) (Real.log T) := by
      have ht0 : 0 < t := by linarith [ht.1]
      constructor
      · refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [ht.1, Real.pi_pos]
      · refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [ht.2, Real.pi_gt_three]
    have := hSii _ hL
    have e : (∫ v in (-h)..h, (h - |v|) * (2 * (Av y v (Real.log (t / (2 * π)))).re)) =
        2 * ∫ v in (-h)..h, (h - |v|) * (Av y v (Real.log (t / (2 * π)))).re := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      ring
    rw [e, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  -- final arithmetic
  refine hmain.trans ?_
  have hBA0 : 0 ≤ B - A := by linarith
  have hBA : B - A ≤ 3 * T := by linarith
  have hX : 2 * (D₀ / Real.sqrt K * h ^ 2) + ε T * h ^ 2 ≤ (2 * D₀ + 1) / Real.sqrt K * h ^ 2 := by
    have : ε T * h ^ 2 ≤ 1 / Real.sqrt K * h ^ 2 :=
      mul_le_mul_of_nonneg_right hεT.le (by positivity)
    have e : (2 * D₀ + 1) / Real.sqrt K * h ^ 2 =
        2 * (D₀ / Real.sqrt K * h ^ 2) + 1 / Real.sqrt K * h ^ 2 := by ring
    linarith
  have hX0 : 0 ≤ 2 * (D₀ / Real.sqrt K * h ^ 2) + ε T * h ^ 2 := by positivity
  calc (B - A) * (2 * (D₀ / Real.sqrt K * h ^ 2) + ε T * h ^ 2)
      ≤ (3 * T) * ((2 * D₀ + 1) / Real.sqrt K * h ^ 2) := mul_le_mul hBA hX hX0 (by positivity)
    _ = (6 * D₀ + 3) / Real.sqrt K * T * h ^ 2 := by ring

/-- **The diagonal clause for the fixed window `φ_T` of `SelbergKey4.Window`** on `[T/2, 3T]`
(the window used for the off-diagonal clause), level 2 on `SKQFHyp θ ∧ DiagApproxHyp θ`. -/
theorem diagLag_bound_phiT {θ : ℝ} (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      lagInt (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (SelbergKey4.phiT T) (T / 2) (3 * T)
          (K / Real.log T) ≤ D / Real.sqrt K * T * (K / Real.log T) ^ 2 := by
  obtain ⟨D, hD0, hK⟩ := diagLag_bound_of_SKQF hS hD
  refine ⟨D, hD0, fun K hK1 => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hφ, hφ0, -, -, -⟩ := SelbergKey4.admissible_phiT (T := T) (by linarith)
  exact hT₀ T (le_trans (le_max_left _ _) hT) _ _ _ hφ hφ0 (fun t => SelbergKey4.Phi_le_one _)
    le_rfl (by linarith) le_rfl

end RamanujanTau.SelbergKeyDiag
