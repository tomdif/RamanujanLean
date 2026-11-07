/-
# Karamata's Tauberian theorem for Laplace transforms with a logarithmic factor

Continuous analogue of `EisensteinReal.karamata`, with the slowly varying factor `log(1/t)`:
let `m ≥ 0` on `(0,∞)` with `F(t) = ∫_0^∞ m(x) e^{-xt} dx` finite for `t > 0` and

    t^ρ F(t) / log(1/t) → K          (t → 0⁺).

Put `S_t(f) = ∫_0^∞ m(x) e^{-xt} f(e^{-xt}) dx`.  Then `t^ρ S_t(f)/log(1/t) → K Λ(f)` with
the same limit functional `Λ` (`EisensteinReal.Lam`) as in the discrete case:

* for `f = x^j`: `S_t(f) = F((j+1)t)` and `log(1/((j+1)t)) / log(1/t) → 1`;
* polynomials by linearity, continuous `f` by Weierstrass, and the step function
  `gK(x)·Q(x)` (`gK = x⁻¹·1[x ≥ e⁻¹]`, `Q` continuous, `0 ≤ Q ≤ B`) by the same ramp sandwich
  as `EisensteinReal.conv_gK`.
-/
import RamanujanTau.EisensteinReal.Karamata

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Real MeasureTheory Filter Topology Set Polynomial
open RamanujanTau.EisensteinReal (Adm Lam kw adm_of_continuous adm_add Lam_add Lam_smul Lam_mono
  Lam_pow Lam_const exp_neg_mem_Icc gK adm_gK ramp hcut continuous_ramp continuous_hcut
  ramp_nonneg ramp_le_one ramp_eq_zero ramp_eq_one hcut_pos hcut_le hcut_eq Lam_bump_le adm_poly
  tendsto_mul_left_nhdsGT)

/-- Hypotheses of the continuous Karamata theorem with a `log` factor. -/
structure KarHypC (m : ℝ → ℝ) (ρ K : ℝ) : Prop where
  nonneg : ∀ x, 0 < x → 0 ≤ m x
  integ : ∀ t : ℝ, 0 < t → IntegrableOn (fun x => m x * Real.exp (-(x * t))) (Ioi 0)
  lim : Tendsto (fun t => t ^ ρ / Real.log (1 / t) *
    ∫ x in Ioi 0, m x * Real.exp (-(x * t))) (𝓝[>] 0) (𝓝 K)

/-- `S_t(f) = ∫_0^∞ m(x) e^{-xt} f(e^{-xt}) dx`. -/
noncomputable def SC (m f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioi 0, m x * Real.exp (-(x * t)) * f (Real.exp (-(x * t)))

variable {m : ℝ → ℝ} {ρ K : ℝ}

lemma integrableOn_SC (h : KarHypC m ρ K) {f : ℝ → ℝ} (hf : Adm f) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => m x * Real.exp (-(x * t)) * f (Real.exp (-(x * t)))) (Ioi 0) := by
  obtain ⟨hfm, B, hB⟩ := hf
  refine Integrable.mono' ((h.integ t ht).const_mul B) ?_ ?_
  · exact (h.integ t ht).aestronglyMeasurable.mul
      ((hfm.comp (by fun_prop : Measurable fun x : ℝ => Real.exp (-(x * t)))).aestronglyMeasurable)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have h0 : 0 ≤ m x * Real.exp (-(x * t)) := mul_nonneg (h.nonneg x hx) (Real.exp_pos _).le
    rw [norm_mul, Real.norm_of_nonneg h0, mul_comm B]
    exact mul_le_mul_of_nonneg_left (by
      rw [Real.norm_eq_abs]
      exact hB _ (exp_neg_mem_Icc (mul_nonneg (le_of_lt hx) ht.le))) h0

lemma SC_add (h : KarHypC m ρ K) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g) {t : ℝ} (ht : 0 < t) :
    SC m (fun x => f x + g x) t = SC m f t + SC m g t := by
  unfold SC
  simp only [mul_add]
  exact integral_add (integrableOn_SC h hf ht) (integrableOn_SC h hg ht)

lemma SC_smul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : SC m (fun x => c * f x) t = c * SC m f t := by
  unfold SC
  rw [← integral_const_mul]
  congr 1; funext x; ring

lemma SC_mono (h : KarHypC m ρ K) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g)
    (hfg : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ g x) {t : ℝ} (ht : 0 < t) : SC m f t ≤ SC m g t := by
  unfold SC
  refine setIntegral_mono_on (integrableOn_SC h hf ht) (integrableOn_SC h hg ht)
    measurableSet_Ioi fun x hx => ?_
  exact mul_le_mul_of_nonneg_left (hfg _ (exp_neg_mem_Icc (mul_nonneg (le_of_lt hx) ht.le)))
    (mul_nonneg (h.nonneg x hx) (Real.exp_pos _).le)

/-- `t^ρ S_t(f)/log(1/t) → K Λ(f)`. -/
def ConvC (m : ℝ → ℝ) (ρ K : ℝ) (f : ℝ → ℝ) : Prop :=
  Tendsto (fun t => t ^ ρ / Real.log (1 / t) * SC m f t) (𝓝[>] 0) (𝓝 (K * Lam ρ f))

lemma nrm_nonneg {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 ≤ t ^ ρ / Real.log (1 / t) :=
  div_nonneg (Real.rpow_nonneg ht.le _)
    (Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith))

lemma KC_nonneg (h : KarHypC m ρ K) : 0 ≤ K := by
  refine ge_of_tendsto h.lim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact mul_nonneg (nrm_nonneg ht.1 ht.2)
    (setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (h.nonneg x hx) (Real.exp_pos _).le)

lemma tendsto_log_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t => Real.log (1 / (c * t)) / Real.log (1 / t)) (𝓝[>] 0) (𝓝 1) := by
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun t => ?_
    simp [one_div]
  have h1 : Tendsto (fun t => 1 - Real.log c * (Real.log (1 / t))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have := (hL.inv_tendsto_atTop.const_mul (Real.log c)).const_sub 1
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hL.eventually_gt_atTop 0] with t ht hLt
  have ht0 : 0 < t := ht
  rw [one_div (c * t), Real.log_inv, Real.log_mul hc.ne' ht0.ne', one_div t, Real.log_inv] at *
  have hlt : Real.log t ≠ 0 := (by linarith : Real.log t < 0).ne
  field_simp
  ring

lemma convC_pow (h : KarHypC m ρ K) (hρ : 0 < ρ) (j : ℕ) : ConvC m ρ K (fun x => x ^ j) := by
  unfold ConvC
  rw [Lam_pow hρ j]
  have hm : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hlim := ((h.lim.comp (tendsto_mul_left_nhdsGT hm)).const_mul
    ((1 / ((j : ℝ) + 1)) ^ ρ)).mul (tendsto_log_ratio hm)
  rw [mul_one] at hlim
  rw [mul_comm K]
  refine hlim.congr' ?_
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ((j : ℝ) + 1) * t < 1 := by
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT this] with t ht
    refine ⟨ht.1, ?_⟩
    have := ht.2
    rw [lt_div_iff₀ hm] at this; linarith
  filter_upwards [hev] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have ht1' : t < 1 := by
    have : t ≤ ((j : ℝ) + 1) * t := by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  have hL1 : 0 < Real.log (1 / t) := Real.log_pos (by rw [lt_div_iff₀ ht0]; linarith)
  have hL2 : 0 < Real.log (1 / (((j : ℝ) + 1) * t)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
  simp only [Function.comp]
  have eS : SC m (fun x => x ^ j) t = ∫ x in Ioi 0, m x * Real.exp (-(x * (((j : ℝ) + 1) * t))) := by
    unfold SC
    congr 1; funext x
    rw [mul_assoc, ← pow_succ', ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  rw [eS, Real.mul_rpow hm.le ht0.le, Real.div_rpow zero_le_one hm.le, Real.one_rpow]
  have hpow : 0 < ((j : ℝ) + 1) ^ ρ := Real.rpow_pos_of_pos hm ρ
  field_simp

lemma convC_poly (h : KarHypC m ρ K) (hρ : 0 < ρ) (p : ℝ[X]) :
    ConvC m ρ K (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    unfold ConvC at *
    simp only [eval_add]
    rw [Lam_add hρ (adm_poly p) (adm_poly q), mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [SC_add h (adm_poly p) (adm_poly q) ht, mul_add]
  | monomial j c =>
    unfold ConvC
    simp only [eval_monomial]
    rw [Lam_smul, show K * (c * Lam ρ fun x => x ^ j) = c * (K * Lam ρ fun x => x ^ j) by ring]
    refine ((convC_pow h hρ j).const_mul c).congr' (Eventually.of_forall fun t => ?_)
    show c * (t ^ ρ / Real.log (1 / t) * SC m (fun x => x ^ j) t) =
      t ^ ρ / Real.log (1 / t) * SC m (fun x => c * x ^ j) t
    rw [SC_smul]; ring

/-- **Sandwich step.** -/
lemma convC_of_sandwich (h : KarHypC m ρ K) (hρ : 0 < ρ) {g : ℝ → ℝ} (hg : Adm g)
    (H : ∀ ε > 0, ∃ f₁ f₂ : ℝ → ℝ, Adm f₁ ∧ Adm f₂ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f₁ x ≤ g x ∧ g x ≤ f₂ x) ∧ ConvC m ρ K f₁ ∧ ConvC m ρ K f₂ ∧
      Lam ρ f₂ ≤ Lam ρ f₁ + ε) :
    ConvC m ρ K g := by
  have hK := KC_nonneg h
  unfold ConvC
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · set D := K * Lam ρ g - b
    have hD : 0 < D := by simp only [D]; linarith
    obtain ⟨f₁, f₂, h1, h2, hfg, c1, -, hε⟩ := H (D / (K + 1)) (by positivity)
    have hl : Lam ρ g ≤ Lam ρ f₂ := Lam_mono hρ hg h2 fun x hx => (hfg x hx).2
    have hKe : K * (D / (K + 1)) < D := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    have hb1 : b < K * Lam ρ f₁ := by
      have : K * Lam ρ g ≤ K * Lam ρ f₁ + K * (D / (K + 1)) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hl.trans hε) hK
      simp only [D] at hKe; linarith
    filter_upwards [(tendsto_order.1 c1).1 b hb1,
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht1 ht
    exact ht1.trans_le (mul_le_mul_of_nonneg_left
      (SC_mono h h1 hg (fun x hx => (hfg x hx).1) ht.1) (nrm_nonneg ht.1 ht.2))
  · set D := b - K * Lam ρ g
    have hD : 0 < D := by simp only [D]; linarith
    obtain ⟨f₁, f₂, h1, h2, hfg, -, c2, hε⟩ := H (D / (K + 1)) (by positivity)
    have hl : Lam ρ f₁ ≤ Lam ρ g := Lam_mono hρ h1 hg fun x hx => (hfg x hx).1
    have hKe : K * (D / (K + 1)) < D := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    have hb1 : K * Lam ρ f₂ < b := by
      have : K * Lam ρ f₂ ≤ K * Lam ρ g + K * (D / (K + 1)) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hε.trans (by linarith)) hK
      simp only [D] at hKe; linarith
    filter_upwards [(tendsto_order.1 c2).2 b hb1,
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht1 ht
    exact (mul_le_mul_of_nonneg_left
      (SC_mono h hg h2 (fun x hx => (hfg x hx).2) ht.1) (nrm_nonneg ht.1 ht.2)).trans_lt ht1

/-- `ConvC` for every continuous test function (Weierstrass). -/
lemma convC_of_continuous (h : KarHypC m ρ K) (hρ : 0 < ρ) {f : ℝ → ℝ} (hf : Continuous f) :
    ConvC m ρ K f := by
  refine convC_of_sandwich h hρ (adm_of_continuous hf) fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf.continuousOn (ε / 2)
    (by positivity)
  refine ⟨fun x => (p - C (ε / 2)).eval x, fun x => (p + C (ε / 2)).eval x, adm_poly _,
    adm_poly _, fun x hx => ?_, convC_poly h hρ _, convC_poly h hρ _, ?_⟩
  · have := hp x hx
    simp only [eval_sub, eval_add, eval_C]
    constructor <;> linarith [abs_lt.1 this]
  · have e : (fun x => (p + C (ε / 2)).eval x) =
        fun x => (p - C (ε / 2)).eval x + (fun _ => ε) x := by
      funext x; simp only [eval_sub, eval_add, eval_C]; ring
    rw [e, Lam_add hρ (adm_poly _) (adm_of_continuous continuous_const), Lam_const hρ]

/-- `ConvC` for the weighted step function `gK·Q`. -/
lemma convC_gKQ (h : KarHypC m ρ K) (hρ : 1 ≤ ρ) {Q : ℝ → ℝ} (hQc : Continuous Q) {BQ : ℝ}
    (hQ0 : ∀ x, 0 ≤ Q x) (hQB : ∀ x, Q x ≤ BQ) : ConvC m ρ K (fun x => gK x * Q x) := by
  have hρ0 : 0 < ρ := by linarith
  set c := Real.exp (-1) with hcdef
  have hc : 0 < c := Real.exp_pos _
  have hBQ : 0 ≤ BQ := (hQ0 0).trans (hQB 0)
  set Qc : ℝ := 8 * 2 ^ (ρ - 1) / (c ^ 2 * Gamma ρ)
  have hQc0 : 0 < Qc := by have := Gamma_pos_of_pos hρ0; positivity
  have hadmg : Adm (fun x => gK x * Q x) := by
    obtain ⟨hm1, B, hB⟩ := adm_gK
    refine ⟨hm1.mul hQc.measurable, B * BQ, fun x hx => ?_⟩
    rw [abs_mul, abs_of_nonneg (hQ0 x)]
    exact mul_le_mul (hB x hx) (hQB x) (hQ0 x) ((abs_nonneg _).trans (hB x hx))
  refine convC_of_sandwich h hρ0 hadmg fun ε hε => ?_
  set δ := min (c / 2) (ε / (Qc * (BQ + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδc : δ ≤ c / 2 := min_le_left _ _
  have hδQ : δ * Qc * BQ ≤ ε := by
    have := min_le_right (c / 2) (ε / (Qc * (BQ + 1)))
    have h1 : δ * (Qc * (BQ + 1)) ≤ ε := by
      calc δ * (Qc * (BQ + 1)) ≤ ε / (Qc * (BQ + 1)) * (Qc * (BQ + 1)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hc1 : Continuous fun x => ramp c δ x * hcut c x * Q x :=
    ((continuous_ramp _ _).mul (continuous_hcut hc)).mul hQc
  have hc2 : Continuous fun x => ramp (c - δ) δ x * hcut c x * Q x :=
    ((continuous_ramp _ _).mul (continuous_hcut hc)).mul hQc
  set D := fun x => 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x
  have hDadm : Adm D := by
    refine ⟨(measurable_const.indicator measurableSet_Icc).const_mul _, 2 / c, fun x _ => ?_⟩
    simp only [D]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) x))]
    calc 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x ≤ 2 / c * 1 := by
          gcongr; exact indicator_le_self' (fun _ _ => zero_le_one) x
      _ = 2 / c := mul_one _
  have hBDadm : Adm (fun x => BQ * D x) := by
    obtain ⟨hm1, B, hB⟩ := hDadm
    refine ⟨hm1.const_mul _, BQ * B, fun x hx => ?_⟩
    rw [abs_mul, abs_of_nonneg hBQ]
    exact mul_le_mul_of_nonneg_left (hB x hx) hBQ
  refine ⟨_, _, adm_of_continuous hc1, adm_of_continuous hc2, fun x _ => ⟨?_, ?_⟩,
    convC_of_continuous h hρ0 hc1, convC_of_continuous h hρ0 hc2, ?_⟩
  · unfold gK
    split_ifs with hx
    · rw [hcut_eq hc hx]
      have : 0 ≤ x⁻¹ * Q x := mul_nonneg (inv_pos.2 (hc.trans_le hx)).le (hQ0 x)
      calc ramp c δ x * x⁻¹ * Q x = ramp c δ x * (x⁻¹ * Q x) := by ring
        _ ≤ 1 * (x⁻¹ * Q x) := mul_le_mul_of_nonneg_right (ramp_le_one _ _ _) this
        _ = x⁻¹ * Q x := one_mul _
    · rw [ramp_eq_zero hδ (by linarith)]; simp
  · unfold gK
    split_ifs with hx
    · rw [hcut_eq hc hx, ramp_eq_one hδ (by linarith), one_mul]
    · rw [zero_mul]
      exact mul_nonneg (mul_nonneg (ramp_nonneg _ _ _) (hcut_pos hc x).le) (hQ0 x)
  · have hle : ∀ x ∈ Icc (0 : ℝ) 1, ramp (c - δ) δ x * hcut c x * Q x ≤
        ramp c δ x * hcut c x * Q x + BQ * D x := by
      intro x _
      have h1 : 0 ≤ ramp c δ x * hcut c x * Q x :=
        mul_nonneg (mul_nonneg (ramp_nonneg _ _ _) (hcut_pos hc x).le) (hQ0 x)
      by_cases hmem : x ∈ Icc (c - δ) (c + δ)
      · simp only [D]
        rw [indicator_of_mem hmem, mul_one]
        have : ramp (c - δ) δ x * hcut c x * Q x ≤ BQ * (2 / c) :=
          calc ramp (c - δ) δ x * hcut c x * Q x ≤ 1 * (2 / c) * BQ := by
                apply mul_le_mul _ (hQB x) (hQ0 x) (by positivity)
                exact mul_le_mul (ramp_le_one _ _ _) (hcut_le hc x) (hcut_pos hc x).le zero_le_one
            _ = BQ * (2 / c) := by ring
        linarith
      · simp only [D]
        rw [indicator_of_notMem hmem, mul_zero, mul_zero, add_zero]
        rcases not_and_or.1 hmem with h' | h'
        · rw [ramp_eq_zero hδ (by linarith), zero_mul, zero_mul]; exact h1
        · rw [ramp_eq_one hδ (by linarith), ramp_eq_one hδ (by linarith)]
    have := Lam_mono hρ0 (adm_of_continuous hc2)
      (adm_add (adm_of_continuous hc1) hBDadm) hle
    rw [Lam_add hρ0 (adm_of_continuous hc1) hBDadm, Lam_smul] at this
    have hb := Lam_bump_le hρ hδ hδc
    have hb' : BQ * Lam ρ D ≤ BQ * (δ * Qc) := mul_le_mul_of_nonneg_left hb hBQ
    nlinarith

end RamanujanTau.CriticalMeanSquareAsymp
