/-
# Karamata's Tauberian theorem (Laplace-transform / power-series form)

`karamata`: let `aₙ ≥ 0`, suppose `F(t) = ∑ aₙ e^{-nt}` converges for `t > 0` and
`t^ρ F(t) → K` as `t → 0⁺`, with `ρ ≥ 1`. Then `(∑_{n ≤ N} aₙ) / N^ρ → K / Γ(ρ+1)`.

Proof (Karamata 1931): put `S_t(f) = ∑ aₙ e^{-nt} f(e^{-nt})` and
`Λ(f) = Γ(ρ)⁻¹ ∫₀^∞ f(e^{-u}) e^{-u} u^{ρ-1} du`.
* For `f = x^m`, `t^ρ S_t(f) = t^ρ F((m+1)t) → K (m+1)^{-ρ} = K Λ(f)`; by linearity this holds
  for every polynomial.
* Weierstrass approximation (`exists_polynomial_near_of_continuousOn`) and positivity of `aₙ`
  give the same limit for every continuous `f`.
* Sandwiching the step function `g(x) = x⁻¹·1[x ≥ e⁻¹]` between continuous functions whose
  `Λ`-values differ by `≤ ε` gives it for `g`. At `t = 1/N`, `S_t(g) = ∑_{n ≤ N} aₙ` and
  `Λ(g) = 1/Γ(ρ+1)`.
-/
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal

open Real MeasureTheory Filter Topology Set Polynomial

/-! ### The limit functional `Λ` -/

/-- The Gamma weight `e^{-u} u^{ρ-1}`. -/
noncomputable def kw (ρ u : ℝ) : ℝ := Real.exp (-u) * u ^ (ρ - 1)

lemma kw_nonneg (ρ : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ kw ρ u := by
  unfold kw; positivity

lemma measurable_kw (ρ : ℝ) : Measurable (kw ρ) := by
  unfold kw; fun_prop

/-- Admissible test functions: measurable and bounded on `[0,1]`. -/
def Adm (f : ℝ → ℝ) : Prop := Measurable f ∧ ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B

lemma exp_neg_mem_Icc {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

lemma adm_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : Adm f := by
  refine ⟨hf.measurable, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

lemma adm_add {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g) : Adm (fun x => f x + g x) := by
  obtain ⟨hf1, B, hB⟩ := hf
  obtain ⟨hg1, B', hB'⟩ := hg
  exact ⟨hf1.add hg1, B + B', fun x hx => (abs_add_le _ _).trans (add_le_add (hB x hx) (hB' x hx))⟩

lemma integrableOn_adm {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℝ} (hf : Adm f) :
    IntegrableOn (fun u => f (Real.exp (-u)) * kw ρ u) (Ioi 0) := by
  obtain ⟨hm, B, hB⟩ := hf
  refine Integrable.mono' ((GammaIntegral_convergent hρ).const_mul B) ?_ ?_
  · exact ((hm.comp (Real.measurable_exp.comp measurable_neg)).mul
      (measurable_kw ρ)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hk := kw_nonneg ρ (le_of_lt hu)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hk]
    exact mul_le_mul_of_nonneg_right (hB _ (exp_neg_mem_Icc (le_of_lt hu))) hk

/-- `Λ(f) = Γ(ρ)⁻¹ ∫₀^∞ f(e^{-u}) e^{-u} u^{ρ-1} du`. -/
noncomputable def Lam (ρ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ u in Ioi 0, f (Real.exp (-u)) * kw ρ u) / Gamma ρ

lemma Lam_add {ρ : ℝ} (hρ : 0 < ρ) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g) :
    Lam ρ (fun x => f x + g x) = Lam ρ f + Lam ρ g := by
  unfold Lam
  simp only [add_mul]
  rw [integral_add (integrableOn_adm hρ hf) (integrableOn_adm hρ hg), add_div]

lemma Lam_smul (ρ c : ℝ) (f : ℝ → ℝ) : Lam ρ (fun x => c * f x) = c * Lam ρ f := by
  unfold Lam
  simp only [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

lemma Lam_mono {ρ : ℝ} (hρ : 0 < ρ) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ g x) : Lam ρ f ≤ Lam ρ g := by
  unfold Lam
  refine div_le_div_of_nonneg_right ?_ (Gamma_pos_of_pos hρ).le
  refine setIntegral_mono_on (integrableOn_adm hρ hf) (integrableOn_adm hρ hg) measurableSet_Ioi
    fun u hu => ?_
  exact mul_le_mul_of_nonneg_right (h _ (exp_neg_mem_Icc (le_of_lt hu)))
    (kw_nonneg ρ (le_of_lt hu))

lemma Lam_pow {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    Lam ρ (fun x => x ^ m) = (1 / ((m : ℝ) + 1)) ^ ρ := by
  unfold Lam
  have e : ∀ u : ℝ, Real.exp (-u) ^ m * kw ρ u = u ^ (ρ - 1) * Real.exp (-(((m : ℝ) + 1) * u)) := by
    intro u
    unfold kw
    rw [← Real.exp_nat_mul, show -(((m : ℝ) + 1) * u) = (m : ℝ) * -u + -u by ring, Real.exp_add]
    ring
  simp only [e]
  rw [integral_rpow_mul_exp_neg_mul_Ioi hρ (by positivity)]
  exact mul_div_cancel_right₀ _ (Gamma_pos_of_pos hρ).ne'

lemma Lam_const {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) : Lam ρ (fun _ => c) = c := by
  have h0 := Lam_pow hρ 0
  simp only [pow_zero, Nat.cast_zero, zero_add, div_one, one_rpow] at h0
  have h := Lam_smul ρ c (fun _ => 1)
  simp only [mul_one] at h
  rw [h, h0, mul_one]

/-! ### The sums `S_t(f)` -/

/-- Hypotheses of Karamata's theorem. -/
structure KarHyp (a : ℕ → ℝ) (ρ K : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ a n
  summ : ∀ t : ℝ, 0 < t → Summable (fun n : ℕ => a n * Real.exp (-(n * t)))
  lim : Tendsto (fun t => t ^ ρ * ∑' n : ℕ, a n * Real.exp (-(n * t))) (𝓝[>] 0) (𝓝 K)

/-- `S_t(f) = ∑ aₙ e^{-nt} f(e^{-nt})`. -/
noncomputable def S (a : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, a n * Real.exp (-(n * t)) * f (Real.exp (-(n * t)))

variable {a : ℕ → ℝ} {ρ K : ℝ}

lemma nt_nonneg {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 ≤ (n : ℝ) * t := by positivity

lemma summable_S (h : KarHyp a ρ K) {f : ℝ → ℝ} (hf : Adm f) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => a n * Real.exp (-(n * t)) * f (Real.exp (-(n * t)))) := by
  obtain ⟨-, B, hB⟩ := hf
  refine Summable.of_norm_bounded ((h.summ t ht).mul_left B) fun n => ?_
  have h0 : 0 ≤ a n * Real.exp (-(n * t)) := mul_nonneg (h.nonneg n) (Real.exp_pos _).le
  rw [norm_mul, Real.norm_of_nonneg h0, mul_comm B]
  exact mul_le_mul_of_nonneg_left (by
    rw [Real.norm_eq_abs]; exact hB _ (exp_neg_mem_Icc (nt_nonneg ht n))) h0

lemma S_add (h : KarHyp a ρ K) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g) {t : ℝ} (ht : 0 < t) :
    S a (fun x => f x + g x) t = S a f t + S a g t := by
  unfold S
  simp only [mul_add]
  exact (summable_S h hf ht).tsum_add (summable_S h hg ht)

lemma S_smul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : S a (fun x => c * f x) t = c * S a f t := by
  unfold S
  rw [← tsum_mul_left]
  congr 1; funext n; ring

lemma S_mono (h : KarHyp a ρ K) {f g : ℝ → ℝ} (hf : Adm f) (hg : Adm g)
    (hfg : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ g x) {t : ℝ} (ht : 0 < t) : S a f t ≤ S a g t := by
  unfold S
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_S h hf ht) (summable_S h hg ht)
  exact mul_le_mul_of_nonneg_left (hfg _ (exp_neg_mem_Icc (nt_nonneg ht n)))
    (mul_nonneg (h.nonneg n) (Real.exp_pos _).le)

/-- `t^ρ S_t(f) → K Λ(f)`. -/
def Conv (a : ℕ → ℝ) (ρ K : ℝ) (f : ℝ → ℝ) : Prop :=
  Tendsto (fun t => t ^ ρ * S a f t) (𝓝[>] 0) (𝓝 (K * Lam ρ f))

lemma K_nonneg (h : KarHyp a ρ K) : 0 ≤ K := by
  refine ge_of_tendsto h.lim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    (tsum_nonneg fun n => mul_nonneg (h.nonneg n) (Real.exp_pos _).le)

lemma tendsto_mul_left_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

lemma conv_pow (h : KarHyp a ρ K) (hρ : 0 < ρ) (m : ℕ) : Conv a ρ K (fun x => x ^ m) := by
  unfold Conv
  rw [Lam_pow hρ m]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlim := (h.lim.comp (tendsto_mul_left_nhdsGT hm)).const_mul ((1 / ((m : ℝ) + 1)) ^ ρ)
  rw [mul_comm K]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [Function.comp]
  have eS : S a (fun x => x ^ m) t = ∑' n : ℕ, a n * Real.exp (-(n * (((m : ℝ) + 1) * t))) := by
    unfold S
    congr 1; funext n
    rw [mul_assoc, ← pow_succ', ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  rw [eS, Real.mul_rpow hm.le ht0, ← mul_assoc, ← mul_assoc, ← Real.mul_rpow (by positivity) hm.le]
  rw [one_div_mul_cancel hm.ne', Real.one_rpow, one_mul]

lemma adm_poly (p : ℝ[X]) : Adm (fun x => p.eval x) := adm_of_continuous p.continuous

lemma conv_poly (h : KarHyp a ρ K) (hρ : 0 < ρ) (p : ℝ[X]) : Conv a ρ K (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    unfold Conv at *
    simp only [eval_add]
    rw [Lam_add hρ (adm_poly p) (adm_poly q), mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [S_add h (adm_poly p) (adm_poly q) ht, mul_add]
  | monomial m c =>
    unfold Conv
    simp only [eval_monomial]
    rw [Lam_smul, show K * (c * Lam ρ fun x => x ^ m) = c * (K * Lam ρ fun x => x ^ m) by ring]
    refine ((conv_pow h hρ m).const_mul c).congr' (Eventually.of_forall fun t => ?_)
    show c * (t ^ ρ * S a (fun x => x ^ m) t) = t ^ ρ * S a (fun x => c * x ^ m) t
    rw [S_smul]; ring

/-- **Sandwich step.** If `g` can be squeezed between functions for which `Conv` holds, with
`Λ`-values within `ε`, then `Conv` holds for `g`. -/
lemma conv_of_sandwich (h : KarHyp a ρ K) (hρ : 0 < ρ) {g : ℝ → ℝ} (hg : Adm g)
    (H : ∀ ε > 0, ∃ f₁ f₂ : ℝ → ℝ, Adm f₁ ∧ Adm f₂ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f₁ x ≤ g x ∧ g x ≤ f₂ x) ∧ Conv a ρ K f₁ ∧ Conv a ρ K f₂ ∧
      Lam ρ f₂ ≤ Lam ρ f₁ + ε) :
    Conv a ρ K g := by
  have hK := K_nonneg h
  unfold Conv
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
    filter_upwards [(tendsto_order.1 c1).1 b hb1, self_mem_nhdsWithin] with t ht1 ht
    exact ht1.trans_le (mul_le_mul_of_nonneg_left
      (S_mono h h1 hg (fun x hx => (hfg x hx).1) ht) (Real.rpow_nonneg (le_of_lt ht) _))
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
    filter_upwards [(tendsto_order.1 c2).2 b hb1, self_mem_nhdsWithin] with t ht1 ht
    exact (mul_le_mul_of_nonneg_left
      (S_mono h hg h2 (fun x hx => (hfg x hx).2) ht) (Real.rpow_nonneg (le_of_lt ht) _)).trans_lt ht1

/-- `Conv` for every continuous test function (Weierstrass). -/
lemma conv_of_continuous (h : KarHyp a ρ K) (hρ : 0 < ρ) {f : ℝ → ℝ} (hf : Continuous f) :
    Conv a ρ K f := by
  refine conv_of_sandwich h hρ (adm_of_continuous hf) fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf.continuousOn (ε / 2)
    (by positivity)
  refine ⟨fun x => (p - C (ε / 2)).eval x, fun x => (p + C (ε / 2)).eval x, adm_poly _,
    adm_poly _, fun x hx => ?_, conv_poly h hρ _, conv_poly h hρ _, ?_⟩
  · have := hp x hx
    simp only [eval_sub, eval_add, eval_C]
    constructor <;> linarith [abs_lt.1 this]
  · have e : (fun x => (p + C (ε / 2)).eval x) =
        fun x => (p - C (ε / 2)).eval x + (fun _ => ε) x := by
      funext x; simp only [eval_sub, eval_add, eval_C]; ring
    rw [e, Lam_add hρ (adm_poly _) (adm_of_continuous continuous_const), Lam_const hρ]

/-! ### The step function `g(x) = x⁻¹·1[x ≥ e⁻¹]` -/

/-- `g(x) = x⁻¹` for `x ≥ e⁻¹`, else `0`; `S_{1/N}(g) = ∑_{n ≤ N} aₙ`. -/
noncomputable def gK (x : ℝ) : ℝ := if Real.exp (-1) ≤ x then x⁻¹ else 0

lemma adm_gK : Adm gK := by
  refine ⟨Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_inv
    measurable_const, Real.exp 1, fun x _ => ?_⟩
  unfold gK
  split_ifs with h
  · have hx0 : 0 < x := (Real.exp_pos _).trans_le h
    rw [abs_of_pos (inv_pos.2 hx0)]
    calc x⁻¹ ≤ (Real.exp (-1))⁻¹ := inv_anti₀ (Real.exp_pos _) h
      _ = Real.exp 1 := by rw [Real.exp_neg, inv_inv]
  · simp only [abs_zero]; positivity

lemma Lam_gK {ρ : ℝ} (hρ : 0 < ρ) : Lam ρ gK = 1 / Gamma (ρ + 1) := by
  unfold Lam
  have e : ∫ u in Ioi (0 : ℝ), gK (Real.exp (-u)) * kw ρ u =
      ∫ u in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator (fun u => u ^ (ρ - 1)) u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold gK kw
    by_cases h1 : u ≤ 1
    · rw [if_pos (Real.exp_le_exp.2 (by linarith)), indicator_of_mem (show u ∈ Iic 1 from h1),
        ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
    · rw [if_neg (fun h => h1 (by have := Real.exp_le_exp.1 h; linarith)),
        indicator_of_notMem (show u ∉ Iic 1 from h1), zero_mul]
  rw [e, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    sub_add_cancel, Real.one_rpow, Real.zero_rpow hρ.ne', sub_zero, Real.Gamma_add_one hρ.ne']
  have := Gamma_pos_of_pos hρ
  field_simp

/-- `ramp α δ x = clamp((x-α)/δ, 0, 1)`. -/
noncomputable def ramp (α δ x : ℝ) : ℝ := max 0 (min ((x - α) / δ) 1)

/-- `hcut c x = 1 / max(x, c/2)`. -/
noncomputable def hcut (c x : ℝ) : ℝ := (max x (c / 2))⁻¹

lemma continuous_ramp (α δ : ℝ) : Continuous (ramp α δ) := by
  unfold ramp; fun_prop

lemma continuous_hcut {c : ℝ} (hc : 0 < c) : Continuous (hcut c) :=
  (continuous_id.max continuous_const).inv₀ fun x =>
    (lt_max_of_lt_right (by linarith : (0 : ℝ) < c / 2)).ne'

lemma ramp_nonneg (α δ x : ℝ) : 0 ≤ ramp α δ x := le_max_left _ _

lemma ramp_le_one (α δ x : ℝ) : ramp α δ x ≤ 1 := max_le zero_le_one (min_le_right _ _)

lemma ramp_eq_zero {α δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ α) : ramp α δ x = 0 :=
  max_eq_left (min_le_of_left_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

lemma ramp_eq_one {α δ x : ℝ} (hδ : 0 < δ) (hx : α + δ ≤ x) : ramp α δ x = 1 := by
  unfold ramp
  rw [min_eq_right (by rw [le_div_iff₀ hδ]; linarith), max_eq_right zero_le_one]

lemma hcut_pos {c : ℝ} (hc : 0 < c) (x : ℝ) : 0 < hcut c x :=
  inv_pos.2 (lt_max_of_lt_right (by linarith))

lemma hcut_le {c : ℝ} (hc : 0 < c) (x : ℝ) : hcut c x ≤ 2 / c := by
  unfold hcut
  calc (max x (c / 2))⁻¹ ≤ (c / 2)⁻¹ := inv_anti₀ (by linarith) (le_max_right _ _)
    _ = 2 / c := by rw [inv_div]

lemma hcut_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) : hcut c x = x⁻¹ := by
  unfold hcut; rw [max_eq_left (by linarith)]

/-- The `Λ`-mass of a short interval around `c = e⁻¹`. -/
lemma Lam_bump_le {ρ : ℝ} (hρ : 1 ≤ ρ) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ Real.exp (-1) / 2) :
    Lam ρ (fun x => 2 / Real.exp (-1) *
      (Icc (Real.exp (-1) - δ) (Real.exp (-1) + δ)).indicator (fun _ => (1 : ℝ)) x) ≤
      δ * (8 * 2 ^ (ρ - 1) / (Real.exp (-1) ^ 2 * Gamma ρ)) := by
  set c := Real.exp (-1) with hcdef
  have hc : 0 < c := Real.exp_pos _
  have hρ0 : 0 < ρ := by linarith
  have hΓ := Gamma_pos_of_pos hρ0
  set A := -Real.log (c + δ)
  set B := -Real.log (c - δ)
  set M : ℝ := 2 / c * 2 ^ (ρ - 1)
  have hcδ : 0 < c - δ := by linarith
  have hB2 : B ≤ 2 := by
    have h1 : Real.log (c / 2) ≤ Real.log (c - δ) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hc.ne' two_ne_zero, hcdef, Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    simp only [B]; linarith
  have hAB : B - A ≤ 4 * δ / c := by
    have h1 : B - A = Real.log ((c + δ) / (c - δ)) := by
      rw [Real.log_div (by linarith) hcδ.ne']; simp only [A, B]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (c + δ) / (c - δ) by positivity)
    have h3 : (c + δ) / (c - δ) - 1 ≤ 4 * δ / c := by
      rw [div_sub_one hcδ.ne', div_le_div_iff₀ hcδ hc]; nlinarith
    linarith
  have hM : 0 ≤ M := by positivity
  have hadm : Adm (fun x => 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x) := by
    refine ⟨(measurable_const.indicator measurableSet_Icc).const_mul _, 2 / c, fun x _ => ?_⟩
    rw [abs_of_nonneg (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) x))]
    calc 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x ≤ 2 / c * 1 := by
          gcongr; exact indicator_le_self' (fun _ _ => zero_le_one) x
      _ = 2 / c := mul_one _
  have hint : Integrable ((Icc A B).indicator (fun _ => M)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) (Real.exp (-u)) * kw ρ u ≤
        (Icc A B).indicator (fun _ => M) u := by
    intro u hu
    have hu0 : 0 < u := hu
    by_cases hmem : Real.exp (-u) ∈ Icc (c - δ) (c + δ)
    · have hA : A ≤ u := by
        have := Real.log_le_log (Real.exp_pos _) hmem.2
        rw [Real.log_exp] at this; simp only [A]; linarith
      have hBu : u ≤ B := by
        have := Real.log_le_log hcδ hmem.1
        rw [Real.log_exp] at this; simp only [B]; linarith
      rw [indicator_of_mem hmem, indicator_of_mem (show u ∈ Icc A B from ⟨hA, hBu⟩), mul_one]
      have hkw : kw ρ u ≤ 2 ^ (ρ - 1) := by
        unfold kw
        have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have h2 : u ^ (ρ - 1) ≤ 2 ^ (ρ - 1) :=
          Real.rpow_le_rpow hu0.le (hBu.trans hB2) (by linarith)
        calc Real.exp (-u) * u ^ (ρ - 1) ≤ 1 * 2 ^ (ρ - 1) :=
              mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = _ := one_mul _
      simp only [M]; gcongr
    · rw [indicator_of_notMem hmem, mul_zero, zero_mul]
      exact indicator_nonneg (fun _ _ => hM) u
  unfold Lam
  rw [div_le_iff₀ hΓ]
  calc ∫ u in Ioi 0, 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) (Real.exp (-u)) *
        kw ρ u
      ≤ ∫ u in Ioi 0, (Icc A B).indicator (fun _ => M) u :=
        setIntegral_mono_on (integrableOn_adm hρ0 hadm) hint.integrableOn measurableSet_Ioi hpt
    _ ≤ ∫ u, (Icc A B).indicator (fun _ => M) u :=
        setIntegral_le_integral hint (Eventually.of_forall fun u => indicator_nonneg
          (fun _ _ => hM) u)
    _ = (B - A) * M := by
        rw [integral_indicator_const M measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
        have : 0 ≤ B - A := by
          simp only [A, B]
          linarith [Real.log_le_log hcδ (show c - δ ≤ c + δ by linarith)]
        rw [max_eq_left this]
    _ ≤ 4 * δ / c * M := mul_le_mul_of_nonneg_right hAB hM
    _ = δ * (8 * 2 ^ (ρ - 1) / (c ^ 2 * Gamma ρ)) * Gamma ρ := by
        simp only [M]; field_simp; ring

/-- `Conv` for the step function. -/
lemma conv_gK (h : KarHyp a ρ K) (hρ : 1 ≤ ρ) : Conv a ρ K gK := by
  have hρ0 : 0 < ρ := by linarith
  set c := Real.exp (-1) with hcdef
  have hc : 0 < c := Real.exp_pos _
  set Q : ℝ := 8 * 2 ^ (ρ - 1) / (c ^ 2 * Gamma ρ)
  have hQ : 0 < Q := by have := Gamma_pos_of_pos hρ0; positivity
  refine conv_of_sandwich h hρ0 adm_gK fun ε hε => ?_
  set δ := min (c / 2) (ε / Q)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδc : δ ≤ c / 2 := min_le_left _ _
  have hδQ : δ * Q ≤ ε := by
    have := min_le_right (c / 2) (ε / Q)
    calc δ * Q ≤ ε / Q * Q := mul_le_mul_of_nonneg_right this hQ.le
      _ = ε := div_mul_cancel₀ _ hQ.ne'
  have hc1 : Continuous fun x => ramp c δ x * hcut c x :=
    (continuous_ramp _ _).mul (continuous_hcut hc)
  have hc2 : Continuous fun x => ramp (c - δ) δ x * hcut c x :=
    (continuous_ramp _ _).mul (continuous_hcut hc)
  set D := fun x => 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x
  have hDadm : Adm D := by
    refine ⟨(measurable_const.indicator measurableSet_Icc).const_mul _, 2 / c, fun x _ => ?_⟩
    simp only [D]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) x))]
    calc 2 / c * (Icc (c - δ) (c + δ)).indicator (fun _ => (1 : ℝ)) x ≤ 2 / c * 1 := by
          gcongr; exact indicator_le_self' (fun _ _ => zero_le_one) x
      _ = 2 / c := mul_one _
  refine ⟨_, _, adm_of_continuous hc1, adm_of_continuous hc2, fun x _ => ⟨?_, ?_⟩,
    conv_of_continuous h hρ0 hc1, conv_of_continuous h hρ0 hc2, ?_⟩
  · unfold gK
    split_ifs with hx
    · rw [hcut_eq hc hx]
      have : 0 < x⁻¹ := inv_pos.2 (hc.trans_le hx)
      calc ramp c δ x * x⁻¹ ≤ 1 * x⁻¹ := mul_le_mul_of_nonneg_right (ramp_le_one _ _ _) this.le
        _ = x⁻¹ := one_mul _
    · rw [ramp_eq_zero hδ (by linarith), zero_mul]
  · unfold gK
    split_ifs with hx
    · rw [hcut_eq hc hx, ramp_eq_one hδ (by linarith), one_mul]
    · exact mul_nonneg (ramp_nonneg _ _ _) (hcut_pos hc x).le
  · have hle : ∀ x ∈ Icc (0 : ℝ) 1, ramp (c - δ) δ x * hcut c x ≤
        ramp c δ x * hcut c x + D x := by
      intro x _
      have h1 : 0 ≤ ramp c δ x * hcut c x := mul_nonneg (ramp_nonneg _ _ _) (hcut_pos hc x).le
      by_cases hmem : x ∈ Icc (c - δ) (c + δ)
      · simp only [D]
        rw [indicator_of_mem hmem, mul_one]
        have : ramp (c - δ) δ x * hcut c x ≤ 2 / c :=
          calc ramp (c - δ) δ x * hcut c x ≤ 1 * hcut c x :=
                mul_le_mul_of_nonneg_right (ramp_le_one _ _ _) (hcut_pos hc x).le
            _ ≤ 2 / c := by rw [one_mul]; exact hcut_le hc x
        linarith
      · simp only [D]
        rw [indicator_of_notMem hmem, mul_zero, add_zero]
        rcases not_and_or.1 hmem with h' | h'
        · rw [ramp_eq_zero hδ (by linarith), zero_mul]; exact h1
        · rw [ramp_eq_one hδ (by linarith), ramp_eq_one hδ (by linarith)]
    have := Lam_mono hρ0 (adm_of_continuous hc2)
      (adm_add (adm_of_continuous hc1) hDadm) hle
    rw [Lam_add hρ0 (adm_of_continuous hc1) hDadm] at this
    have hb := Lam_bump_le hρ hδ hδc
    linarith

/-- **Karamata's Tauberian theorem.** If `aₙ ≥ 0`, `∑ aₙ e^{-nt}` converges for `t > 0`, and
`t^ρ ∑ aₙ e^{-nt} → K` as `t → 0⁺` (`ρ ≥ 1`), then `(∑_{n ≤ N} aₙ)/N^ρ → K/Γ(ρ+1)`. -/
theorem karamata (h : KarHyp a ρ K) (hρ : 1 ≤ ρ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), a n) / (N : ℝ) ^ ρ) atTop
      (𝓝 (K / Gamma (ρ + 1))) := by
  have hρ0 : 0 < ρ := by linarith
  have hc := conv_gK h hρ
  unfold Conv at hc
  rw [Lam_gK hρ0, mul_one_div] at hc
  have ht : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact one_div_pos.2 this
  refine (hc.comp ht).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp]
  have hS : S a gK (1 / (N : ℝ)) = ∑ n ∈ Finset.range (N + 1), a n := by
    unfold S
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
      unfold gK
      rw [if_pos (Real.exp_le_exp.2 (by
        rw [neg_le_neg_iff, mul_one_div, div_le_one hN0]; exact hnN)), mul_assoc,
        mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
    · intro n hn
      have hnN : (N : ℝ) < n := by
        exact_mod_cast (show N < n by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn)
      unfold gK
      rw [if_neg (fun hle => by
        have := Real.exp_le_exp.1 hle
        rw [neg_le_neg_iff, mul_one_div, div_le_one hN0] at this; linarith), mul_zero]
  rw [hS, one_div, Real.inv_rpow hN0.le, inv_mul_eq_div]

end RamanujanTau.EisensteinReal
