/-
# The Gaussian integral of `1/|1 − e^{v₀+βx}|`: the non-uniform denominator bound

`bad_integral_le`: for `P > 0`, `β ≠ 0`, `0 < η ≤ 1` and `|1 − e^{v₀+βx}| ≥ m > 0` on `ℝ`,

  `∫ e^{−P(x−x₀)²}/|1 − e^{v₀+βx}| dx ≤ (3/η)√(π/P) + (1/m)(2η/|β|)(1 + 16|β|²/(π²P))`.

Off the *bad set* `{x : |v₀+βx − 2πik| < η for some k}` the denominator is `≥ η/3` (`norm_one_sub_exp_ge`);
on it, only the uniform bound `m` is used, but the bad set is small:
* if `|Im β| ≤ |Re β|` it lies in one interval of length `2η/|β|` (only one pole is close to the line);
* otherwise it lies in a union of intervals of length `2η/|β|` centred on an arithmetic progression of
  spacing `s = 2π Im β/|β|²`, `|s| ≥ 4η/|β|`, whose Gaussian mass is `≤ (2η/|β|)(1 + 32/(Ps²))`
  (`gauss_union_le`).

`opt_eta`: `min_{0<η≤1} (a/η + bη) ≤ 2a + 2√(ab)`.
-/
import RamanujanTau.MockCusp.Kernel
import RamanujanTau.MockCusp.Denom

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal

noncomputable section

/-! ### the two-sided geometric series -/

lemma hasSum_exp_abs {c : ℝ} (hc : 0 < c) :
    HasSum (fun j : ℤ => Real.exp (-c * |(j : ℝ)|))
      ((1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := hasSum_geometric_of_lt_one hr0 hr1
  have e : ∀ n : ℕ, Real.exp (-c) ^ n = Real.exp (-c * n) := fun n => by
    rw [← Real.exp_nat_mul]; congr 1; ring
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · refine hg.congr_fun fun n => ?_
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), e]
  · refine (hg.mul_left (Real.exp (-c))).congr_fun fun n => ?_
    push_cast
    rw [abs_of_nonpos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]), e, ← Real.exp_add]
    congr 1; ring

lemma tsum_exp_abs_le {c : ℝ} (hc : 0 < c) :
    ∑' j : ℤ, Real.exp (-c * |(j : ℝ)|) ≤ 1 + 2 / c := by
  rw [(hasSum_exp_abs hc).tsum_eq]
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-c) := by linarith
  have hec : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
  have hinv : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
  have hE : 0 < Real.exp c := Real.exp_pos c
  rw [hinv] at hpos ⊢
  rw [show (1 - (Real.exp c)⁻¹)⁻¹ + (Real.exp c)⁻¹ * (1 - (Real.exp c)⁻¹)⁻¹ =
      (Real.exp c + 1) / (Real.exp c - 1) by
    have : Real.exp c - 1 ≠ 0 := by linarith
    field_simp]
  have h1 : 0 < Real.exp c - 1 := by linarith
  rw [div_le_iff₀ h1]
  have : 2 / c * (Real.exp c - 1) ≥ 2 := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  nlinarith

/-! ### Gaussian mass of a union of intervals centred on an arithmetic progression -/

lemma gauss_pt_le {P s ℓ τ₀ x0 x : ℝ} (hP : 0 < P) (hs : s ≠ 0) (hℓ : 4 * ℓ ≤ |s|) (k : ℤ)
    (hx : x ∈ Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ)) :
    Real.exp (-P * (x - x0) ^ 2) ≤
      Real.exp (-(P * s ^ 2 / 16) * |((k - round ((x0 - τ₀) / s) : ℤ) : ℝ)|) := by
  set k₁ := round ((x0 - τ₀) / s)
  set j : ℤ := k - k₁
  have hsp : 0 < |s| := abs_pos.mpr hs
  have hr := abs_sub_round ((x0 - τ₀) / s)
  have hu : |x0 - τ₀ - k₁ * s| ≤ |s| / 2 := by
    have : x0 - τ₀ - k₁ * s = s * ((x0 - τ₀) / s - k₁) := by field_simp
    rw [this, abs_mul]; nlinarith [abs_nonneg ((x0 - τ₀) / s - k₁)]
  have hxk : |x - τ₀ - k * s| ≤ |s| / 4 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hd : |(x - x0) - j * s| ≤ 3 * |s| / 4 := by
    have e : (x - x0) - j * s = (x - τ₀ - k * s) - (x0 - τ₀ - k₁ * s) := by
      simp only [j]; push_cast; ring
    rw [e]
    calc |(x - τ₀ - k * s) - (x0 - τ₀ - k₁ * s)| ≤ |x - τ₀ - k * s| + |x0 - τ₀ - k₁ * s| := abs_sub _ _
      _ ≤ _ := by linarith
  apply Real.exp_le_exp.mpr
  rcases eq_or_ne j 0 with hj | hj
  · rw [hj]; simp only [Int.cast_zero, abs_zero, mul_zero]
    nlinarith [sq_nonneg (x - x0)]
  · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    have hjs : |(j : ℝ) * s| = |(j : ℝ)| * |s| := abs_mul _ _
    have hlow : |(j : ℝ)| * |s| / 4 ≤ |x - x0| := by
      have := abs_sub_abs_le_abs_sub ((j : ℝ) * s) (j * s - (x - x0))
      rw [show (j : ℝ) * s - (j * s - (x - x0)) = x - x0 by ring, abs_sub_comm, hjs] at this
      nlinarith
    have h0 : 0 ≤ |(j : ℝ)| * |s| / 4 := by positivity
    have hsq : (|(j : ℝ)| * |s| / 4) ^ 2 ≤ (x - x0) ^ 2 := by
      rw [← sq_abs (x - x0)]; exact pow_le_pow_left₀ h0 hlow 2
    have hss : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    have : |(j : ℝ)| * s ^ 2 / 16 ≤ (|(j : ℝ)| * |s| / 4) ^ 2 := by
      rw [hss]; nlinarith [sq_nonneg |s|]
    nlinarith

/-- **Gaussian mass of the bad set** in the regime `|Im β| > |Re β|`. -/
theorem gauss_union_le {P s ℓ τ₀ x0 : ℝ} (hP : 0 < P) (hs : s ≠ 0) (hℓ0 : 0 ≤ ℓ) (hℓ : 4 * ℓ ≤ |s|) :
    ∫ x in ⋃ k : ℤ, Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ), Real.exp (-P * (x - x0) ^ 2) ≤
      2 * ℓ * (1 + 32 / (P * s ^ 2)) := by
  set G : ℝ → ℝ := fun x => Real.exp (-P * (x - x0) ^ 2)
  set c : ℝ := P * s ^ 2 / 16
  have hc : 0 < c := by have := pow_pos (abs_pos.mpr hs) 2; rw [sq_abs] at this; positivity
  set k₁ := round ((x0 - τ₀) / s)
  set g : ℤ → ℝ := fun k => 2 * ℓ * Real.exp (-c * |((k - k₁ : ℤ) : ℝ)|)
  have hgs : HasSum g (2 * ℓ * ((1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹)) := by
    have h := ((hasSum_exp_abs hc).mul_left (2 * ℓ))
    exact ((Equiv.subRight k₁).hasSum_iff (f := fun j : ℤ => 2 * ℓ * Real.exp (-c * |(j : ℝ)|))).mpr h
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  set U := ⋃ k : ℤ, Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ)
  have hG0 : ∀ x, 0 ≤ G x := fun x => (Real.exp_pos _).le
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0)
    ((by fun_prop : Continuous G).aestronglyMeasurable)]
  have hlin : ∫⁻ x in U, ENNReal.ofReal (G x) ≤ ENNReal.ofReal (∑' k, g k) := by
    refine (lintegral_iUnion_le _ _).trans ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hg0 hgs.summable]
    refine ENNReal.tsum_le_tsum fun k => ?_
    calc ∫⁻ x in Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ), ENNReal.ofReal (G x)
        ≤ ∫⁻ _ in Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ), ENNReal.ofReal (Real.exp (-c * |((k - k₁ : ℤ) : ℝ)|)) :=
          setLIntegral_mono' measurableSet_Ioo fun x hx =>
            ENNReal.ofReal_le_ofReal (gauss_pt_le hP hs hℓ k hx)
      _ = ENNReal.ofReal (Real.exp (-c * |((k - k₁ : ℤ) : ℝ)|)) * ENNReal.ofReal (2 * ℓ) := by
          rw [setLIntegral_const, Real.volume_Ioo]; congr 2; ring
      _ = ENNReal.ofReal (g k) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; simp only [g]; ring_nf
  have hfin : ENNReal.ofReal (∑' k, g k) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.toReal_mono hfin hlin).trans ?_
  rw [ENNReal.toReal_ofReal (tsum_nonneg hg0), hgs.tsum_eq]
  have := tsum_exp_abs_le hc
  rw [(hasSum_exp_abs hc).tsum_eq] at this
  have e : 2 / c = 32 / (P * s ^ 2) := by simp only [c]; field_simp; ring
  rw [e] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### the bad set -/

/-- the two real lower bounds for `|v₀ + βx − 2πik|`, from `|w|·|β| = |w β̄|`. -/
lemma line_bounds (v₀ β : ℂ) (x : ℝ) (k : ℤ) :
    |(v₀ * (starRingEnd ℂ) β).re + ‖β‖ ^ 2 * x - 2 * π * k * β.im| ≤ ‖v₀ + β * x - 2 * π * I * k‖ * ‖β‖ ∧
    |(v₀ * (starRingEnd ℂ) β).im - 2 * π * k * β.re| ≤ ‖v₀ + β * x - 2 * π * I * k‖ * ‖β‖ := by
  set w := v₀ + β * x - 2 * π * I * k
  have hn : ‖w‖ * ‖β‖ = ‖w * (starRingEnd ℂ) β‖ := by rw [norm_mul, Complex.norm_conj]
  have hb : ‖β‖ ^ 2 = β.re ^ 2 + β.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : (w * (starRingEnd ℂ) β).re = (v₀ * (starRingEnd ℂ) β).re + ‖β‖ ^ 2 * x - 2 * π * k * β.im := by
    rw [hb]; simp only [w, mul_re, mul_im, sub_re, add_re, sub_im, add_im, conj_re, conj_im, ofReal_re,
      ofReal_im, I_re, I_im, intCast_re, intCast_im, Complex.re_ofNat, Complex.im_ofNat]; ring
  have him : (w * (starRingEnd ℂ) β).im = (v₀ * (starRingEnd ℂ) β).im - 2 * π * k * β.re := by
    simp only [w, mul_re, mul_im, sub_re, add_re, sub_im, add_im, conj_re, conj_im, ofReal_re,
      ofReal_im, I_re, I_im, intCast_re, intCast_im, Complex.re_ofNat, Complex.im_ofNat]; ring
  rw [hn, ← hre, ← him]
  exact ⟨abs_re_le_norm _, abs_im_le_norm _⟩

/-- **The non-uniform denominator bound** (Gaussian integral of `1/|1 − e^{v₀+βx}|`). -/
theorem bad_integral_le {P x0 : ℝ} (hP : 0 < P) {v₀ β : ℂ} (hβ : β ≠ 0) {m η : ℝ} (hm : 0 < m)
    (hη : 0 < η) (hη1 : η ≤ 1) (hden : ∀ x : ℝ, m ≤ ‖1 - cexp (v₀ + β * x)‖) :
    Integrable (fun x : ℝ => Real.exp (-P * (x - x0) ^ 2) / ‖1 - cexp (v₀ + β * x)‖) ∧
    ∫ x, Real.exp (-P * (x - x0) ^ 2) / ‖1 - cexp (v₀ + β * x)‖ ≤
      3 / η * √(π / P) + 1 / m * (2 * η / ‖β‖ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P))) := by
  set G : ℝ → ℝ := fun x => Real.exp (-P * (x - x0) ^ 2) with hGd
  set Dn : ℝ → ℝ := fun x => ‖1 - cexp (v₀ + β * x)‖
  have hGc : Continuous G := by fun_prop
  have hDc : Continuous Dn := by fun_prop
  have hG0 : ∀ x, 0 ≤ G x := fun x => (Real.exp_pos _).le
  have hG1 : ∀ x, G x ≤ 1 := fun x => by
    simp only [G]; rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - x0)]
  have hGi : Integrable G := (integrable_exp_neg_mul_sq hP).comp_sub_right x0
  have hGint : ∫ x, G x = √(π / P) := by
    simp only [G]; rw [integral_sub_right_eq_self (fun x => Real.exp (-P * x ^ 2)) x0, integral_gaussian]
  have hDpos : ∀ x, 0 < Dn x := fun x => hm.trans_le (hden x)
  have hFc : Continuous fun x => G x / Dn x := hGc.div hDc fun x => (hDpos x).ne'
  have hFi : Integrable fun x => G x / Dn x := by
    refine Integrable.mono' (hGi.div_const m) hFc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hG0 x) (hDpos x).le)]
    exact div_le_div_of_nonneg_left (hG0 x) hm (hden x)
  refine ⟨hFi, ?_⟩
  -- the bad set
  set Bad : Set ℝ := ⋃ k : ℤ, {x : ℝ | ‖v₀ + β * x - 2 * π * I * k‖ < η}
  have hBo : IsOpen Bad := isOpen_iUnion fun k => isOpen_lt (by fun_prop) continuous_const
  have hBm : MeasurableSet Bad := hBo.measurableSet
  have hpt : ∀ x, G x / Dn x ≤ 3 / η * G x + 1 / m * Bad.indicator G x := by
    intro x
    by_cases hx : x ∈ Bad
    · rw [Set.indicator_of_mem hx]
      have : G x / Dn x ≤ 1 / m * G x := by
        rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_left (hG0 x) hm (hden x)
      have : 0 ≤ 3 / η * G x := by have := hG0 x; positivity
      linarith
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      have hall : ∀ k : ℤ, η ≤ ‖v₀ + β * x - 2 * π * I * k‖ := by
        intro k; by_contra hk; push Not at hk
        exact hx (Set.mem_iUnion.mpr ⟨k, hk⟩)
      have h3 := norm_one_sub_exp_ge (v := v₀ + β * x) hall
      rw [min_eq_right hη1] at h3
      have hη3 : 0 < η / 3 := by positivity
      calc G x / Dn x ≤ G x / (η / 3) := div_le_div_of_nonneg_left (hG0 x) hη3 h3
        _ = 3 / η * G x := by field_simp
  have hsumi : Integrable fun x => 3 / η * G x + 1 / m * Bad.indicator G x :=
    (hGi.const_mul _).add ((hGi.indicator hBm).const_mul _)
  refine (integral_mono hFi hsumi hpt).trans ?_
  rw [integral_add (hGi.const_mul _) ((hGi.indicator hBm).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hBm, hGint]
  gcongr
  -- the Gaussian mass of the bad set
  set p := β.re
  set q := β.im
  set a := (v₀ * (starRingEnd ℂ) β).re
  set b := (v₀ * (starRingEnd ℂ) β).im
  have hbn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hB2 : ‖β‖ ^ 2 = p ^ 2 + q ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hB2p : 0 < ‖β‖ ^ 2 := by positivity
  set ℓ := η / ‖β‖
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hmemB : ∀ x ∈ Bad, ∃ k : ℤ, |a + ‖β‖ ^ 2 * x - 2 * π * k * q| < η * ‖β‖ ∧
      |b - 2 * π * k * p| < η * ‖β‖ := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have hk' : ‖v₀ + β * x - 2 * π * I * k‖ < η := hk
    obtain ⟨h1, h2⟩ := line_bounds v₀ β x k
    exact ⟨k, h1.trans_lt (mul_lt_mul_of_pos_right hk' hbn),
      h2.trans_lt (mul_lt_mul_of_pos_right hk' hbn)⟩
  have hN1 : 1 ≤ 1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P) := by
    have : 0 ≤ 16 * ‖β‖ ^ 2 / (π ^ 2 * P) := by positivity
    linarith
  have hGon : ∀ t : Set ℝ, IntegrableOn G t := fun t => hGi.integrableOn
  have hGae : ∀ t : Set ℝ, 0 ≤ᵐ[volume.restrict t] G := fun t => Eventually.of_forall hG0
  rcases le_or_gt |q| |p| with hqp | hqp
  · -- one pole only
    by_cases hne : Bad.Nonempty
    · obtain ⟨x₁, hx₁⟩ := hne
      obtain ⟨k₀, -, hk₀⟩ := hmemB x₁ hx₁
      set τ := (2 * π * k₀ * q - a) / ‖β‖ ^ 2
      have hsub : Bad ⊆ Ioo (τ - ℓ) (τ + ℓ) := by
        intro x hx
        obtain ⟨k, hk1, hk2⟩ := hmemB x hx
        have hkk : k = k₀ := by
          by_contra hne'
          have h1 : (1 : ℝ) ≤ ((k : ℝ) - k₀) ^ 2 := by
            have : (1 : ℝ) ≤ |((k - k₀ : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne')
            push_cast at this
            nlinarith [abs_nonneg ((k : ℝ) - k₀), sq_abs ((k : ℝ) - k₀)]
          have h2 : |2 * π * ((k : ℝ) - k₀) * p| < 2 * ‖β‖ := by
            have := abs_sub (b - 2 * π * k₀ * p) (b - 2 * π * k * p)
            rw [show b - 2 * π * k₀ * p - (b - 2 * π * k * p) = 2 * π * ((k : ℝ) - k₀) * p by ring] at this
            nlinarith
          have h3 : (2 * π * ((k : ℝ) - k₀) * p) ^ 2 < (2 * ‖β‖) ^ 2 := by
            rw [← sq_abs]; exact pow_lt_pow_left₀ h2 (abs_nonneg _) two_ne_zero
          have hpq : q ^ 2 ≤ p ^ 2 := by rw [← sq_abs q, ← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg _) hqp 2
          have hpi : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
          have hp2 : 0 < p ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * π ^ 2 * p ^ 2)]
        rw [hkk] at hk1
        have e : x - τ = (a + ‖β‖ ^ 2 * x - 2 * π * k₀ * q) / ‖β‖ ^ 2 := by
          simp only [τ]; field_simp; ring
        have : |x - τ| < ℓ := by
          rw [e, abs_div, abs_of_pos hB2p, div_lt_iff₀ hB2p]
          simp only [ℓ]; rw [div_mul_eq_mul_div, lt_div_iff₀ hbn]; nlinarith
        rw [abs_lt] at this
        exact ⟨by linarith, by linarith⟩
      calc ∫ x in Bad, G x ≤ ∫ x in Ioo (τ - ℓ) (τ + ℓ), G x :=
            setIntegral_mono_set (hGon _) (hGae _) (Eventually.of_forall hsub)
        _ ≤ ∫ x in Ioo (τ - ℓ) (τ + ℓ), (1 : ℝ) :=
            setIntegral_mono_on (hGon _) (integrableOn_const (by simp)) measurableSet_Ioo fun x _ => hG1 x
        _ = 2 * ℓ := by
            rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul, mul_one]; ring
        _ ≤ 2 * ℓ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P)) := le_mul_of_one_le_right (by positivity) hN1
        _ = 2 * η / ‖β‖ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P)) := by simp only [ℓ]; ring
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Measure.restrict_empty, integral_zero_measure]
      positivity
  · -- a progression of poles
    have hq0 : q ≠ 0 := fun h => by rw [h, abs_zero] at hqp; exact (abs_nonneg p).not_gt hqp
    have hpq : p ^ 2 < q ^ 2 := by rw [← sq_abs q, ← sq_abs p]; exact pow_lt_pow_left₀ hqp (abs_nonneg _) two_ne_zero
    set s := 2 * π * q / ‖β‖ ^ 2
    set τ₀ := -a / ‖β‖ ^ 2
    have hs : s ≠ 0 := by simp only [s]; have := Real.pi_pos; positivity
    have habs : |s| = 2 * π * |q| / ‖β‖ ^ 2 := by
      simp only [s]; rw [abs_div, abs_mul, abs_of_pos hB2p, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have hpi : 8 < π ^ 2 := by nlinarith [Real.pi_gt_three]
    have h2b : 2 * ‖β‖ ≤ π * |q| := by
      have h : (2 * ‖β‖) ^ 2 ≤ (π * |q|) ^ 2 := by
        rw [mul_pow, mul_pow, hB2, sq_abs]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h
    have hℓs : 4 * ℓ ≤ |s| := by
      rw [habs]; simp only [ℓ]
      rw [← mul_div_assoc, div_le_div_iff₀ hbn hB2p]
      have : 4 * η * ‖β‖ ^ 2 ≤ 4 * ‖β‖ ^ 2 := by nlinarith
      nlinarith
    have hsub : Bad ⊆ ⋃ k : ℤ, Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ) := by
      intro x hx
      obtain ⟨k, hk1, -⟩ := hmemB x hx
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      have e : x - (τ₀ + k * s) = (a + ‖β‖ ^ 2 * x - 2 * π * k * q) / ‖β‖ ^ 2 := by
        simp only [τ₀, s]; field_simp; ring
      have : |x - (τ₀ + k * s)| < ℓ := by
        rw [e, abs_div, abs_of_pos hB2p, div_lt_iff₀ hB2p]
        simp only [ℓ]; rw [div_mul_eq_mul_div, lt_div_iff₀ hbn]; nlinarith
      rw [abs_lt] at this
      exact ⟨by linarith, by linarith⟩
    have hgu := gauss_union_le (x0 := x0) (τ₀ := τ₀) hP hs hℓ0 hℓs
    have hNle : 32 / (P * s ^ 2) ≤ 16 * ‖β‖ ^ 2 / (π ^ 2 * P) := by
      have hs2 : s ^ 2 = 4 * π ^ 2 * q ^ 2 / (‖β‖ ^ 2) ^ 2 := by simp only [s]; ring
      rw [hs2, div_le_div_iff₀ (by positivity) (by positivity)]
      have hq2 : 0 < q ^ 2 := by positivity
      have : ‖β‖ ^ 2 ≤ 2 * q ^ 2 := by rw [hB2]; linarith
      have e : 32 * (π ^ 2 * P) = 8 * (4 * π ^ 2 * P) := by ring
      field_simp
      nlinarith [mul_pos (mul_pos hq2 hP) (pow_pos Real.pi_pos 2), mul_pos hB2p hB2p]
    calc ∫ x in Bad, G x ≤ ∫ x in ⋃ k : ℤ, Ioo (τ₀ + k * s - ℓ) (τ₀ + k * s + ℓ), G x :=
          setIntegral_mono_set (hGon _) (hGae _) (Eventually.of_forall hsub)
      _ ≤ 2 * ℓ * (1 + 32 / (P * s ^ 2)) := hgu
      _ ≤ 2 * ℓ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P)) := by gcongr
      _ = 2 * η / ‖β‖ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * P)) := by simp only [ℓ]; ring

/-- `min_{0<η≤1} (a/η + bη) ≤ 2a + 2√(ab)`. -/
lemma opt_eta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ a / η + b * η ≤ 2 * a + 2 * √(a * b) := by
  have hs0 : 0 ≤ √(a * b) := Real.sqrt_nonneg _
  rcases le_or_gt a b with hab | hab
  · refine ⟨√(a / b), Real.sqrt_pos.mpr (div_pos ha hb), ?_, ?_⟩
    · rw [Real.sqrt_le_one]; exact (div_le_one hb).mpr hab
    · have hu := Real.sqrt_pos.mpr ha
      have hv := Real.sqrt_pos.mpr hb
      rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
      have e1 : a = √a ^ 2 := (Real.sq_sqrt ha.le).symm
      have e2 : b = √b ^ 2 := (Real.sq_sqrt hb.le).symm
      have : a / (√a / √b) + b * (√a / √b) = 2 * (√a * √b) := by
        field_simp
        rw [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]; ring
      rw [this]; nlinarith
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    rw [div_one, mul_one]; linarith

end

end MockCusp
