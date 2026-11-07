/-
# Step 4/5 of `docs/SKQF_PROOF.md` §4: the twisted smoothed sums `J_z` (level 1)

    J_z(x) = Σ_{m≤x} fR(m) m^{−1+iz} log(x/m) = Σ_{m≤x} (fR(m)/m) e^{iz log m} log(x/m),

`fR` = coefficients of `R(s)^{−1/2}` (`SelbergDelange3.fR`).  `J_0 = Isum fR` (`QFProof.J_bound`).

Abel summation against `S(u) = Σ_{m≤u} fR(m)/m` (`Ssum fR`):

    J_z(x) = −∫_1^x S(u) u^{iz−1}(iz log(x/u) − 1) du,

and the pointwise first clause of `selberg_sum_fR` gives `|S(u)| ≤ K (1+log u)^{−1/2}`, so

    |J_z(x)| ≤ K (1+log x)^{1/2} (1 + |z| log x) x^{|Im z|}          (all z ∈ ℂ, x ≥ 1).

No Deligne bound, no strip restriction.
-/
import RamanujanTau.SelbergDelange3.Selberg
import Mathlib.NumberTheory.AbelSummation

set_option autoImplicit false

namespace RamanujanTau.SvStripB

open Finset Complex MeasureTheory
open RamanujanTau.SelbergDelange2 (Isum Ssum)
open RamanujanTau.SelbergDelange3 (fR selberg_sum_fR)

/-- **The twisted smoothed sum** `J_z(x) = Σ_{m≤x} (fR(m)/m) m^{iz} log(x/m)`. -/
noncomputable def Jz (z : ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ Ioc 0 ⌊x⌋₊, ((fR m / m : ℝ) : ℂ) * cexp (I * z * (Real.log m : ℂ)) * (Real.log (x / m) : ℂ)

/-- `J_0 = J = Isum fR`. -/
lemma Jz_zero (x : ℝ) : Jz 0 x = (Isum fR x : ℂ) := by
  unfold Jz Isum; push_cast; simp

/-- The term in `s`-normalisation: `fR(m) m^{−s}` with `s = 1 − iz`. -/
lemma term_cpow (z : ℂ) {m : ℕ} (hm : 0 < m) :
    (fR m : ℂ) * (m : ℂ) ^ (-(1 - I * z)) =
      ((fR m / m : ℝ) : ℂ) * cexp (I * z * (Real.log m : ℂ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_log hmR.le]
  rw [cpow_def_of_ne_zero hm0, hl]
  have e : cexp (↑(Real.log m) * -(1 - I * z)) =
      cexp (↑(-Real.log m)) * cexp (I * z * ↑(Real.log m)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [e, ← ofReal_exp, Real.exp_neg, Real.exp_log hmR]
  push_cast; ring

/-- `J_z(x) = Σ_{m≤x} fR(m) m^{−(1−iz)} log(x/m)`. -/
lemma Jz_eq_cpow (z : ℂ) (x : ℝ) :
    Jz z x = ∑ m ∈ Ioc 0 ⌊x⌋₊, (fR m : ℂ) * (m : ℂ) ^ (-(1 - I * z)) * (Real.log (x / m) : ℂ) := by
  unfold Jz
  refine sum_congr rfl fun m hm => ?_
  rw [term_cpow z (mem_Ioc.1 hm).1]

/-- **Holomorphy**: `z ↦ J_z(x)` is entire (finite sum). -/
theorem Jz_differentiable (x : ℝ) : Differentiable ℂ (fun z => Jz z x) := by
  unfold Jz
  refine Differentiable.fun_sum fun m _ => ?_
  fun_prop

theorem Jz_differentiableOn (x : ℝ) (U : Set ℂ) : DifferentiableOn ℂ (fun z => Jz z x) U :=
  (Jz_differentiable x).differentiableOn

/-! ### The pointwise bound for `S(u) = Σ_{m≤u} fR(m)/m` -/

lemma Ssum_le_trivial {t X : ℝ} (htX : t ≤ X) :
    |Ssum fR t| ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, |fR n| / n := by
  unfold Ssum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : Ioc 0 ⌊t⌋₊ ⊆ Ioc 0 ⌊X⌋₊ := Ioc_subset_Ioc_right (Nat.floor_le_floor htX)
  refine le_trans (le_of_eq (sum_congr rfl fun n _ => ?_))
    (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity)
  rw [abs_div, Nat.abs_cast]

/-- **`|S(u)| ≤ K/√(1+log u)`** for `u ≥ 1` (level 1, from the first clause of `selberg_sum_fR`). -/
theorem Ssum_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ t →
    |Ssum fR t| ≤ K / Real.sqrt (1 + Real.log t) := by
  obtain ⟨C₁, K₃, X₂, c₀, h⟩ := selberg_sum_fR
  set X : ℝ := max X₂ (Real.exp (2 * |c₀| + 2)) with hX
  have hX1 : 1 ≤ X := le_trans (Real.one_le_exp (by positivity)) (le_max_right _ _)
  set K0 : ℝ := ∑ n ∈ Ioc 0 ⌊X⌋₊, |fR n| / n with hK0
  have hK00 : 0 ≤ K0 := sum_nonneg fun n _ => by positivity
  have hsX : 0 ≤ Real.sqrt (1 + Real.log X) := Real.sqrt_nonneg _
  refine ⟨K0 * Real.sqrt (1 + Real.log X) + 2 * |C₁| + 4 * |K₃|, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set L := Real.log t with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ht
  have hs : 0 < Real.sqrt (1 + L) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  rcases lt_or_ge t X with hlt | hge
  · have hb := Ssum_le_trivial hlt.le
    rw [← hK0] at hb
    have hLX : Real.sqrt (1 + L) ≤ Real.sqrt (1 + Real.log X) :=
      Real.sqrt_le_sqrt (by linarith [Real.log_le_log ht0 hlt.le])
    have : |Ssum fR t| * Real.sqrt (1 + L) ≤ K0 * Real.sqrt (1 + Real.log X) :=
      mul_le_mul hb hLX hs.le hK00
    have : 0 ≤ 2 * |C₁| + 4 * |K₃| := by positivity
    linarith
  · have hx2 : X₂ ≤ t := le_trans (le_max_left _ _) hge
    have hta : 2 * |c₀| + 2 ≤ L := by
      rw [hL, Real.le_log_iff_exp_le ht0]; exact le_trans (le_max_right _ _) hge
    have hc := le_abs_self c₀
    have hpos : 0 < L - c₀ := by linarith [abs_nonneg c₀]
    have hL1 : 1 ≤ L := by linarith [abs_nonneg c₀]
    have hLp : 0 < L := by linarith
    have h1 := (h t hx2).1
    rw [← hL] at h1
    set s := Real.sqrt (1 + L) with hsdef
    set r := Real.sqrt (L - c₀) with hr
    set q := Real.sqrt L with hq
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hq0 : 0 < q := Real.sqrt_pos.2 hLp
    have hs2 : s ^ 2 = 1 + L := Real.sq_sqrt (by linarith)
    have hr2 : r ^ 2 = L - c₀ := Real.sq_sqrt hpos.le
    have hq2 : q ^ 2 = L := Real.sq_sqrt hLp.le
    have hsr : s ≤ 2 * r := by nlinarith [abs_nonneg c₀]
    have hsq : s ≤ 2 * q := by nlinarith
    have e1 : (L - c₀) ^ (-(1 / 2 : ℝ)) = r⁻¹ := by
      rw [Real.rpow_neg hpos.le, hr, Real.sqrt_eq_rpow]
    have e2 : L ^ (-(1 / 2 : ℝ) - 1) = q⁻¹ / L := by
      rw [Real.rpow_sub_one hLp.ne', Real.rpow_neg hLp.le, hq, Real.sqrt_eq_rpow]
    rw [e1, e2] at h1
    have hlog : Real.log (1 + L) ≤ L := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + L by linarith); linarith
    have hlog0 : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
    -- main term
    have hm : |C₁ * r⁻¹| * s ≤ 2 * |C₁| := by
      rw [abs_mul, abs_inv, abs_of_pos hr0, mul_assoc]
      have : r⁻¹ * s ≤ 2 := by
        rw [inv_mul_le_iff₀ hr0]; linarith
      nlinarith [abs_nonneg C₁]
    -- error term
    have he : K₃ * (1 + Real.log (1 + L)) * (q⁻¹ / L) * s ≤ 4 * |K₃| := by
      have hA : 0 ≤ (1 + Real.log (1 + L)) * (q⁻¹ / L) * s := by positivity
      have hB : (1 + Real.log (1 + L)) * (q⁻¹ / L) * s ≤ 4 := by
        have : (1 + Real.log (1 + L)) * (q⁻¹ / L) * s ≤ (2 * L) * (q⁻¹ / L) * (2 * q) := by
          gcongr; linarith
        refine this.trans (le_of_eq ?_)
        field_simp; ring
      calc K₃ * (1 + Real.log (1 + L)) * (q⁻¹ / L) * s
          = K₃ * ((1 + Real.log (1 + L)) * (q⁻¹ / L) * s) := by ring
        _ ≤ |K₃| * ((1 + Real.log (1 + L)) * (q⁻¹ / L) * s) := by gcongr; exact le_abs_self K₃
        _ ≤ |K₃| * 4 := by gcongr
        _ = 4 * |K₃| := by ring
    have htri : |Ssum fR t| ≤ |Ssum fR t - C₁ * r⁻¹| + |C₁ * r⁻¹| := by
      have := abs_add_le (Ssum fR t - C₁ * r⁻¹) (C₁ * r⁻¹); simpa using this
    have hs0 : 0 ≤ s := hs.le
    have : |Ssum fR t| * s ≤ |Ssum fR t - C₁ * r⁻¹| * s + |C₁ * r⁻¹| * s := by nlinarith
    have : |Ssum fR t - C₁ * r⁻¹| * s ≤ K₃ * (1 + Real.log (1 + L)) * (q⁻¹ / L) * s :=
      mul_le_mul_of_nonneg_right h1 hs0
    have : 0 ≤ K0 * Real.sqrt (1 + Real.log X) := by positivity
    linarith

/-! ### Abel summation -/

/-- The Abel weight `φ(u) = u^{iz}(log x − log u)`. -/
noncomputable def wt (z : ℂ) (x u : ℝ) : ℂ :=
  cexp (I * z * (Real.log u : ℂ)) * ((Real.log x : ℂ) - (Real.log u : ℂ))

/-- Its derivative `φ'(u) = u^{iz}(iz(log x − log u) − 1)/u`. -/
noncomputable def wt' (z : ℂ) (x u : ℝ) : ℂ :=
  cexp (I * z * (Real.log u : ℂ)) * ((I * z * ((Real.log x : ℂ) - (Real.log u : ℂ)) - 1) * (u : ℂ)⁻¹)

lemma hasDerivAt_wt (z : ℂ) (x : ℝ) {u : ℝ} (hu : 0 < u) : HasDerivAt (wt z x) (wt' z x u) u := by
  have hl : HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) ((u⁻¹ : ℝ) : ℂ) u :=
    (Real.hasDerivAt_log hu.ne').ofReal_comp
  have h1 := (hl.const_mul (I * z)).cexp
  have h2 := hl.const_sub (Real.log x : ℂ)
  convert h1.mul h2 using 1
  unfold wt'; push_cast; ring

lemma continuousOn_wt' (z : ℂ) (x : ℝ) : ContinuousOn (wt' z x) (Set.Icc 1 x) := by
  have hlog : ContinuousOn (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (Set.Icc 1 x) :=
    continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun u hu => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hu.1])
  have hinv : ContinuousOn (fun u : ℝ => (u : ℂ)⁻¹) (Set.Icc 1 x) :=
    continuous_ofReal.continuousOn.inv₀ fun u hu => by
      simp only [ne_eq, ofReal_eq_zero]; linarith [hu.1]
  unfold wt'
  refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ hinv)
  · exact (continuousOn_const.mul hlog).cexp
  · exact (continuousOn_const.mul (continuousOn_const.sub hlog)).sub continuousOn_const

lemma sum_c_eq (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, ((fR k / k : ℝ) : ℂ) = (Ssum fR t : ℂ) := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  unfold Ssum; push_cast; simp

/-- **Abel summation identity**: `J_z(x) = −∫_{(1,x]} φ'(u) S(u) du`. -/
theorem Jz_eq_integral (z : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    Jz z x = -∫ t in Set.Ioc 1 x, wt' z x t * (Ssum fR t : ℂ) := by
  set c : ℕ → ℂ := fun k => ((fR k / k : ℝ) : ℂ) with hc
  have hc0 : c 0 = 0 := by simp [hc]
  have hdiff : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ (wt z x) t := fun t ht =>
    (hasDerivAt_wt z x (by linarith [ht.1])).differentiableAt
  have heq : Set.EqOn (wt' z x) (deriv (wt z x)) (Set.Icc 1 x) := fun t ht =>
    ((hasDerivAt_wt z x (by linarith [ht.1])).deriv).symm
  have hint : IntegrableOn (deriv (wt z x)) (Set.Icc 1 x) :=
    ((continuousOn_wt' z x).integrableOn_Icc).congr_fun heq measurableSet_Icc
  have hA := sum_mul_eq_sub_integral_mul₀ c hc0 x hdiff hint
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, wt z x k * c k = Jz z x := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, hc0, mul_zero, zero_add]
    unfold Jz
    refine sum_congr rfl fun m hm => ?_
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hm).1.ne'
    have hx0 : x ≠ 0 := by linarith
    rw [Real.log_div hx0 hm0]
    simp only [wt, hc]; push_cast; ring
  have hb : wt z x x = 0 := by simp [wt]
  rw [← hL, hA, hb, zero_mul, zero_sub]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [sum_c_eq, ← heq ⟨ht.1.le, ht.2⟩]

/-! ### The bound -/

lemma norm_wt'_le (z : ℂ) {x t : ℝ} (ht1 : 1 ≤ t) (htx : t ≤ x) :
    ‖wt' z x t‖ ≤ Real.exp (|z.im| * Real.log x) * (1 + ‖z‖ * Real.log x) * t⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hltx : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx
  unfold wt'
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have h1 : Real.exp (I * z * ↑(Real.log t)).re ≤ Real.exp (|z.im| * Real.log x) := by
    apply Real.exp_le_exp.2
    have : (I * z * ↑(Real.log t)).re = -z.im * Real.log t := by simp [mul_re]
    rw [this]
    have : -z.im ≤ |z.im| := neg_le_abs _
    nlinarith [abs_nonneg z.im]
  have h2 : ‖I * z * ((Real.log x : ℂ) - (Real.log t : ℂ)) - 1‖ ≤ 1 + ‖z‖ * Real.log x := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_I, one_mul, norm_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg z]
  have : 0 ≤ t⁻¹ := by positivity
  calc Real.exp (I * z * ↑(Real.log t)).re * (‖I * z * (↑(Real.log x) - ↑(Real.log t)) - 1‖ * t⁻¹)
      ≤ Real.exp (|z.im| * Real.log x) * ((1 + ‖z‖ * Real.log x) * t⁻¹) := by gcongr
    _ = _ := by ring

/-- `∫_1^x du/(u√(1+log u)) = 2(√(1+log x) − 1)`. -/
lemma integral_weight {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, t⁻¹ * (Real.sqrt (1 + Real.log t))⁻¹ =
      2 * Real.sqrt (1 + Real.log x) - 2 := by
  have hd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt (fun u => 2 * Real.sqrt (1 + Real.log u))
      (t⁻¹ * (Real.sqrt (1 + Real.log t))⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < 1 + Real.log t := by linarith [Real.log_nonneg ht.1]
    have := (((Real.hasDerivAt_log ht0.ne').const_add 1).sqrt hl0.ne').const_mul 2
    convert this using 1
    have : 0 < Real.sqrt (1 + Real.log t) := Real.sqrt_pos.2 hl0
    field_simp
  have hc : ContinuousOn (fun t : ℝ => t⁻¹ * (Real.sqrt (1 + Real.log t))⁻¹) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun u hu => ?_) (ContinuousOn.inv₀ ?_ ?_)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hu.1]
    · exact (continuousOn_const.add (Real.continuousOn_log.mono fun u hu => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hu.1])).sqrt
    · intro u hu
      exact (Real.sqrt_pos.2 (by linarith [Real.log_nonneg hu.1])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  simp

/-- **Main bound** (level 1): for all `z ∈ ℂ`, `x ≥ 1`,
`|J_z(x)| ≤ K √(1+log x) (1 + |z| log x) x^{|Im z|}`. -/
theorem Jz_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ∀ x : ℝ, 1 ≤ x →
    ‖Jz z x‖ ≤ K * Real.sqrt (1 + Real.log x) * (1 + ‖z‖ * Real.log x) *
      Real.exp (|z.im| * Real.log x) := by
  obtain ⟨K, hK, hS⟩ := Ssum_bound
  refine ⟨2 * K, by positivity, fun z x hx => ?_⟩
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set A : ℝ := Real.exp (|z.im| * Real.log x) * (1 + ‖z‖ * Real.log x) with hA
  have hA0 : 0 ≤ A := by positivity
  set g : ℝ → ℝ := fun t => A * K * (t⁻¹ * (Real.sqrt (1 + Real.log t))⁻¹) with hg
  have hgi : IntervalIntegrable g volume 1 x := by
    have hc : ContinuousOn (fun t : ℝ => t⁻¹ * (Real.sqrt (1 + Real.log t))⁻¹) (Set.Icc 1 x) := by
      refine ContinuousOn.mul (continuousOn_inv₀.mono fun u hu => ?_) (ContinuousOn.inv₀ ?_ ?_)
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hu.1]
      · exact (continuousOn_const.add (Real.continuousOn_log.mono fun u hu => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hu.1])).sqrt
      · intro u hu
        exact (Real.sqrt_pos.2 (by linarith [Real.log_nonneg hu.1])).ne'
    rw [← Set.uIcc_of_le hx] at hc
    exact (continuousOn_const.mul hc).intervalIntegrable
  have hgI : IntegrableOn g (Set.Ioc 1 x) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hgi
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)), ‖wt' z x t * (Ssum fR t : ℂ)‖ ≤ g t := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 ≤ t := ht.1.le
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    have h1 := norm_wt'_le z ht1 ht.2
    have h2 := hS t ht1
    have hl0 : 0 < Real.sqrt (1 + Real.log t) := Real.sqrt_pos.2 (by linarith [Real.log_nonneg ht1])
    calc ‖wt' z x t‖ * |Ssum fR t|
        ≤ (Real.exp (|z.im| * Real.log x) * (1 + ‖z‖ * Real.log x) * t⁻¹) *
            (K / Real.sqrt (1 + Real.log t)) := by gcongr
      _ = g t := by simp only [hg, hA]; ring
  have hmain := norm_integral_le_of_norm_le hgI hpt
  have hgint : ∫ t in Set.Ioc 1 x, g t = A * K * (2 * Real.sqrt (1 + Real.log x) - 2) := by
    rw [← intervalIntegral.integral_of_le hx, hg]
    simp only
    rw [intervalIntegral.integral_const_mul, integral_weight hx]
  rw [hgint] at hmain
  rw [Jz_eq_integral z hx, norm_neg]
  refine hmain.trans ?_
  have : 0 ≤ Real.sqrt (1 + Real.log x) := Real.sqrt_nonneg _
  have : A * K * (2 * Real.sqrt (1 + Real.log x) - 2) ≤ A * K * (2 * Real.sqrt (1 + Real.log x)) := by
    have : 0 ≤ A * K := by positivity
    nlinarith
  refine this.trans (le_of_eq ?_)
  rw [hA]; ring

/-- The same, with `(1+log x)^{1/2}` written as an `rpow` (as in `QFProof.J_bound`). -/
theorem Jz_bound_rpow : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ∀ x : ℝ, 1 ≤ x →
    ‖Jz z x‖ ≤ K * (1 + Real.log x) ^ (1 / 2 : ℝ) * (1 + ‖z‖ * Real.log x) *
      Real.exp (|z.im| * Real.log x) := by
  obtain ⟨K, hK, h⟩ := Jz_bound
  exact ⟨K, hK, fun z x hx => by rw [← Real.sqrt_eq_rpow]; exact h z x hx⟩

/-- **Strip form** (`|z|` traded for `|Re z|`, at the cost `x^{|Im z|}`):
`|J_z(x)| ≤ K √(1+log x) (1 + |Re z| log x) x^{2|Im z|}`. -/
theorem Jz_bound_re : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ∀ x : ℝ, 1 ≤ x →
    ‖Jz z x‖ ≤ K * Real.sqrt (1 + Real.log x) * (1 + |z.re| * Real.log x) *
      Real.exp (2 * |z.im| * Real.log x) := by
  obtain ⟨K, hK, h⟩ := Jz_bound
  refine ⟨K, hK, fun z x hx => (h z x hx).trans ?_⟩
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set b := |z.im| * Real.log x with hb
  have hb0 : 0 ≤ b := by positivity
  have hz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hkey : (1 + ‖z‖ * Real.log x) * Real.exp b ≤
      (1 + |z.re| * Real.log x) * Real.exp (2 * |z.im| * Real.log x) := by
    have e : Real.exp (2 * |z.im| * Real.log x) = Real.exp b * Real.exp b := by
      rw [← Real.exp_add, hb]; ring_nf
    rw [e]
    have hexp : 1 + b ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
    have hE : 0 < Real.exp b := Real.exp_pos b
    have h1 : 1 + ‖z‖ * Real.log x ≤ (1 + |z.re| * Real.log x) + b := by
      rw [hb]; nlinarith
    have h2 : (1 + |z.re| * Real.log x) + b ≤ (1 + |z.re| * Real.log x) * Real.exp b := by
      have : 0 ≤ |z.re| * Real.log x := by positivity
      nlinarith
    calc (1 + ‖z‖ * Real.log x) * Real.exp b ≤ ((1 + |z.re| * Real.log x) * Real.exp b) * Real.exp b := by
          gcongr; linarith
      _ = _ := by ring
  have hs : 0 ≤ K * Real.sqrt (1 + Real.log x) := by positivity
  calc K * Real.sqrt (1 + Real.log x) * (1 + ‖z‖ * Real.log x) * Real.exp b
      = K * Real.sqrt (1 + Real.log x) * ((1 + ‖z‖ * Real.log x) * Real.exp b) := by ring
    _ ≤ K * Real.sqrt (1 + Real.log x) *
        ((1 + |z.re| * Real.log x) * Real.exp (2 * |z.im| * Real.log x)) := by gcongr
    _ = _ := by ring

end RamanujanTau.SvStripB
