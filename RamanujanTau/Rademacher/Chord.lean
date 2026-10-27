/-
# The error term on a Ford segment: the chord estimate

`E(w) = W(w)(F(q'(w)) − 1)`. In `z = 1/w` the segment `w = k + iu` is an arc of the circle
`|z − 1/2k| = 1/2k`. `E_z(z) = E(1/z)·i/z²` is holomorphic on a disc inside `Re z > 0` containing the arc and its chord,
so (Morera) the two integrals agree. On the chord `Re(1/z) ≥ k` and `|z| ≤ √2/N`, so
`|E_z| ≤ C|z|^{1/2}`, and the chord has length `≤ 2√2/N`: the error is `O(N^{−3/2})`.
-/
import RamanujanTau.Rademacher.MainTerm

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Filter Metric MeasureTheory Set
open scoped Real Topology

noncomputable section

/-- **path independence** for a function with a primitive. -/
lemma integral_eq_of_primitive {f P : ℂ → ℂ} {U : Set ℂ} (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    {γ γ' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ Icc a b, γ t ∈ U)
    (hcont : ContinuousOn (fun t => f (γ t) * γ' t) (Icc a b)) :
    ∫ t in a..b, f (γ t) * γ' t = P (γ b) - P (γ a) := by
  have hder : ∀ t ∈ Icc a b, HasDerivAt (fun t => P (γ t)) (f (γ t) * γ' t) t := by
    intro t ht
    have := ((hP (γ t) (hmem t ht)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t)
    simpa [Function.comp, mul_comm] using this
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ (fun t ht => hder t (Ioo_subset_Icc_self ht))
    (hcont.intervalIntegrable_of_Icc hab)
  exact fun t ht => (hder t ht).continuousAt.continuousWithinAt

/-! ### the error integrand -/

/-- `E(w) = W(w)(F(q'(w)) − 1)`. -/
def Ef (h' : ℤ) (k n : ℕ) (w : ℂ) : ℂ := Wf k n w * (F (qp h' k w) - 1)

/-- `E_z(z) = E(1/z)·i/z²`. -/
def Ez (h' : ℤ) (k n : ℕ) (z : ℂ) : ℂ := Ef h' k n (1 / z) * (I / z ^ 2)

lemma qp_mem {h' : ℤ} {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.re) : qp h' k w ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, qp, norm_exp]
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have : (2 * π * I * ((h' + I * w) / k)).re = -(2 * π * w.re / k) := by
    rw [show (2 * π * I * ((h' + I * w) / k)) = ((2 * π / k : ℝ) : ℂ) * (I * h' - w) by
      push_cast; field_simp; ring_nf; rw [I_sq]; ring, re_ofReal_mul]
    simp; ring
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  have : 0 < 2 * π * w.re / k := by positivity
  linarith

lemma differentiableAt_Wf {k n : ℕ} {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ (Wf k n) w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  unfold Wf
  refine DifferentiableAt.mul ?_ ?_
  · exact differentiableAt_id.cpow_const (Or.inl hw)
  · exact ((differentiableAt_const _).mul differentiableAt_id |>.add
      ((differentiableAt_const _).div differentiableAt_id hw0)).cexp

lemma differentiableAt_Ef {h' : ℤ} {k n : ℕ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (Ef h' k n) w := by
  unfold Ef
  refine (differentiableAt_Wf hw).mul (DifferentiableAt.sub_const ?_ _)
  have hq : DifferentiableAt ℂ (qp h' k) w := by unfold qp; fun_prop
  exact (F_diff.differentiableAt (isOpen_ball.mem_nhds (qp_mem hk hw))).comp w hq

lemma re_inv_pos {z : ℂ} (hz : 0 < z.re) : 0 < (1 / z).re := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [one_div, inv_re]; exact div_pos hz (Complex.normSq_pos.mpr hz0)

lemma differentiableAt_Ez {h' : ℤ} {k n : ℕ} (hk : 0 < k) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (Ez h' k n) z := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  unfold Ez
  refine DifferentiableAt.mul ?_ ((differentiableAt_const _).div (by fun_prop) (pow_ne_zero _ hz0))
  exact (differentiableAt_Ef hk (re_inv_pos hz)).comp z ((differentiableAt_const _).div differentiableAt_id hz0)

/-! ### the pointwise bound -/

/-- `S₀ = Σ_{m≥1} p(m) e^{−2πm}`. -/
def S0 : ℝ := ∑' m : ℕ, (p (m + 1) : ℝ) * Real.exp (-(2 * π * (m + 1)))

lemma summable_S0 : Summable fun m : ℕ => (p (m + 1) : ℝ) * Real.exp (-(2 * π * (m + 1))) := by
  have := (summable_p_exp (t := 2 * π) (by positivity)).comp_injective (add_left_injective 1)
  refine this.congr fun m => ?_
  simp only [Function.comp]; push_cast; ring_nf

/-- `CE(n) = e^{2πn + π/12} S₀`. -/
def CE (n : ℕ) : ℝ := Real.exp (2 * π * n + π / 12) * S0

lemma S0_nonneg : 0 ≤ S0 := tsum_nonneg fun m => by positivity

lemma p_zero' : p 0 = 1 := by decide

lemma term_le {X : ℝ} {k : ℕ} (hk : 0 < k) (hX : (k : ℝ) ≤ X) (m : ℕ) :
    Real.exp (π * X / (12 * k)) * ((p (m + 1) : ℝ) * Real.exp (-(2 * π * X / k)) ^ (m + 1)) ≤
      Real.exp (π / 12) * ((p (m + 1) : ℝ) * Real.exp (-(2 * π * (m + 1)))) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.exp_nat_mul, mul_left_comm, mul_left_comm (Real.exp (π / 12)), ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  set Y := X / k with hY
  have hY1 : 1 ≤ Y := by rw [hY, le_div_iff₀ hkr]; linarith
  have e1 : π * X / (12 * k) = π * Y / 12 := by rw [hY]; field_simp
  have e2 : (((m + 1 : ℕ) : ℝ)) * -(2 * π * X / k) = -(2 * π * ((m : ℝ) + 1) * Y) := by rw [hY]; push_cast; ring
  rw [e1, e2]
  have hc : 0 ≤ π * (2 * ((m : ℝ) + 1) - 1 / 12) := by
    have := Real.pi_pos; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hY1 hc]

lemma norm_expF_le {h' : ℤ} {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : (k : ℝ) ≤ w.re) :
    ‖cexp (π / (12 * k) * w)‖ * ‖F (qp h' k w) - 1‖ ≤ Real.exp (π / 12) * S0 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hwre : 0 < w.re := lt_of_lt_of_le hkr hw
  have hq := qp_mem (h' := h') hk hwre
  have hs := hasSum_F hq
  rw [← hasSum_nat_add_iff' 1] at hs
  simp only [Finset.range_one, Finset.sum_singleton, p_zero', pow_zero, mul_one, Nat.cast_one] at hs
  have hnq : ‖qp h' k w‖ = Real.exp (-(2 * π * w.re / k)) := by
    rw [qp, norm_exp]
    congr 1
    rw [show (2 * π * I * ((h' + I * w) / k)) = ((2 * π / k : ℝ) : ℂ) * (I * h' - w) by
      push_cast; field_simp; ring_nf; rw [I_sq]; ring, re_ofReal_mul]
    simp; ring
  have hea : ‖cexp (π / (12 * k) * w)‖ = Real.exp (π * w.re / (12 * k)) := by
    rw [norm_exp, show (π : ℂ) / (12 * k) = ((π / (12 * k) : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
    ring_nf
  rw [hea]
  have hE0 : 0 < Real.exp (π * w.re / (12 * k)) := Real.exp_pos _
  have hsum : Summable fun m : ℕ => (p (m + 1) : ℝ) * ‖qp h' k w‖ ^ (m + 1) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (summable_S0.mul_left
      (Real.exp (π / 12) / Real.exp (π * w.re / (12 * k))))
    have := term_le hk hw m
    rw [hnq]
    rw [div_mul_eq_mul_div, le_div_iff₀ hE0, mul_comm]
    linarith
  have hnorm : ‖F (qp h' k w) - 1‖ ≤ ∑' m : ℕ, (p (m + 1) : ℝ) * ‖qp h' k w‖ ^ (m + 1) :=
    hs.norm_le_of_bounded hsum.hasSum fun m => by rw [norm_mul, norm_pow, Complex.norm_natCast]
  calc Real.exp (π * w.re / (12 * k)) * ‖F (qp h' k w) - 1‖
      ≤ Real.exp (π * w.re / (12 * k)) * ∑' m : ℕ, (p (m + 1) : ℝ) * ‖qp h' k w‖ ^ (m + 1) := by gcongr
    _ = ∑' m : ℕ, Real.exp (π * w.re / (12 * k)) * ((p (m + 1) : ℝ) * ‖qp h' k w‖ ^ (m + 1)) :=
        (tsum_mul_left).symm
    _ ≤ ∑' m : ℕ, Real.exp (π / 12) * ((p (m + 1) : ℝ) * Real.exp (-(2 * π * (m + 1)))) := by
        refine (hsum.mul_left _).tsum_le_tsum (fun m => ?_) (summable_S0.mul_left _)
        rw [hnq]; exact term_le hk hw m
    _ = Real.exp (π / 12) * S0 := by rw [tsum_mul_left]; rfl

/-- **the pointwise bound** `‖E_z(z)‖ ≤ CE(n) |z|^{1/2}` where `Re(1/z) ≥ k` and `|z| ≤ 1/k`. -/
lemma norm_Ez_le {h' : ℤ} {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) {z : ℂ} (hz0 : z ≠ 0)
    (hre : (k : ℝ) ≤ (1 / z).re) (hzk : ‖z‖ ≤ 1 / k) :
    ‖Ez h' k n z‖ ≤ CE n * ‖z‖ ^ (1 / 2 : ℝ) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set w : ℂ := 1 / z with hw
  have hw0 : w ≠ 0 := one_div_ne_zero hz0
  have hnw : ‖w‖ = ‖z‖⁻¹ := by rw [hw, norm_div, norm_one, one_div]
  unfold Ez Ef Wf
  rw [← hw]
  have hsplit : cexp (π / (12 * k) * w + 2 * π / k * ((n : ℂ) - 1 / 24) / w) =
      cexp (π / (12 * k) * w) * cexp (2 * π / k * ((n : ℂ) - 1 / 24) / w) := Complex.exp_add _ _
  rw [hsplit]
  have h1 : ‖w ^ (-(5 / 2 : ℂ))‖ = ‖z‖ ^ (5 / 2 : ℝ) := by
    rw [norm_cpow_of_ne_zero hw0, hnw]
    simp only [neg_im, div_ofNat_im, re_ofNat, im_ofNat, zero_div, neg_zero, mul_zero, Real.exp_zero, div_one,
      neg_re, div_ofNat_re]
    rw [Real.inv_rpow hzpos.le, ← Real.rpow_neg hzpos.le, neg_neg]
    try norm_num
  have h2 : ‖cexp (2 * π / k * ((n : ℂ) - 1 / 24) / w)‖ ≤ Real.exp (2 * π * n) := by
    rw [norm_exp, Real.exp_le_exp]
    have e : 2 * π / k * ((n : ℂ) - 1 / 24) / w = ((2 * π / k * ((n : ℝ) - 1 / 24) : ℝ) : ℂ) * z := by
      rw [hw]; push_cast; field_simp
    rw [e, re_ofReal_mul]
    have hb0 : 0 ≤ 2 * π / k * ((n : ℝ) - 1 / 24) := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ (n : ℝ) - 1 / 24 := by linarith
      positivity
    calc 2 * π / k * ((n : ℝ) - 1 / 24) * z.re ≤ 2 * π / k * ((n : ℝ) - 1 / 24) * ‖z‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hb0
      _ ≤ 2 * π / k * ((n : ℝ) - 1 / 24) * (1 / k) := mul_le_mul_of_nonneg_left hzk hb0
      _ ≤ 2 * π * n := by
          have hkk : (0 : ℝ) < k := by linarith
          have e2 : 2 * π / k * ((n : ℝ) - 1 / 24) * (1 / k) = 2 * π * ((n : ℝ) - 1 / 24) / (k * k) := by
            field_simp
          rw [e2, div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (k : ℝ) * k := by nlinarith
          have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * π * n)]
  have h3 := norm_expF_le (h' := h') hk hre
  have h4 : ‖I / z ^ 2‖ = ‖z‖⁻¹ ^ 2 := by rw [norm_div, Complex.norm_I, norm_pow, one_div, inv_pow]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, h1, h4]
  calc ‖z‖ ^ (5 / 2 : ℝ) * (‖cexp (π / (12 * k) * w)‖ * ‖cexp (2 * π / k * ((n : ℂ) - 1 / 24) / w)‖) *
        ‖F (qp h' k w) - 1‖ * ‖z‖⁻¹ ^ 2
      = (‖z‖ ^ (5 / 2 : ℝ) * ‖z‖⁻¹ ^ 2) * ‖cexp (2 * π / k * ((n : ℂ) - 1 / 24) / w)‖ *
        (‖cexp (π / (12 * k) * w)‖ * ‖F (qp h' k w) - 1‖) := by ring
    _ ≤ (‖z‖ ^ (5 / 2 : ℝ) * ‖z‖⁻¹ ^ 2) * Real.exp (2 * π * n) * (Real.exp (π / 12) * S0) := by
        gcongr
    _ = CE n * ‖z‖ ^ (1 / 2 : ℝ) := by
        have : ‖z‖ ^ (5 / 2 : ℝ) * ‖z‖⁻¹ ^ 2 = ‖z‖ ^ (1 / 2 : ℝ) := by
          rw [show (5 / 2 : ℝ) = 1 / 2 + 2 by norm_num, Real.rpow_add hzpos, Real.rpow_two, inv_pow,
            mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hzpos.ne'), mul_one]
        rw [this, CE, Real.exp_add]; ring

/-! ### geometry -/

/-- `z(u) = 1/(k + iu)`. -/
def zp (k : ℕ) (u : ℝ) : ℂ := 1 / ((k : ℂ) + u * I)

lemma zp_re (k : ℕ) (u : ℝ) : (zp k u).re = k / ((k : ℝ) ^ 2 + u ^ 2) := by
  rw [zp, one_div, inv_re, Complex.normSq_apply]; simp; ring_nf

lemma norm_zp_sq {k : ℕ} (hk : 0 < k) (u : ℝ) : ‖zp k u‖ ^ 2 = 1 / ((k : ℝ) ^ 2 + u ^ 2) := by
  rw [zp, norm_div, norm_one, div_pow, normSq_wk]; ring

lemma hasDerivAt_zp {k : ℕ} (hk : 0 < k) (u : ℝ) : HasDerivAt (zp k) (-I / ((k : ℂ) + u * I) ^ 2) u := by
  have hw := wk_ne hk u
  have h1 : HasDerivAt (fun u : ℝ => (k : ℂ) + u * I) I u := by
    simpa using ((hasDerivAt_id u).ofReal_comp.mul_const I).const_add (k : ℂ)
  have h2 := ((hasDerivAt_inv hw).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u h1
  convert h2 using 1
  · funext v; simp [zp, Function.comp]
  · simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring

/-- the closed Ford disc in `z`. -/
lemma zp_mem_disc {k : ℕ} (hk : 0 < k) (u : ℝ) :
    zp k u ∈ closedBall ((1 / (2 * k) : ℝ) : ℂ) (1 / (2 * k)) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [mem_closedBall, dist_eq_norm]
  have hq : 0 < (k : ℝ) ^ 2 + u ^ 2 := by positivity
  have hsq : ‖zp k u - ((1 / (2 * k) : ℝ) : ℂ)‖ ^ 2 = (1 / (2 * k)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre := zp_re k u
    have him : (zp k u).im = -u / ((k : ℝ) ^ 2 + u ^ 2) := by
      rw [zp, one_div, inv_im, Complex.normSq_apply]; simp; ring_nf
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, hre, him]
    field_simp
    ring
  exact le_of_eq ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq)

lemma disc_props {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ∈ closedBall ((1 / (2 * k) : ℝ) : ℂ) (1 / (2 * k)))
    (hz0 : z ≠ 0) : (k : ℝ) ≤ (1 / z).re ∧ ‖z‖ ≤ 1 / k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [mem_closedBall, dist_eq_norm] at hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h2 : ‖z - ((1 / (2 * k) : ℝ) : ℂ)‖ ^ 2 ≤ (1 / (2 * k)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero] at h2
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : (k : ℝ) * ‖z‖ ^ 2 ≤ z.re := by
    rw [hn2]
    have : (z.re - 1 / (2 * k)) ^ 2 + z.im ^ 2 ≤ (1 / (2 * k)) ^ 2 := by nlinarith
    have e : (z.re - 1 / (2 * k)) ^ 2 + z.im ^ 2 - (1 / (2 * k)) ^ 2 = (z.re ^ 2 + z.im ^ 2) - z.re / k := by
      field_simp; ring
    have : (z.re ^ 2 + z.im ^ 2) ≤ z.re / k := by linarith
    rw [le_div_iff₀ hkr] at this; linarith
  constructor
  · rw [one_div, inv_re, Complex.normSq_eq_norm_sq, le_div_iff₀ (by positivity)]
    linarith
  · have : ‖z‖ ^ 2 ≤ ‖z‖ / k := by
      have := (Complex.re_le_norm z)
      rw [le_div_iff₀ hkr]; nlinarith
    rw [le_div_iff₀ hkr]
    have h3 : ‖z‖ * ‖z‖ ≤ ‖z‖ * (1 / k) := by
      rw [← pow_two, mul_one_div]; exact this
    have := le_of_mul_le_mul_left h3 hpos
    rw [le_div_iff₀ hkr] at this; linarith

lemma mem_bigBall {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {z : ℂ} (hre : ρ ≤ z.re) (hz : ‖z‖ ≤ 1) :
    z ∈ ball ((2 / ρ : ℝ) : ℂ) (2 / ρ - ρ / 2) := by
  rw [mem_ball, dist_eq_norm]
  set R := 2 / ρ with hR
  have hR2 : R * ρ = 2 := by rw [hR]; field_simp
  have hpos : 0 < R - ρ / 2 := by
    have : 2 ≤ R := by rw [hR, le_div_iff₀ hρ]; linarith
    linarith
  have hsq : ‖z - (R : ℂ)‖ ^ 2 < (R - ρ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    have hn2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [Complex.sq_norm, Complex.normSq_apply] at this; nlinarith
    have : R * ρ ≤ R * z.re := mul_le_mul_of_nonneg_left hre (by linarith)
    nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hpos.le two_ne_zero).mp hsq

lemma bigBall_re {ρ : ℝ} {z : ℂ} (hz : z ∈ ball ((2 / ρ : ℝ) : ℂ) (2 / ρ - ρ / 2)) : ρ / 2 < z.re := by
  rw [mem_ball, dist_eq_norm] at hz
  have := abs_re_le_norm (z - ((2 / ρ : ℝ) : ℂ))
  rw [sub_re, ofReal_re] at this
  have := abs_lt.mp (lt_of_le_of_lt this hz)
  linarith

/-- **the chord estimate**. -/
theorem err_bound {k n kp kn N : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (hN : 1 ≤ N) (hkN : k ≤ N) (hkp1 : kp ≤ N)
    (hkn1 : kn ≤ N) (hkp : N < k + kp) (hkn : N < k + kn) (h' : ℤ) :
    ‖∫ u in (-(kp : ℝ))..(kn : ℝ), Ef h' k n ((k : ℂ) + u * I)‖ ≤
      CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkNr : (k : ℝ) ≤ N := by exact_mod_cast hkN
  set ρ : ℝ := 1 / (2 * N ^ 2) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one (by positivity)]; nlinarith
  set B := ball ((2 / ρ : ℝ) : ℂ) (2 / ρ - ρ / 2) with hB
  have hBre : ∀ z ∈ B, 0 < z.re := fun z hz => by have := bigBall_re hz; linarith
  have hdiff : DifferentiableOn ℂ (Ez h' k n) B := fun z hz =>
    (differentiableAt_Ez hk (hBre z hz)).differentiableWithinAt
  obtain ⟨P, hP⟩ := hdiff.isExactOn_ball
  -- endpoints
  set z₁ := zp k (-(kp : ℝ)) with hz₁
  set z₂ := zp k (kn : ℝ) with hz₂
  have hzN : ∀ K : ℕ, K ≤ N → N < k + K → ‖zp k K‖ ≤ √2 / N ∧ ρ ≤ (zp k K).re := by
    intro K hK1 hK
    have hKr : (K : ℝ) ≤ N := by exact_mod_cast hK1
    have hlow : (N : ℝ) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + K ^ 2 := by
      have : (N : ℝ) < k + K := by exact_mod_cast hK
      nlinarith [sq_nonneg ((k : ℝ) - K), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    constructor
    · have h2 : ‖zp k K‖ ^ 2 ≤ (√2 / N) ^ 2 := by
        rw [norm_zp_sq hk, div_pow, Real.sq_sqrt (by norm_num), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    · rw [zp_re, hρ, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hz₁b : ‖z₁‖ ≤ √2 / N ∧ ρ ≤ z₁.re := by
    have := hzN kp hkp1 hkp
    have e : zp k (-(kp : ℝ)) = (starRingEnd ℂ) (zp k kp) := by
      simp [zp]
    rw [hz₁, e, Complex.norm_conj, conj_re]; exact this
  have hz₂b := hzN kn hkn1 hkn
  -- the arc integral
  have harc : ∫ u in (-(kp : ℝ))..(kn : ℝ), Ef h' k n ((k : ℂ) + u * I) = P z₂ - P z₁ := by
    have e : ∀ u : ℝ, Ef h' k n ((k : ℂ) + u * I) = Ez h' k n (zp k u) * (-I / ((k : ℂ) + u * I) ^ 2) := by
      intro u
      have hw := wk_ne hk u
      unfold Ez zp
      rw [one_div_one_div]
      field_simp
      rw [I_sq]; ring
    simp only [e]
    refine integral_eq_of_primitive hP (by linarith [(Nat.cast_nonneg kp : (0 : ℝ) ≤ kp),
      (Nat.cast_nonneg kn : (0 : ℝ) ≤ kn)]) (hasDerivAt_zp hk) (fun u hu => ?_) ?_
    · refine mem_bigBall hρ0 hρ1 ?_ ?_
      · rw [zp_re, hρ, div_le_div_iff₀ (by positivity) (by positivity)]
        have hu2 : u ^ 2 ≤ (N : ℝ) ^ 2 := by
          have h1 : -(N : ℝ) ≤ u := by linarith [hu.1, (show (kp : ℝ) ≤ N by exact_mod_cast hkp1)]
          have h2 : u ≤ N := by linarith [hu.2, (show (kn : ℝ) ≤ N by exact_mod_cast hkn1)]
          nlinarith
        nlinarith
      · have h2 : ‖zp k u‖ ^ 2 ≤ 1 := by
          rw [norm_zp_sq hk, div_le_one (by positivity)]; nlinarith [sq_nonneg u]
        nlinarith [norm_nonneg (zp k u)]
    · intro u hu
      have hzu : 0 < (zp k u).re := by rw [zp_re]; positivity
      exact ((differentiableAt_Ez hk hzu).continuousAt.comp (hasDerivAt_zp hk u).continuousAt).mul
        (by exact (continuousAt_const.div (by fun_prop) (pow_ne_zero _ (wk_ne hk u)))) |>.continuousWithinAt
  -- the chord
  set γ : ℝ → ℂ := fun t => z₁ + t * (z₂ - z₁) with hγ
  have hγmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall ((1 / (2 * k) : ℝ) : ℂ) (1 / (2 * k)) := by
    intro t ht
    have := (convex_closedBall ((1 / (2 * k) : ℝ) : ℂ) (1 / (2 * k))).add_smul_sub_mem
      (zp_mem_disc hk (-(kp : ℝ))) (zp_mem_disc hk (kn : ℝ)) ht
    simpa [hγ, Complex.real_smul] using this
  have hγre : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ (γ t).re := by
    intro t ht
    simp only [hγ, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_re]
    nlinarith [ht.1, ht.2, hz₁b.2, hz₂b.2]
  have hγnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ √2 / N := by
    intro t ht
    have e : γ t = (1 - t : ℝ) • z₁ + (t : ℝ) • z₂ := by simp [hγ, Complex.real_smul]; ring
    rw [e]
    calc ‖(1 - t : ℝ) • z₁ + (t : ℝ) • z₂‖ ≤ ‖(1 - t : ℝ) • z₁‖ + ‖(t : ℝ) • z₂‖ := norm_add_le _ _
      _ = (1 - t) * ‖z₁‖ + t * ‖z₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]), Real.norm_of_nonneg ht.1]
      _ ≤ (1 - t) * (√2 / N) + t * (√2 / N) :=
          add_le_add (mul_le_mul_of_nonneg_left hz₁b.1 (by linarith [ht.2])) (mul_le_mul_of_nonneg_left hz₂b.1 ht.1)
      _ = √2 / N := by ring
  have hchord : ∫ t in (0 : ℝ)..1, Ez h' k n (γ t) * (z₂ - z₁) = P z₂ - P z₁ := by
    have := integral_eq_of_primitive (γ := γ) (γ' := fun _ => z₂ - z₁) hP zero_le_one
      (fun t => by
        have h := ((hasDerivAt_id t).ofReal_comp.mul_const (z₂ - z₁)).const_add z₁
        convert h using 1
        simp)
      (fun t ht => mem_bigBall hρ0 hρ1 (hγre t ht) (by
        have hne : γ t ≠ 0 := fun h0 => by have := hγre t ht; rw [h0] at this; simp at this; linarith
        have := (disc_props hk (hγmem t ht) hne).2
        have : (1 : ℝ) / k ≤ 1 := by rw [div_le_one (by positivity)]; exact hkr
        linarith)) ?_
    · simpa [hγ] using this
    · intro t ht
      have hre : 0 < (γ t).re := lt_of_lt_of_le hρ0 (hγre t ht)
      exact (((differentiableAt_Ez hk hre).continuousAt.comp
        (by simp only [hγ]; fun_prop : ContinuousAt γ t)).mul continuousAt_const).continuousWithinAt
  rw [harc, ← hchord]
  have hlen : ‖z₂ - z₁‖ ≤ 2 * √2 / N := by
    calc ‖z₂ - z₁‖ ≤ ‖z₂‖ + ‖z₁‖ := norm_sub_le _ _
      _ ≤ √2 / N + √2 / N := add_le_add hz₂b.1 hz₁b.1
      _ = _ := by ring
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖Ez h' k n (γ t) * (z₂ - z₁)‖ ≤
      CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hne : γ t ≠ 0 := fun h0 => by have := hγre t ht'; rw [h0] at this; simp at this; linarith
    obtain ⟨h1, h2⟩ := disc_props hk (hγmem t ht') hne
    have hE := norm_Ez_le (h' := h') hk hn hne h1 h2
    have hCE : 0 ≤ CE n := mul_nonneg (Real.exp_pos _).le S0_nonneg
    rw [norm_mul]
    calc ‖Ez h' k n (γ t)‖ * ‖z₂ - z₁‖ ≤ (CE n * ‖γ t‖ ^ (1 / 2 : ℝ)) * (2 * √2 / N) :=
          mul_le_mul hE hlen (norm_nonneg _) (by positivity)
      _ ≤ (CE n * (√2 / N) ^ (1 / 2 : ℝ)) * (2 * √2 / N) := by
          gcongr
          exact hγnorm t ht'
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  simpa using this

end

end Rademacher
