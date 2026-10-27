/-
# The transformation of `F = 1/(q;q)_∞` at the cusp `h/k`

For `k > 0` and `hh' ≡ −1 (mod k)`, there is `ω` with `‖ω‖ = 1` such that, for `Re z > 0`,

  `F(e^{2πi(h+iz)/k}) = ω · √z · e^{π(1/z − z)/(12k)} · F(e^{2πi(h'+i/z)/k})`.

This is `EtaGeneral` at `γ = (h', −(hh'+1)/k; k, −h)` and `τ = (h+iz)/k`; here `γτ = (h'+i/z)/k` and `kτ − h = iz`.
-/
import RamanujanTau.Rademacher.EtaGeneral
import RamanujanTau.HardyRamanujan.Modular

set_option autoImplicit false

namespace Rademacher
open Complex ModularForm MatrixGroups Metric
open scoped Real
open UpperHalfPlane hiding I

noncomputable section

/-- the matrix `(h', −m; k, −h)` with `km = hh' + 1`. -/
def gam (h k h' m : ℤ) (hm : k * m = h * h' + 1) : SL(2, ℤ) :=
  ⟨!![h', -m; k, -h], by rw [Matrix.det_fin_two_of]; linarith⟩

lemma eta_eq_Pq (w : ℂ) : η w = cexp (2 * π * I * w / 24) * HardyRamanujan.Pq (cexp (2 * π * I * w)) := by
  simp only [ModularForm.eta, ModularForm.eta_q_eq_pow, Function.Periodic.qParam, HardyRamanujan.Pq_eq]
  norm_num

lemma cexp_mem_ball {w : ℂ} (hw : 0 < w.im) : cexp (2 * π * I * w) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_exp]
  have : (2 * π * I * w).re = -(2 * π * w.im) := by simp
  rw [this, Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith

lemma sqrt_I_mul {z : ℂ} (hz : 0 < z.re) : sqrt (I * z) = sqrt I * sqrt z := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hlog : log (I * z) = log I + log z := by
    refine (log_mul_eq_add_log_iff I_ne_zero hz0).mpr ?_
    rw [arg_I]
    have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
    rw [abs_lt] at this
    constructor <;> linarith [Real.pi_pos]
  rw [_root_.sqrt_eq_exp (mul_ne_zero I_ne_zero hz0), _root_.sqrt_eq_exp I_ne_zero, _root_.sqrt_eq_exp hz0, hlog,
    add_div, Complex.exp_add]

lemma norm_sqrt_I : ‖sqrt I‖ = 1 := by
  rw [_root_.sqrt_eq_exp I_ne_zero, norm_exp, log_I]
  simp

/-- **the transformation at `h/k`**. -/
theorem F_transform {h k h' : ℤ} (hk : 0 < k) (hdvd : k ∣ h * h' + 1) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ z : ℂ, 0 < z.re →
      HardyRamanujan.F (cexp (2 * π * I * ((h + I * z) / k))) =
        ω * sqrt z * cexp (π * (1 / z - z) / (12 * k)) *
          HardyRamanujan.F (cexp (2 * π * I * ((h' + I / z) / k))) := by
  obtain ⟨m, hm⟩ := hdvd
  set γ := gam h k h' m hm.symm with hγ
  have hc : 0 < γ 1 0 := by simp [hγ, gam]; exact hk
  obtain ⟨ε, hε24, hε⟩ := eta_mob_unit γ hc
  have hεn : ‖ε‖ = 1 := by
    have := congrArg norm hε24
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hph : ‖cexp (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k))‖ = 1 := by
    rw [norm_exp]
    have : (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)).re = 0 := by
      rw [show (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)) = ((2 * π * (h - h' : ℤ) / (24 * k) : ℝ) : ℂ) * I by
        push_cast; ring]
      rw [re_ofReal_mul, Complex.I_re, mul_zero]
    rw [this, Real.exp_zero]
  refine ⟨ε * sqrt I * cexp (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)),
    by rw [norm_mul, norm_mul, hεn, norm_sqrt_I, hph, one_mul, one_mul], fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set τ : ℂ := (h + I * z) / k with hτ
  have hτim : 0 < τ.im := by
    have hτ2 : τ = (h + I * z) / ((k : ℝ) : ℂ) := by rw [hτ]; push_cast; rfl
    rw [hτ2, div_ofReal_im]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [add_im, intCast_im, mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    exact div_pos hz hk'
  have hmob : mob γ τ = (h' + I / z) / k := by
    simp only [mob, hγ, gam, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const]
    rw [hτ]
    have hmc : (k : ℂ) * m = h * h' + 1 := by exact_mod_cast hm.symm
    field_simp
    push_cast
    ring_nf
    rw [I_sq]
    linear_combination (-z) * hmc
  have hlin : lin γ τ = I * z := by
    simp only [lin, hγ, gam, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const]
    rw [hτ]; push_cast; field_simp; ring
  have key := hε τ hτim
  rw [hmob, hlin, eta_eq_Pq, eta_eq_Pq, sqrt_I_mul hz] at key
  have hτ' : 0 < ((h' + I / z) / k : ℂ).im := by rw [← hmob]; exact mob_im_pos γ hτim
  have hP := HardyRamanujan.Pq_ne_zero (cexp_mem_ball hτim)
  have hP' := HardyRamanujan.Pq_ne_zero (cexp_mem_ball hτ')
  unfold HardyRamanujan.F
  -- `F(Q) = ε √i √z e^{2πi(τ − τ')/24} F(Q')`
  have hexp : cexp (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)) * cexp (π * (1 / z - z) / (12 * k)) =
      cexp (2 * π * I * τ / 24) * (cexp (2 * π * I * ((h' + I / z) / k) / 24))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, hτ]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [show ε * sqrt I * cexp (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)) * sqrt z * cexp (π * (1 / z - z) / (12 * k))
      = ε * (sqrt I * sqrt z) * (cexp (2 * π * I * ((h - h' : ℤ) : ℂ) / (24 * k)) * cexp (π * (1 / z - z) / (12 * k)))
      by ring, hexp]
  have hs : sqrt I * sqrt z ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0; have := norm_sqrt_I; rw [h0, norm_zero] at this; exact zero_ne_one this
    · simp only [sqrt]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hz0
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, norm_zero] at hεn; exact zero_ne_one hεn
  have he : cexp (2 * π * I * τ / 24) ≠ 0 := Complex.exp_ne_zero _
  have he' : cexp (2 * π * I * ((h' + I / z) / k) / 24) ≠ 0 := Complex.exp_ne_zero _
  generalize cexp (2 * π * I * τ / 24) = e at key he ⊢
  generalize cexp (2 * π * I * ((h' + I / z) / k) / 24) = e' at key he' ⊢
  generalize HardyRamanujan.Pq (cexp (2 * π * I * τ)) = P at key hP ⊢
  generalize HardyRamanujan.Pq (cexp (2 * π * I * ((h' + I / z) / k))) = P' at key hP' ⊢
  generalize sqrt I * sqrt z = s at key hs ⊢
  have hP'eq : P' = ε * s * (e * P) / e' := by
    rw [eq_div_iff he']; linear_combination key
  rw [hP'eq]
  field_simp

end

end Rademacher
