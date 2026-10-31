import RamanujanTau.Rademacher.EtaGeneral
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Petersson's formula for the eta multiplier, for odd lower-left entry

For `γ = [a b; c d] ∈ SL₂(ℤ)` with `c > 0` odd,

  `η(γz) = (d/c) e(((a+d)c - bd(c²-1) - 3c)/24) √(cz+d) η(z)`.

The proof is a Euclidean recursion through pairs `(c,d)` of odd integers. The square-root branch is
computed in the two cases `d > 0` and `d < 0`, and Jacobi reciprocity gives the sign.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex ModularForm MatrixGroups Rademacher
open scoped Real
open UpperHalfPlane hiding I

noncomputable section

/-- `e(n/24)`. -/
def e24 (n : ℤ) : ℂ := cexp (2 * π * I * n / 24)

lemma e24_add (a b : ℤ) : e24 (a + b) = e24 a * e24 b := by
  unfold e24
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e24_eq_of_dvd {a b : ℤ} (h : (24 : ℤ) ∣ a - b) : e24 a = e24 b := by
  obtain ⟨m, hm⟩ := h
  have ha : a = b + 24 * m := by omega
  rw [ha, e24_add]
  have : e24 (24 * m) = 1 := by
    unfold e24
    have he : (2 * (π : ℂ) * I * ((24 * m : ℤ) : ℂ) / 24) = m * (2 * π * I) := by
      push_cast
      ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
  rw [this, mul_one]

lemma e24_twelve : e24 12 = -1 := by
  unfold e24
  have he : (2 * (π : ℂ) * I * ((12 : ℤ) : ℂ) / 24) = π * I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]

lemma e24_ne_zero (n : ℤ) : e24 n ≠ 0 := Complex.exp_ne_zero _

/-- The arithmetic exponent in Petersson's formula. -/
def petE (a b c d : ℤ) : ℤ := (a + d) * c - b * d * (c ^ 2 - 1) - 3 * c

/-- The value in Petersson's formula. -/
def petVal (γ : SL(2, ℤ)) : ℂ :=
  (jacobiSym (γ 1 1) (γ 1 0).natAbs : ℤ) * e24 (petE (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))

/-- The transformation law with a given constant. -/
def EtaLaw (γ : SL(2, ℤ)) (v : ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → η (mob γ z) = v * sqrt (lin γ z) * η z

/-- The translation. -/
def tr (n : ℤ) : SL(2, ℤ) := ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- `η(z+n) = e(n/24) η(z)`. -/
lemma eta_add_int (n : ℤ) (z : ℂ) : η (z + n) = e24 n * η z := by
  unfold ModularForm.eta
  have hq : ∀ k : ℕ, eta_q k (z + n) = eta_q k z := by
    intro k
    simp only [eta_q_eq_cexp]
    have : (2 * (π : ℂ) * I * ((k : ℂ) + 1) * (z + n)) =
        2 * π * I * (k + 1) * z + (((k + 1 : ℕ) * n : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [hq]
  rw [← mul_assoc]
  congr 1
  unfold e24
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma mob_mul_tr (γ : SL(2, ℤ)) (n : ℤ) (z : ℂ) : mob (γ * tr n) z = mob γ (z + n) := by
  unfold mob
  simp only [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring_nf

lemma lin_mul_tr (γ : SL(2, ℤ)) (n : ℤ) (z : ℂ) : lin (γ * tr n) z = lin γ (z + n) := by
  unfold lin
  simp only [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring

/-- Right multiplication by a translation. -/
lemma EtaLaw.mul_tr {γ : SL(2, ℤ)} {v : ℂ} (h : EtaLaw γ v) (n : ℤ) :
    EtaLaw (γ * tr n) (e24 n * v) := by
  intro z hz
  have hz' : 0 < (z + n).im := by simpa using hz
  rw [mob_mul_tr, lin_mul_tr, h _ hz', eta_add_int]
  ring

lemma tr_mul_tr (m n : ℤ) : tr m * tr n = tr (m + n) := by
  apply Subtype.ext
  change !![1, m; 0, 1] * !![1, n; 0, 1] = !![1, m + n; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

lemma tr_zero : tr 0 = 1 := by
  apply Subtype.ext
  change !![(1 : ℤ), 0; 0, 1] = 1
  simp [Matrix.one_fin_two]

/-- The arithmetic of a right translation, for odd `c`. -/
lemma petVal_mul_tr (γ : SL(2, ℤ)) (n : ℤ) (hc : Odd (γ 1 0)) :
    petVal (γ * tr n) = e24 n * petVal γ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have e00 : (γ * tr n) 0 0 = γ 0 0 := by
    simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (γ * tr n) 0 1 = γ 0 1 + n * γ 0 0 := by
    simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : (γ * tr n) 1 0 = γ 1 0 := by
    simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (γ * tr n) 1 1 = γ 1 1 + n * γ 1 0 := by
    simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  unfold petVal
  rw [e00, e01, e10, e11]
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  have hJ : jacobiSym (d + n * c) c.natAbs = jacobiSym d c.natAbs := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left d]
    congr 1
    obtain ⟨k, hk⟩ : ((c.natAbs : ℕ) : ℤ) ∣ c := Int.natAbs_dvd.mpr dvd_rfl
    have hc' : d + n * c = d + (n * k) * (c.natAbs : ℤ) := by
      conv_lhs => rw [hk]
      ring
    rw [hc', Int.add_mul_emod_self_right]
  rw [hJ, mul_left_comm, ← e24_add]
  congr 1
  apply e24_eq_of_dvd
  obtain ⟨x, hx⟩ := hc
  have hcube : ∀ w : ZMod 24, (2 * w + 1) * ((2 * w + 1) ^ 2 - 1) = 0 := by decide +kernel
  have h24 : (24 : ℤ) ∣ c * (c ^ 2 - 1) := by
    have := hcube (x : ZMod 24)
    rw [hx]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp
    push_cast
    exact this
  obtain ⟨u, hu⟩ := h24
  refine ⟨-(n * (2 * b + n * a) * u), ?_⟩
  unfold petE
  have : c * (c ^ 2 - 1) = 24 * u := hu
  linear_combination (-(n * (2 * b + n * a))) * this - (n * (c ^ 2 - 1)) * hdet

lemma arg_bounds {u : ℂ} (hu : 0 < u.im) : 0 < u.arg ∧ u.arg < Real.pi := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hs : 0 < Real.sin u.arg := by
    have := Complex.norm_mul_sin_arg u
    rw [← this] at hu
    exact (pos_iff_pos_of_mul_pos hu).mp hn
  constructor
  · by_contra h
    exact absurd (Real.sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.mp h)
      (Complex.neg_pi_lt_arg u).le) (not_le.mpr hs)
  · rcases (Complex.arg_le_pi u).lt_or_eq with h | h
    · exact h
    · rw [h, Real.sin_pi] at hs
      exact absurd hs (lt_irrefl _)

lemma sin_add_arg (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) :
    ‖u‖ * ‖z‖ * Real.sin (u.arg + z.arg) = (u * z).im := by
  have h1 := Complex.norm_mul_sin_arg u
  have h2 := Complex.norm_mul_sin_arg z
  have h3 := Complex.norm_mul_cos_arg u
  have h4 := Complex.norm_mul_cos_arg z
  rw [Complex.mul_im, Real.sin_add, ← h1, ← h2, ← h3, ← h4]
  ring

lemma sqrt_exp_half {w : ℂ} (hw : w ≠ 0) : sqrt w = cexp (log w / 2) := sqrt_eq_exp hw

/-- If `u, z, uz` lie in the upper half-plane then principal square roots multiply. -/
lemma sqrt_mul_of_im_pos {u z : ℂ} (hu : 0 < u.im) (hz : 0 < z.im) (huz : 0 < (u * z).im) :
    sqrt u * sqrt z = sqrt (u * z) := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨a0, a1⟩ := arg_bounds hu
  obtain ⟨b0, b1⟩ := arg_bounds hz
  have hsin : 0 < Real.sin (u.arg + z.arg) := by
    have := sin_add_arg u z hu0 hz0
    rw [← this] at huz
    exact (pos_iff_pos_of_mul_pos huz).mp (mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hz0))
  have hlt : u.arg + z.arg < Real.pi := by
    by_contra h
    push Not at h
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := u.arg + z.arg - 2 * Real.pi)
      (by linarith) (by linarith)
    rw [Real.sin_sub_two_pi] at this
    exact absurd hsin (not_lt.mpr this)
  have hlog : log (u * z) = log u + log z := by
    have hexp : cexp (log u + log z) = u * z := by
      rw [Complex.exp_add, Complex.exp_log hu0, Complex.exp_log hz0]
    rw [← hexp, Complex.log_exp]
    · simp only [add_im, log_im]
      linarith [Real.pi_pos]
    · simp only [add_im, log_im]
      linarith
  rw [sqrt_exp_half hu0, sqrt_exp_half hz0, sqrt_exp_half (mul_ne_zero hu0 hz0), hlog,
    ← Complex.exp_add]
  congr 1
  ring

/-- If `u, z, w` lie in the upper half-plane with `uz = -w`, the square roots differ by `I`. -/
lemma sqrt_mul_of_eq_neg {u z w : ℂ} (hu : 0 < u.im) (hz : 0 < z.im) (hw : 0 < w.im)
    (huz : u * z = -w) : sqrt u * sqrt z = I * sqrt w := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  obtain ⟨a0, a1⟩ := arg_bounds hu
  obtain ⟨b0, b1⟩ := arg_bounds hz
  have him : (u * z).im < 0 := by rw [huz]; simpa using hw
  have hsin : Real.sin (u.arg + z.arg) < 0 := by
    have := sin_add_arg u z hu0 hz0
    rw [← this] at him
    have hp : 0 < ‖u‖ * ‖z‖ := mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hz0)
    by_contra h
    exact absurd (mul_nonneg hp.le (not_lt.mp h)) (not_le.mpr him)
  have hgt : Real.pi < u.arg + z.arg := by
    by_contra h
    exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (not_lt.mp h)) (not_le.mpr hsin)
  have hlog : log w = log u + log z - Real.pi * I := by
    have hexp : cexp (log u + log z - Real.pi * I) = w := by
      rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hu0, Complex.exp_log hz0, huz,
        Complex.exp_pi_mul_I]
      simp
    rw [← hexp, Complex.log_exp]
    · simp only [sub_im, add_im, log_im, mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
      linarith [Real.pi_pos]
    · simp only [sub_im, add_im, log_im, mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
      linarith
  have hI : I = cexp (Real.pi * I / 2) := by
    have : (Real.pi : ℂ) * I / 2 = ((Real.pi / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  rw [sqrt_exp_half hu0, sqrt_exp_half hz0, sqrt_exp_half hw0, hlog]
  have h2 : cexp (Real.pi * I / 2) * cexp ((log u + log z - Real.pi * I) / 2) =
      cexp (log u / 2) * cexp (log z / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [← h2, ← hI]

lemma sqrt_I_eq : sqrt I = e24 3 := by
  rw [sqrt_exp_half I_ne_zero, Complex.log_I]
  unfold e24
  congr 1
  push_cast
  ring

/-- `S = [0 -1; 1 0]`. -/
def sS : SL(2, ℤ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- `S⁻¹ = [0 1; -1 0]`. -/
def sI : SL(2, ℤ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

lemma sS_mul_sI : sS * sI = 1 := by
  apply Subtype.ext
  change !![(0 : ℤ), -1; 1, 0] * !![0, 1; -1, 0] = 1
  rw [Matrix.mul_fin_two]
  simp [Matrix.one_fin_two]

lemma sI_mul_sS : sI * sS = 1 := by
  apply Subtype.ext
  change !![(0 : ℤ), 1; -1, 0] * !![0, -1; 1, 0] = 1
  rw [Matrix.mul_fin_two]
  simp [Matrix.one_fin_two]

section Entries
variable (γ : SL(2, ℤ))

lemma sS_00 : (γ * sS) 0 0 = γ 0 1 := by simp [sS, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sS_01 : (γ * sS) 0 1 = -γ 0 0 := by simp [sS, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sS_10 : (γ * sS) 1 0 = γ 1 1 := by simp [sS, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sS_11 : (γ * sS) 1 1 = -γ 1 0 := by simp [sS, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sI_00 : (γ * sI) 0 0 = -γ 0 1 := by simp [sI, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sI_01 : (γ * sI) 0 1 = γ 0 0 := by simp [sI, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sI_10 : (γ * sI) 1 0 = -γ 1 1 := by simp [sI, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma sI_11 : (γ * sI) 1 1 = γ 1 0 := by simp [sI, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

end Entries

lemma neg_inv_im {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hn : 0 < normSq z := Complex.normSq_pos.mpr hz0
  simp only [neg_div, one_div, neg_im, inv_im, neg_neg]
  exact div_pos hz hn

/-- The action through `S`. -/
lemma mob_comp (γ : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) (δ : SL(2, ℤ))
    (h00 : δ 0 0 = γ 0 1) (h01 : δ 0 1 = -γ 0 0) (h10 : δ 1 0 = γ 1 1) (h11 : δ 1 1 = -γ 1 0) :
    mob δ z = mob γ (-1 / z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hd := denom_ne_zero' δ hz
  have hd2 := denom_ne_zero' γ (neg_inv_im hz)
  unfold mob
  rw [div_eq_div_iff hd hd2, h00, h01, h10, h11]
  push_cast
  field_simp
  ring

lemma mob_comp' (γ : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) (δ : SL(2, ℤ))
    (h00 : δ 0 0 = -γ 0 1) (h01 : δ 0 1 = γ 0 0) (h10 : δ 1 0 = -γ 1 1) (h11 : δ 1 1 = γ 1 0) :
    mob δ z = mob γ (-1 / z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hd := denom_ne_zero' δ hz
  have hd2 := denom_ne_zero' γ (neg_inv_im hz)
  unfold mob
  rw [div_eq_div_iff hd hd2, h00, h01, h10, h11]
  push_cast
  field_simp
  ring

lemma eta_S (z : ℂ) (hz : 0 < z.im) : η (-1 / z) = e24 (-3) * (sqrt z * η z) := by
  have h := eta_comp_eq_csqrt_I_inv (show z ∈ upperHalfPlaneSet from hz)
  have he : e24 (-3) = (sqrt I)⁻¹ := by
    rw [sqrt_I_eq]
    apply eq_inv_of_mul_eq_one_left
    rw [← e24_add]
    simp [e24]
  rw [he]
  simpa using h

lemma lin_im (δ : SL(2, ℤ)) (z : ℂ) : (lin δ z).im = (δ 1 0 : ℝ) * z.im := by
  simp [lin]

/-- Right multiplication by `S`, when `c, d > 0`. -/
lemma EtaLaw.mul_sS {γ : SL(2, ℤ)} {v : ℂ} (h : EtaLaw γ v) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    EtaLaw (γ * sS) (e24 (-3) * v) := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hτ := neg_inv_im hz
  have hcR : (0 : ℝ) < γ 1 0 := by exact_mod_cast hc
  have hdR : (0 : ℝ) < γ 1 1 := by exact_mod_cast hd
  have hu : 0 < (lin γ (-1 / z)).im := by
    simp only [lin, add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    exact mul_pos hcR hτ
  have hw : lin γ (-1 / z) * z = lin (γ * sS) z := by
    simp only [lin, sS_10, sS_11]
    push_cast
    field_simp
    ring
  have hwim : 0 < (lin γ (-1 / z) * z).im := by
    rw [hw, lin_im, sS_10]
    exact mul_pos hdR hz
  rw [mob_comp γ z hz _ (sS_00 γ) (sS_01 γ) (sS_10 γ) (sS_11 γ), h _ hτ, eta_S z hz, ← hw,
    ← sqrt_mul_of_im_pos hu hz hwim]
  ring

/-- Right multiplication by `S⁻¹`, when `c > 0 > d`. -/
lemma EtaLaw.mul_sI {γ : SL(2, ℤ)} {v : ℂ} (h : EtaLaw γ v) (hc : 0 < γ 1 0) (hd : γ 1 1 < 0) :
    EtaLaw (γ * sI) (e24 3 * v) := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hτ := neg_inv_im hz
  have hcR : (0 : ℝ) < γ 1 0 := by exact_mod_cast hc
  have hdR : (γ 1 1 : ℝ) < 0 := by exact_mod_cast hd
  have hu : 0 < (lin γ (-1 / z)).im := by
    simp only [lin, add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    exact mul_pos hcR hτ
  have hwim : 0 < (lin (γ * sI) z).im := by
    rw [lin_im, sI_10]
    push_cast
    exact mul_pos (neg_pos.mpr hdR) hz
  have hw : lin γ (-1 / z) * z = -lin (γ * sI) z := by
    simp only [lin, sI_10, sI_11]
    push_cast
    field_simp
    ring
  have hroot := sqrt_mul_of_eq_neg hu hz hwim hw
  have hI : e24 (-3) * I = e24 3 := by
    have h1 : sqrt I * sqrt I = I := by
      rw [sqrt_exp_half I_ne_zero, ← Complex.exp_add, add_halves, Complex.exp_log I_ne_zero]
    rw [sqrt_I_eq] at h1
    rw [← h1, ← mul_assoc, ← e24_add]
    have : e24 (-3 + 3) = 1 := by simp [e24]
    rw [this, one_mul]
  rw [mob_comp' γ z hz _ (sI_00 γ) (sI_01 γ) (sI_10 γ) (sI_11 γ), h _ hτ, eta_S z hz, ← hI]
  calc v * sqrt (lin γ (-1 / z)) * (e24 (-3) * (sqrt z * η z))
      = v * e24 (-3) * (sqrt (lin γ (-1 / z)) * sqrt z) * η z := by ring
    _ = _ := by rw [hroot]; ring

/-- The congruence for a right multiplication by `S`. -/
lemma cong_pos (a b x y : ℤ) (h : a * (2 * y + 1) - b * (2 * x + 1) = 1) :
    (24 : ℤ) ∣ petE a b (2 * x + 1) (2 * y + 1) - 3 -
      petE b (-a) (2 * y + 1) (-(2 * x + 1)) - 12 * (y * (x + 1)) := by
  have h8 : ∀ a b x y : ZMod 8, a * (2 * y + 1) - b * (2 * x + 1) = 1 →
      ((a + (2 * y + 1)) * (2 * x + 1) - b * (2 * y + 1) * ((2 * x + 1) ^ 2 - 1) - 3 * (2 * x + 1)) - 3 -
      ((b + -(2 * x + 1)) * (2 * y + 1) - (-a) * (-(2 * x + 1)) * ((2 * y + 1) ^ 2 - 1) - 3 * (2 * y + 1)) -
      12 * (y * (x + 1)) = 0 := by decide +kernel
  have h3 : ∀ a b x y : ZMod 3, a * (2 * y + 1) - b * (2 * x + 1) = 1 →
      ((a + (2 * y + 1)) * (2 * x + 1) - b * (2 * y + 1) * ((2 * x + 1) ^ 2 - 1) - 3 * (2 * x + 1)) - 3 -
      ((b + -(2 * x + 1)) * (2 * y + 1) - (-a) * (-(2 * x + 1)) * ((2 * y + 1) ^ 2 - 1) - 3 * (2 * y + 1)) -
      12 * (y * (x + 1)) = 0 := by decide +kernel
  have d8 := h8 a b x y (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h)
  have d3 := h3 a b x y (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h)
  have e8 : (8 : ℤ) ∣ petE a b (2 * x + 1) (2 * y + 1) - 3 -
      petE b (-a) (2 * y + 1) (-(2 * x + 1)) - 12 * (y * (x + 1)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    unfold petE
    push_cast
    exact d8
  have e3 : (3 : ℤ) ∣ petE a b (2 * x + 1) (2 * y + 1) - 3 -
      petE b (-a) (2 * y + 1) (-(2 * x + 1)) - 12 * (y * (x + 1)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    unfold petE
    push_cast
    exact d3
  omega

/-- The congruence for a right multiplication by `S⁻¹`; here `d = -(2y+1)`. -/
lemma cong_neg (a b x y : ℤ) (h : a * (-(2 * y + 1)) - b * (2 * x + 1) = 1) :
    (24 : ℤ) ∣ petE a b (2 * x + 1) (-(2 * y + 1)) + 3 -
      petE (-b) a (2 * y + 1) (2 * x + 1) - 12 * (x * (y + 1)) := by
  have h8 : ∀ a b x y : ZMod 8, a * (-(2 * y + 1)) - b * (2 * x + 1) = 1 →
      ((a + -(2 * y + 1)) * (2 * x + 1) - b * (-(2 * y + 1)) * ((2 * x + 1) ^ 2 - 1) - 3 * (2 * x + 1)) + 3 -
      ((-b + (2 * x + 1)) * (2 * y + 1) - a * (2 * x + 1) * ((2 * y + 1) ^ 2 - 1) - 3 * (2 * y + 1)) -
      12 * (x * (y + 1)) = 0 := by decide +kernel
  have h3 : ∀ a b x y : ZMod 3, a * (-(2 * y + 1)) - b * (2 * x + 1) = 1 →
      ((a + -(2 * y + 1)) * (2 * x + 1) - b * (-(2 * y + 1)) * ((2 * x + 1) ^ 2 - 1) - 3 * (2 * x + 1)) + 3 -
      ((-b + (2 * x + 1)) * (2 * y + 1) - a * (2 * x + 1) * ((2 * y + 1) ^ 2 - 1) - 3 * (2 * y + 1)) -
      12 * (x * (y + 1)) = 0 := by decide +kernel
  have d8 := h8 a b x y (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) h)
  have d3 := h3 a b x y (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h)
  have e8 : (8 : ℤ) ∣ petE a b (2 * x + 1) (-(2 * y + 1)) + 3 -
      petE (-b) a (2 * y + 1) (2 * x + 1) - 12 * (x * (y + 1)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    unfold petE
    push_cast
    exact d8
  have e3 : (3 : ℤ) ∣ petE a b (2 * x + 1) (-(2 * y + 1)) + 3 -
      petE (-b) a (2 * y + 1) (2 * x + 1) - 12 * (x * (y + 1)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    unfold petE
    push_cast
    exact d3
  omega

lemma e24_twelve_mul (k : ℕ) : e24 (12 * k) = (-1) ^ k := by
  induction k with
  | zero => simp [e24]
  | succ k ih =>
    rw [show (12 : ℤ) * ((k + 1 : ℕ) : ℤ) = 12 * k + 12 by push_cast; ring, e24_add, ih, e24_twelve,
      pow_succ]

/-- The sign in `J(-c | d)` against `J(d | c)`. -/
lemma jacobi_sign_pos (x y : ℕ) :
    jacobiSym (-((2 * x + 1 : ℕ) : ℤ)) (2 * y + 1) =
      (-1) ^ (y * (x + 1)) * jacobiSym ((2 * y + 1 : ℕ) : ℤ) (2 * x + 1) := by
  have hdo : Odd (2 * y + 1) := ⟨y, rfl⟩
  have hco : Odd (2 * x + 1) := ⟨x, rfl⟩
  rw [jacobiSym.neg _ hdo]
  rcases Nat.even_or_odd y with hy | hy
  · have h4 : (2 * y + 1) % 4 = 1 := by obtain ⟨u, rfl⟩ := hy; omega
    rw [ZMod.χ₄_nat_one_mod_four h4, one_mul,
      ← jacobiSym.quadratic_reciprocity_one_mod_four h4 hco, hy.mul_right _ |>.neg_one_pow, one_mul]
  · have h4 : (2 * y + 1) % 4 = 3 := by obtain ⟨u, rfl⟩ := hy; omega
    rw [ZMod.χ₄_nat_three_mod_four h4]
    rcases Nat.even_or_odd x with hx | hx
    · have hc4 : (2 * x + 1) % 4 = 1 := by obtain ⟨u, rfl⟩ := hx; omega
      have hpow : Odd (y * (x + 1)) := hy.mul (hx.add_one)
      rw [hpow.neg_one_pow, ← jacobiSym.quadratic_reciprocity_one_mod_four hc4 hdo]
    · have hc4 : (2 * x + 1) % 4 = 3 := by obtain ⟨u, rfl⟩ := hx; omega
      have hpow : Even (y * (x + 1)) := hx.add_one.mul_left y
      rw [hpow.neg_one_pow, jacobiSym.quadratic_reciprocity_three_mod_four hc4 h4]
      ring

/-- The sign in `J(-m | c)` against `J(c | m)`. -/
lemma jacobi_sign_neg (x y : ℕ) :
    jacobiSym (-((2 * y + 1 : ℕ) : ℤ)) (2 * x + 1) =
      (-1) ^ (x * (y + 1)) * jacobiSym ((2 * x + 1 : ℕ) : ℤ) (2 * y + 1) := jacobi_sign_pos y x

lemma natAbs_two_mul (x : ℕ) : (((2 * x + 1 : ℕ) : ℤ)).natAbs = 2 * x + 1 := Int.natAbs_natCast _

/-- The arithmetic of right multiplication by `S`, for `c, d > 0` odd. -/
lemma petVal_sS (γ : SL(2, ℤ)) (x y : ℕ) (hc : γ 1 0 = ((2 * x + 1 : ℕ) : ℤ))
    (hd : γ 1 1 = ((2 * y + 1 : ℕ) : ℤ)) : petVal γ = e24 3 * petVal (γ * sS) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  unfold petVal
  rw [sS_00, sS_01, sS_10, sS_11, hc, hd, natAbs_two_mul, natAbs_two_mul, jacobi_sign_pos]
  have hcong := cong_pos (γ 0 0) (γ 0 1) x y (by rw [hc, hd] at hdet; push_cast at hdet; exact hdet)
  have he : e24 (petE (γ 0 0) (γ 0 1) ((2 * x + 1 : ℕ) : ℤ) ((2 * y + 1 : ℕ) : ℤ)) =
      e24 (3 + petE (γ 0 1) (-γ 0 0) ((2 * y + 1 : ℕ) : ℤ) (-((2 * x + 1 : ℕ) : ℤ)) +
        12 * ((y * (x + 1) : ℕ) : ℤ)) := by
    apply e24_eq_of_dvd
    push_cast
    convert hcong using 1
    ring
  rw [he, e24_add, e24_add, e24_twelve_mul]
  push_cast
  ring

/-- The arithmetic of right multiplication by `S⁻¹`, for `c > 0 > d` odd. -/
lemma petVal_sI (γ : SL(2, ℤ)) (x y : ℕ) (hc : γ 1 0 = ((2 * x + 1 : ℕ) : ℤ))
    (hd : γ 1 1 = -((2 * y + 1 : ℕ) : ℤ)) : petVal γ = e24 (-3) * petVal (γ * sI) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  unfold petVal
  rw [sI_00, sI_01, sI_10, sI_11, hc, hd, natAbs_two_mul, neg_neg, natAbs_two_mul, jacobi_sign_neg]
  have hcong := cong_neg (γ 0 0) (γ 0 1) x y (by rw [hc, hd] at hdet; push_cast at hdet; exact hdet)
  have he : e24 (petE (γ 0 0) (γ 0 1) ((2 * x + 1 : ℕ) : ℤ) (-((2 * y + 1 : ℕ) : ℤ))) =
      e24 (-3 + petE (-γ 0 1) (γ 0 0) ((2 * y + 1 : ℕ) : ℤ) ((2 * x + 1 : ℕ) : ℤ) +
        12 * ((x * (y + 1) : ℕ) : ℤ)) := by
    apply e24_eq_of_dvd
    push_cast
    convert hcong using 1
    ring
  rw [he, e24_add, e24_add, e24_twelve_mul]
  have hs : ((-1 : ℂ) ^ (x * (y + 1))) * (-1) ^ (x * (y + 1)) = 1 := by
    rw [← mul_pow]
    simp
  have key : ∀ J A B t : ℂ, t * t = 1 → (t * J) * (A * B * t) = A * (J * B) := by
    intro J A B t ht
    linear_combination (J * A * B) * ht
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact key _ _ _ _ hs

lemma mul_tr_tr_neg (γ : SL(2, ℤ)) (n : ℤ) : γ * tr n * tr (-n) = γ := by
  rw [mul_assoc, tr_mul_tr, add_neg_cancel, tr_zero, mul_one]

lemma tr_10 (γ : SL(2, ℤ)) (n : ℤ) : (γ * tr n) 1 0 = γ 1 0 := by
  simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma tr_11 (γ : SL(2, ℤ)) (n : ℤ) : (γ * tr n) 1 1 = γ 1 1 + n * γ 1 0 := by
  simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Petersson's formula is unaffected by a right translation. -/
lemma law_of_mul_tr {γ : SL(2, ℤ)} (n : ℤ) (hc : Odd (γ 1 0))
    (h : EtaLaw (γ * tr n) (petVal (γ * tr n))) : EtaLaw γ (petVal γ) := by
  have h2 := h.mul_tr (-n)
  rw [mul_tr_tr_neg, petVal_mul_tr γ n hc, ← mul_assoc, ← e24_add] at h2
  have he : e24 (-n + n) = 1 := by simp [e24]
  rwa [he, one_mul] at h2

/-- The base case `c = 1`, `d = 0`. -/
lemma law_base (γ : SL(2, ℤ)) (hc : γ 1 0 = 1) (hd : γ 1 1 = 0) : EtaLaw γ (petVal γ) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  rw [hc, hd] at hdet
  have hb : γ 0 1 = -1 := by linarith
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hmob : mob γ z = -1 / z + (γ 0 0 : ℤ) := by
    unfold mob
    rw [hc, hd, hb]
    simp only [Int.cast_one, one_mul, Int.cast_zero, add_zero, Int.cast_neg]
    rw [eq_comm, neg_div, neg_add_eq_sub, eq_div_iff hz0, sub_mul, div_mul_cancel₀ _ hz0]
    ring
  have hlin : lin γ z = z := by
    unfold lin
    rw [hc, hd]
    simp
  have hval : petVal γ = e24 (γ 0 0) * e24 (-3) := by
    unfold petVal
    rw [hc, hd, ← e24_add]
    have hJ : jacobiSym 0 (1 : ℤ).natAbs = 1 := by simp
    rw [hJ]
    push_cast
    rw [one_mul]
    congr 1
    unfold petE
    ring
  rw [hmob, hlin, eta_add_int, eta_S z hz, hval]
  ring

/-- **Petersson's formula**, for positive odd lower-left entry. -/
theorem etaLaw_odd : ∀ (c : ℕ) (γ : SL(2, ℤ)), γ 1 0 = c → Odd c → EtaLaw γ (petVal γ) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro γ hc hodd
    have hcpos : 0 < c := hodd.pos
    have hcZ : Odd (γ 1 0) := by rw [hc]; exact_mod_cast hodd
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.property
      rwa [Matrix.det_fin_two] at h
    by_cases hc1 : c = 1
    · subst hc1
      apply law_of_mul_tr (-(γ 1 1)) hcZ
      apply law_base
      · rw [tr_10, hc]; rfl
      · rw [tr_11, hc]; simp
    -- reduce to `d` odd with `|d| < c`
    have hreduce : ∃ n : ℤ, Odd ((γ * tr n) 1 1) ∧ |(γ * tr n) 1 1| < c := by
      obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, Odd (γ 1 1 + n₀ * c) := by
        rcases Int.even_or_odd (γ 1 1) with he | ho
        · refine ⟨1, ?_⟩
          rw [one_mul]
          exact he.add_odd (by exact_mod_cast hodd)
        · exact ⟨0, by simpa using ho⟩
      set d₁ := γ 1 1 + n₀ * c with hd₁
      have h2c : (0 : ℤ) < 2 * c := by positivity
      let r := d₁ % (2 * c)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ h2c.ne'
      have hr1 : r < 2 * c := Int.emod_lt_of_pos _ h2c
      have hrq : d₁ = r + (d₁ / (2 * c)) * (2 * c) := by
        have := Int.emod_add_mul_ediv d₁ (2 * c)
        simp only [r]
        linarith [mul_comm (d₁ / (2 * (c : ℤ))) (2 * (c : ℤ))]
      have hrodd : Odd r := by
        have : r = d₁ - (d₁ / (2 * c)) * (2 * c) := by linarith
        rw [this]
        exact hn₀.sub_even ⟨(d₁ / (2 * c)) * c, by ring⟩
      have hrc : r ≠ c := by
        intro hrc
        apply hc1
        have hdv : (c : ℤ) ∣ d₁ := by
          rw [hrq, hrc]
          exact dvd_add dvd_rfl (Dvd.intro_left _ (by ring : (d₁ / (2 * (c : ℤ)) * 2) * c = _))
        have hdv2 : (c : ℤ) ∣ γ 1 1 := by
          have : γ 1 1 = d₁ - n₀ * c := by rw [hd₁]; ring
          rw [this]
          exact dvd_sub hdv (dvd_mul_left _ _)
        have hone : (c : ℤ) ∣ 1 := by
          rw [← hdet, hc]
          exact dvd_sub (hdv2.mul_left _) (dvd_mul_left _ _)
        exact_mod_cast Nat.dvd_one.mp (by exact_mod_cast hone)
      by_cases hlt : r < c
      · refine ⟨n₀ - (d₁ / (2 * c)) * 2, ?_, ?_⟩
        · rw [tr_11, hc]
          have : γ 1 1 + (n₀ - d₁ / (2 * c) * 2) * c = r := by
            rw [hd₁] at hrq ⊢
            linarith
          rw [this]
          exact hrodd
        · rw [tr_11, hc]
          have : γ 1 1 + (n₀ - d₁ / (2 * c) * 2) * c = r := by
            rw [hd₁] at hrq ⊢
            linarith
          rw [this, abs_of_nonneg hr0]
          exact hlt
      · have hgt : (c : ℤ) < r := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hrc)
        refine ⟨n₀ - (d₁ / (2 * c)) * 2 - 2, ?_, ?_⟩
        · rw [tr_11, hc]
          have : γ 1 1 + (n₀ - d₁ / (2 * c) * 2 - 2) * c = r - 2 * c := by
            rw [hd₁] at hrq ⊢
            linarith
          rw [this]
          exact hrodd.sub_even ⟨c, by ring⟩
        · rw [tr_11, hc]
          have : γ 1 1 + (n₀ - d₁ / (2 * c) * 2 - 2) * c = r - 2 * c := by
            rw [hd₁] at hrq ⊢
            linarith
          rw [this, abs_lt]
          constructor <;> linarith
    obtain ⟨n, hodd', habs⟩ := hreduce
    apply law_of_mul_tr n hcZ
    set δ := γ * tr n with hδ
    have hδc : δ 1 0 = c := by rw [hδ, tr_10, hc]
    obtain ⟨x, hx⟩ := hodd
    have hδ0 : δ 1 1 ≠ 0 := fun h => by simp [h] at hodd'
    rcases lt_or_gt_of_ne hδ0 with hneg | hpos
    · -- `d < 0`: pass to `δ S⁻¹`
      obtain ⟨y, hy⟩ : ∃ y : ℕ, δ 1 1 = -((2 * y + 1 : ℕ) : ℤ) := by
        obtain ⟨u, hu⟩ := hodd'
        refine ⟨(-(u + 1)).toNat, ?_⟩
        have : 0 ≤ -(u + 1) := by omega
        push_cast
        rw [Int.toNat_of_nonneg this, hu]
        ring
      have hlt : 2 * y + 1 < c := by
        rw [hy, abs_neg, abs_of_nonneg (by positivity)] at habs
        exact_mod_cast habs
      have hlaw := ih (2 * y + 1) hlt (δ * sI) (by rw [sI_10, hy, neg_neg]) ⟨y, rfl⟩
      have h2 := hlaw.mul_sS (by rw [sI_10, hy, neg_neg]; positivity)
        (by rw [sI_11, hδc]; exact_mod_cast hcpos)
      rw [mul_assoc, sI_mul_sS, mul_one] at h2
      rw [petVal_sI δ x y (by rw [hδc, hx]) hy]
      exact h2
    · obtain ⟨y, hy⟩ : ∃ y : ℕ, δ 1 1 = ((2 * y + 1 : ℕ) : ℤ) := by
        obtain ⟨u, hu⟩ := hodd'
        refine ⟨u.toNat, ?_⟩
        have : 0 ≤ u := by omega
        push_cast
        rw [Int.toNat_of_nonneg this, hu]
      have hlt : 2 * y + 1 < c := by
        rw [hy, abs_of_nonneg (by positivity)] at habs
        exact_mod_cast habs
      have hlaw := ih (2 * y + 1) hlt (δ * sS) (by rw [sS_10, hy]) ⟨y, rfl⟩
      have h2 := hlaw.mul_sI (by rw [sS_10, hy]; positivity)
        (by rw [sS_11, hδc]; simpa using hcpos)
      rw [mul_assoc, sS_mul_sI, mul_one] at h2
      rw [petVal_sS δ x y (by rw [hδc, hx]) hy]
      exact h2

end

end RamanujanTau.ThetaLift
