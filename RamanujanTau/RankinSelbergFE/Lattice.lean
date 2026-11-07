/-
# Primitive decomposition of the lattice theta function

`ℤ² ∖ 0 ≃ ℕ_{≥1} × {(a,c) coprime}`, `v = k·(a,c)` (`nzEquiv`). For coprime `(a,c)` the matrix
`M = mat (a,c)` of `HoroUnfold` has left column `(a,c)`, so `M⁻¹` has bottom row `(−c, a)` and

    Im(M⁻¹ z) = Im z / |a − c z|² = 1 / Q_z(a,c)                    (`im_inv_mat`).

Hence, in `[0,∞]`,

    Θ(z,t) = 1 + ∑_{(a,c) coprime} H_t(Im(M_{(a,c)}⁻¹ z)),   H_t(Y) = ∑_{k ≥ 1} exp(−π t k² / Y)
                                                                      (`ofReal_Theta`).
-/
import RamanujanTau.RankinSelbergFE.Theta
import RamanujanTau.EisensteinReal.HoroUnfold

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergFE

open Real Filter Topology ModularGroup Matrix
open RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-! ### `ℤ² ∖ 0 ≃ ℕ × copSet` -/

lemma copSet_ne_zero (p : copSet) : (p.1 : ℤ × ℤ) ≠ 0 := by
  intro h
  have h2 : Int.gcd p.1.1 p.1.2 = 1 := p.2
  rw [h] at h2
  simp at h2

/-- `(k, (a,c)) ↦ (k+1)·(a,c)`. -/
def scaleMap (q : ℕ × copSet) : ℤ × ℤ :=
  (((q.1 : ℤ) + 1) * q.2.1.1, ((q.1 : ℤ) + 1) * q.2.1.2)

lemma scaleMap_ne_zero (q : ℕ × copSet) : scaleMap q ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [scaleMap, Prod.fst_zero, Prod.snd_zero, mul_eq_zero] at h1 h2
  have hk : ((q.1 : ℤ) + 1) ≠ 0 := by omega
  apply copSet_ne_zero q.2
  ext
  · simpa [hk] using h1
  · simpa [hk] using h2

lemma gcd_scaleMap (q : ℕ × copSet) :
    Int.gcd (scaleMap q).1 (scaleMap q).2 = q.1 + 1 := by
  simp only [scaleMap]
  rw [Int.gcd_mul_left, show Int.gcd q.2.1.1 q.2.1.2 = 1 from q.2.2]
  simp only [mul_one]
  omega

/-- `ℤ² ∖ 0 ≃ ℕ × {(a,c) coprime}`. -/
noncomputable def nzEquiv : ℕ × copSet ≃ {v : ℤ × ℤ // v ≠ 0} where
  toFun q := ⟨scaleMap q, scaleMap_ne_zero q⟩
  invFun v := (Int.gcd v.1.1 v.1.2 - 1,
    ⟨(v.1.1 / Int.gcd v.1.1 v.1.2, v.1.2 / Int.gcd v.1.1 v.1.2), by
      show Int.gcd _ _ = 1
      refine Int.gcd_div_gcd_div_gcd (Int.gcd_pos_iff.2 ?_)
      by_contra h
      push Not at h
      exact v.2 (Prod.ext h.1 h.2)⟩)
  left_inv q := by
    obtain ⟨k, p⟩ := q
    have hg := gcd_scaleMap (k, p)
    simp only [hg]
    refine Prod.ext (by simp) (Subtype.ext ?_)
    simp only [scaleMap] at hg ⊢
    have hk : ((k : ℤ) + 1) ≠ 0 := by omega
    ext
    · simp only
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      exact Int.mul_ediv_cancel_left _ hk
    · simp only
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      exact Int.mul_ediv_cancel_left _ hk
  right_inv v := by
    obtain ⟨⟨a, c⟩, hv⟩ := v
    have hpos : 0 < Int.gcd a c := Int.gcd_pos_iff.2 (by
      by_contra h; push Not at h; exact hv (Prod.ext h.1 h.2))
    apply Subtype.ext
    simp only [scaleMap]
    rw [show (((Int.gcd a c - 1 : ℕ) : ℤ) + 1) = (Int.gcd a c : ℤ) by omega]
    ext
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left a c)
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right a c)

/-- `∑_{v ∈ ℤ²} F v = F 0 + ∑_{k ≥ 0} ∑_{(a,c) coprime} F((k+1)(a,c))` in `[0,∞]`. -/
lemma tsum_decomp (F : ℤ × ℤ → ℝ≥0∞) :
    ∑' v, F v = F 0 + ∑' (k : ℕ) (p : copSet), F (scaleMap (k, p)) := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0, ← ENNReal.tsum_prod]
  congr 1
  calc _ = ∑' v : ({v : ℤ × ℤ | v ≠ 0} : Set (ℤ × ℤ)), F v := by
          rw [tsum_subtype]
          refine tsum_congr fun v => ?_
          by_cases hv : v = 0 <;> simp [hv]
    _ = _ := (nzEquiv.tsum_eq (fun v : {v : ℤ × ℤ // v ≠ 0} => F v)).symm

/-! ### The inverse matrices -/

lemma inv_mat_10 (p : copSet) : ((mat p)⁻¹ : SL(2, ℤ)) 1 0 = -p.1.2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [mat_apply_10]

lemma inv_mat_11 (p : copSet) : ((mat p)⁻¹ : SL(2, ℤ)) 1 1 = p.1.1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [mat_apply_00]

lemma lq_eq_normSq (z : ℍ) (p : ℤ × ℤ) :
    lq z p = Complex.normSq ((p.1 : ℂ) - p.2 * (z : ℂ)) / z.im := by
  have hy := z.im_pos
  rw [lq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
    Complex.sub_im, Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp
  ring

lemma lq_pos (z : ℍ) (p : ℤ × ℤ) (hp : p ≠ 0) : 0 < lq z p := by
  have hy := z.im_pos
  rcases lt_or_eq_of_le (lq_nonneg z p) with h | h
  · exact h
  · exfalso
    have h' : ((p.1 : ℝ) - p.2 * z.re) ^ 2 / z.im + (p.2 : ℝ) ^ 2 * z.im = 0 := h.symm
    have ha : 0 ≤ ((p.1 : ℝ) - p.2 * z.re) ^ 2 / z.im := by positivity
    have hb : 0 ≤ (p.2 : ℝ) ^ 2 * z.im := by positivity
    have hc : (p.2 : ℝ) ^ 2 * z.im = 0 := by linarith
    have hc2 : (p.2 : ℝ) = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      · exact absurd h hy.ne'
    have ha2 : ((p.1 : ℝ) - p.2 * z.re) ^ 2 / z.im = 0 := by linarith
    rw [hc2, zero_mul, sub_zero, div_eq_zero_iff] at ha2
    have : (p.1 : ℝ) = 0 := by
      rcases ha2 with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      · exact absurd h hy.ne'
    exact hp (Prod.ext (by exact_mod_cast this) (by exact_mod_cast hc2))

/-- `Im(M_{(a,c)}⁻¹ z) = 1 / Q_z(a,c)`. -/
theorem im_inv_mat (p : copSet) (z : ℍ) : ((mat p)⁻¹ • z).im = 1 / lq z p.1 := by
  have hy := z.im_pos
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, inv_mat_10, inv_mat_11,
    lq_eq_normSq]
  have hq : Complex.normSq ((p.1.1 : ℂ) - p.1.2 * (z : ℂ)) ≠ 0 := by
    have := lq_pos z p.1 (copSet_ne_zero p)
    rw [lq_eq_normSq] at this
    exact (div_pos_iff_of_pos_right hy).1 this |>.ne'
  rw [one_div_div]
  congr 1
  congr 1
  push_cast
  ring

lemma lq_scale (z : ℍ) (q : ℕ × copSet) :
    lq z (scaleMap q) = ((q.1 : ℝ) + 1) ^ 2 * lq z q.2.1 := by
  simp only [lq, scaleMap]
  push_cast
  field_simp

/-! ### Theta in terms of primitive vectors -/

/-- `H_t(Y) = ∑_{k ≥ 1} exp(−π t k² / Y)` in `[0, ∞]`. -/
noncomputable def Ht (t Y : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (Real.exp (-π * t * ((k : ℝ) + 1) ^ 2 / Y))

lemma thetaTerm_zero (z : ℍ) (t : ℝ) : thetaTerm z t 0 = 1 := by
  simp [thetaTerm, lq]

/-- **Primitive decomposition**: `Θ(z,t) = 1 + ∑_{(a,c) coprime} H_t(Im(M_{(a,c)}⁻¹ z))`. -/
theorem ofReal_Theta (z : ℍ) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Theta z t) = 1 + ∑' p : copSet, Ht t (((mat p)⁻¹ • z).im) := by
  rw [Theta, ENNReal.ofReal_tsum_of_nonneg (fun p => (thetaTerm_pos z t p).le)
    (summable_thetaTerm z ht), tsum_decomp, thetaTerm_zero, ENNReal.ofReal_one]
  congr 1
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun p => ?_
  refine tsum_congr fun k => ?_
  rw [im_inv_mat, thetaTerm, lq_scale]
  congr 2
  have := lq_pos z p.1 (copSet_ne_zero p)
  field_simp

end RamanujanTau.RankinSelbergFE
