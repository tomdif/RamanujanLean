import RamanujanTau.TheoremA.BinaryEisenstein

/-!
# Pulling level-one polynomials back to level six

Substitution of the proved binary E₄ and E₆ preserves weight and the entire
q-expansion. In characteristic different from two and three, it has no
common projective zero.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

noncomputable def binaryPullback (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![binaryE4 R, binaryE6 R]

theorem binaryEv_pullback {R : Type*} [CommRing R] (P : MvPolynomial (Fin 2) R) :
    binaryEv R (binaryPullback R P) = ModP.ev R P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [binaryPullback, binaryEv, ModP.ev]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, map_mul, hP]
    fin_cases i <;> simp [binaryPullback, ModP.ev, ModP.evVec, binaryEv_E4, binaryEv_E6]

theorem binaryPullback_homogeneous {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin 2) R} {k : ℕ} (hP : ModP.Iso P k) :
    BinaryHomogeneous (binaryPullback R P) k := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro s hs
  rw [ModP.monomial_eq_two]
  simp only [map_mul, map_pow, binaryPullback, aeval_C, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hw : 4 * s 0 + 6 * s 1 = k := by
    simpa only [ModP.weight_wt] using hP (mem_support_iff.mp hs)
  have hh := ((binaryE4_homogeneous R).pow (s 0)).mul
    ((binaryE6_homogeneous R).pow (s 1))
  have hh' : BinaryHomogeneous (binaryE4 R ^ s 0 * binaryE6 R ^ s 1) k := by
    convert hh using 1
    simp only [smul_eq_mul]
    omega
  exact hh'.C_mul _

theorem eval_binaryE4_zero_left {F : Type*} [Field F] (y : F) :
    eval ![0, y] (binaryE4 F) = 3 ^ 6 * y ^ 4 := by
  rw [binaryE4_eq]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem eval_binaryE4_zero_right {F : Type*} [Field F] (x : F) :
    eval ![x, 0] (binaryE4 F) = x ^ 4 := by
  rw [binaryE4_eq]
  simp

theorem eval_binaryE4_diagonal {F : Type*} [Field F] (y : F) :
    eval ![y, y] (binaryE4 F) = 2 ^ 8 * y ^ 4 := by
  rw [binaryE4_eq]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem eval_binaryE4_nine {F : Type*} [Field F] (y : F) :
    eval ![9 * y, y] (binaryE4 F) = 2 ^ 8 * 3 ^ 6 * y ^ 4 := by
  rw [binaryE4_eq]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- No nonzero binary point maps to the origin of the weighted level-one model. -/
theorem binaryEisenstein_common_zero {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x y : F)
    (h4 : eval ![x, y] (binaryE4 F) = 0)
    (h6 : eval ![x, y] (binaryE6 F) = 0) : x = 0 ∧ y = 0 := by
  have hc : (1728 : F) ≠ 0 := by
    have he : (1728 : F) = 2 ^ 6 * 3 ^ 3 := by ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hd := congrArg (eval ![x, y]) (binaryEisenstein_discriminant F)
  simp only [map_sub, map_pow, h4, h6, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), sub_self, map_mul, map_ofNat, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hd
  have hz : x = 0 ∨ y = 0 ∨ x = y ∨ x = 9 * y := by
    simpa only [mul_eq_zero, pow_eq_zero_iff (by decide : 3 ≠ 0),
      pow_eq_zero_iff (by decide : 2 ≠ 0), pow_eq_zero_iff (by decide : 6 ≠ 0),
      hc, false_or, sub_eq_zero, or_assoc] using hd.symm
  rcases hz with hx | hy | hxy | hxy
  · subst x
    rw [eval_binaryE4_zero_left] at h4
    exact ⟨rfl, (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
      ((mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ h3))⟩
  · subst y
    rw [eval_binaryE4_zero_right] at h4
    exact ⟨(pow_eq_zero_iff (by decide : 4 ≠ 0)).mp h4, rfl⟩
  · subst x
    rw [eval_binaryE4_diagonal] at h4
    have hy := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
      ((mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ h2))
    exact ⟨hy, hy⟩
  · subst x
    rw [eval_binaryE4_nine] at h4
    have hy := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
      ((mul_eq_zero.mp h4).resolve_left
        (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)))
    simp [hy]

end RamanujanTau.TheoremA
