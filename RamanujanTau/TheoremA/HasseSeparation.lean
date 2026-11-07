import RamanujanTau.TheoremA.BinaryBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Separation of the Hasse invariant and its companion

Igusa's proved simple-root statements exclude a common zero of A and B in
each weighted projective chart. Scaling extends this to every nonzero point
over an algebraically closed field; the binary pullback preserves this property.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

private lemma square_dvd_of_eval_derivative_eq_zero (f : Polynomial F) (t : F)
    (hf : f ≠ 0) (h0 : f.eval t = 0) (h1 : f.derivative.eval t = 0) :
    (Polynomial.X - Polynomial.C t) ^ 2 ∣ f := by
  apply (Polynomial.le_rootMultiplicity_iff hf).mp
  exact (Polynomial.one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨h0, h1⟩

theorem hasse_companion_chartT_separation (hp5 : 5 ≤ p) (t : F)
    (hA : eval ![t, 1] (Igusa.AF F p hp5) = 0) :
    eval ![t, 1] (Igusa.BF F p hp5) ≠ 0 := by
  intro hB
  have ht : t ^ 3 ≠ 1 := fun ht => Igusa.chartT_ne_of_cube_eq_one hp5 ht hA
  have ha : (Igusa.chartT (Igusa.AF F p hp5)).eval t = 0 := by
    rw [Igusa.eval_chartT, hA]
  have hb : (Igusa.chartT (Igusa.BF F p hp5)).eval t = 0 := by
    rw [Igusa.eval_chartT, hB]
  have hs := congrArg (fun f : Polynomial F => f.eval t)
    (Igusa.chartT_system (F := F) hp5 RamanujanODEProof.ramanujanODE).1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X, ha, hb, mul_zero, add_zero] at hs
  have hd : (Igusa.chartT (Igusa.AF F p hp5)).derivative.eval t = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left (mul_ne_zero
      (neg_ne_zero.mpr (Igusa.four_ne_zero' (F := F) hp5)) (sub_ne_zero.mpr ht.symm))
  exact Igusa.igusa_chartT hp5 RamanujanODEProof.ramanujanODE ht
    (square_dvd_of_eval_derivative_eq_zero _ t (Igusa.chartT_AF_ne_zero hp5) ha hd)

theorem hasse_companion_chartS_separation (hp5 : 5 ≤ p)
    (hA : eval ![1, 0] (Igusa.AF F p hp5) = 0) :
    eval ![1, 0] (Igusa.BF F p hp5) ≠ 0 := by
  intro hB
  have ha : (Igusa.chartS (Igusa.AF F p hp5)).eval 0 = 0 := by
    rw [Igusa.eval_chartS, hA]
  have hb : (Igusa.chartS (Igusa.BF F p hp5)).eval 0 = 0 := by
    rw [Igusa.eval_chartS, hB]
  have hs := congrArg (fun f : Polynomial F => f.eval 0)
    (Igusa.chartS_system (F := F) hp5 RamanujanODEProof.ramanujanODE).1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X, ha, hb, zero_pow (by decide : 2 ≠ 0), sub_zero,
    mul_one, zero_mul, add_zero] at hs
  have hd : (Igusa.chartS (Igusa.AF F p hp5)).derivative.eval 0 = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left (neg_ne_zero.mpr (Igusa.six_ne_zero' (F := F) hp5))
  apply Igusa.igusa_chartS (F := F) hp5 RamanujanODEProof.ramanujanODE
  simpa using square_dvd_of_eval_derivative_eq_zero _ 0 (Igusa.chartS_AF_ne_zero hp5) ha hd

/-- The two level-one Hasse polynomials have no common nonzero weighted point. -/
theorem hasse_companion_separation [IsAlgClosed F] (hp5 : 5 ≤ p) (x y : F)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hA : eval ![x, y] (Igusa.AF F p hp5) = 0) :
    eval ![x, y] (Igusa.BF F p hp5) ≠ 0 := by
  intro hB
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := hxy.resolve_right (not_ne_iff.mpr rfl)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq x (by decide : 0 < 4)
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu; exact hx hu.symm
    have ha := Igusa.eval_scale (Igusa.iso_AF (F := F) hp5) u 1 0
    have hb := Igusa.eval_scale (Igusa.iso_BF (F := F) hp5) u 1 0
    simp only [mul_one, mul_zero, hu, hA, hB] at ha hb
    exact hasse_companion_chartS_separation hp5
      ((mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hu0))
      ((mul_eq_zero.mp hb.symm).resolve_left (pow_ne_zero _ hu0))
  · obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq y (by decide : 0 < 6)
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu; exact hy hu.symm
    have hx : u ^ 4 * (x / u ^ 4) = x := by field_simp
    have ha := Igusa.eval_scale (Igusa.iso_AF (F := F) hp5) u (x / u ^ 4) 1
    have hb := Igusa.eval_scale (Igusa.iso_BF (F := F) hp5) u (x / u ^ 4) 1
    simp only [mul_one, hx, hu, hA, hB] at ha hb
    exact hasse_companion_chartT_separation hp5 (x / u ^ 4)
      ((mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hu0))
      ((mul_eq_zero.mp hb.symm).resolve_left (pow_ne_zero _ hu0))

theorem eval_binaryPullback {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![x, y] (binaryPullback R P) =
      eval ![eval ![x, y] (binaryE4 R), eval ![x, y] (binaryE6 R)] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [binaryPullback]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    fin_cases i <;> simp [binaryPullback]

/-- The binary Hasse invariant and its companion have no common projective zero. -/
theorem binaryHasse_separation [IsAlgClosed F] (hp5 : 5 ≤ p) (x y : F)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hA : eval ![x, y] (binaryHasse F p hp5) = 0) :
    eval ![x, y] (binaryHasseCompanion F p hp5) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by omega : p ≠ 2)
  have h3 : (3 : F) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by omega : p ≠ 3)
  have hE : eval ![x, y] (binaryE4 F) ≠ 0 ∨ eval ![x, y] (binaryE6 F) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨hx, hy⟩ := binaryEisenstein_common_zero h2 h3 x y h.1 h.2
    exact hxy.elim (fun h => h hx) (fun h => h hy)
  rw [binaryHasse, eval_binaryPullback] at hA
  rw [binaryHasseCompanion, eval_binaryPullback]
  exact hasse_companion_separation hp5 _ _ hE hA

/-- Coprimality on the first affine chart, over every characteristic-p field. -/
theorem binaryHasse_chartT_coprime (hp5 : 5 ≤ p) :
    IsCoprime (Igusa.chartT (binaryHasse F p hp5))
      (Igusa.chartT (binaryHasseCompanion F p hp5)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F (AlgebraicClosure F) _ _).mpr
  intro t
  rw [aeval_chartT, aeval_chartT, map_binaryHasse, map_binaryHasseCompanion]
  by_cases h : eval ![t, 1] (binaryHasse (AlgebraicClosure F) p hp5) = 0
  · exact Or.inr (binaryHasse_separation hp5 t 1 (Or.inr one_ne_zero) h)
  · exact Or.inl h

/-- Coprimality on the other affine chart, including the point at infinity. -/
theorem binaryHasse_chartS_coprime (hp5 : 5 ≤ p) :
    IsCoprime (Igusa.chartS (binaryHasse F p hp5))
      (Igusa.chartS (binaryHasseCompanion F p hp5)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F (AlgebraicClosure F) _ _).mpr
  intro t
  rw [aeval_chartS, aeval_chartS, map_binaryHasse, map_binaryHasseCompanion]
  by_cases h : eval ![1, t] (binaryHasse (AlgebraicClosure F) p hp5) = 0
  · exact Or.inr (binaryHasse_separation hp5 1 t (Or.inl one_ne_zero) h)
  · exact Or.inl h

end RamanujanTau.TheoremA
