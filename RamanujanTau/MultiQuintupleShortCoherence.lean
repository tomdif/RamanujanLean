/-
# Arithmetic behind coherence of short Watson pairs

For a dual vector w, put lambda = w/i modulo p, u = (v.w)/p,
ell = 2u + c*lambda, and D = (v.v)/p + c.  Then

  (w.w)/p = lambda*ell - D*lambda^2 (mod p).

Two distinct short vectors in one norm shell cannot have the same lambda.
Equal phase therefore forces D*(lambda+lambda')=ell.  This single reflection
preserves the polarized form for every pair of partners, which is the
arithmetic input missing from arbitrary phase assignments.

The identities below are formal.  The complete geometric/analytic argument
and the finite short-generator certificates remain a paper proof in
RESEARCH_MULTI_QUINTUPLE.md; this module does not assert the full converse.
-/
import RamanujanTau.MultiQuintupleDualCompression

namespace Ramanujan.MultiQuintuple

/-- The norm of a projective lift, including its exact p-squared error. -/
theorem projective_lift_norm_quotient_identity
    (p h l v1 v2 v3 z1 z2 z3 : ℤ)
    (hv : ternaryNorm v1 v2 v3 = p * h) :
    ternaryNorm (l*v1+p*z1) (l*v2+p*z2) (l*v3+p*z3) =
      p * (2*l*(l*h + ternaryDot v1 v2 v3 z1 z2 z3) - h*l^2) +
        p^2 * ternaryNorm z1 z2 z3 := by
  simp only [ternaryNorm, ternaryDot] at hv ⊢
  linear_combination l^2 * hv

/-- Polarization of the projective quotient identity, with its exact error. -/
theorem projective_lift_dot_quotient_identity
    (p h l m v1 v2 v3 z1 z2 z3 t1 t2 t3 : ℤ)
    (hv : ternaryNorm v1 v2 v3 = p * h) :
    ternaryDot (l*v1+p*z1) (l*v2+p*z2) (l*v3+p*z3)
        (m*v1+p*t1) (m*v2+p*t2) (m*v3+p*t3) =
      p * (l*(m*h + ternaryDot v1 v2 v3 t1 t2 t3) +
        m*(l*h + ternaryDot v1 v2 v3 z1 z2 z3) - h*l*m) +
        p^2 * ternaryDot z1 z2 z3 t1 t2 t3 := by
  simp only [ternaryNorm, ternaryDot] at hv ⊢
  linear_combination l*m * hv

/-- Equal norm and equal phase leave precisely the identity and reflection
branches.  This is valid over any field, before specializing to ZMod p. -/
theorem phase_norm_identity_or_reflection
    {F : Type*} [Field F] (D ell l m : F)
    (hnorm : l*ell-D*l^2 = m*ell-D*m^2) :
    l = m ∨ D*(l+m) = ell := by
  have hf : (l-m)*(ell-D*(l+m)) = 0 := by
    calc
      (l-m)*(ell-D*(l+m)) = (l*ell-D*l^2)-(m*ell-D*m^2) := by ring
      _ = 0 := sub_eq_zero.mpr hnorm
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h).symm

/-- The nonidentity branch preserves all polarized pairings, not just the
individual norms.  No assumption of a previously existing linear map occurs. -/
theorem phase_reflection_preserves_polarization
    {F : Type*} [CommRing F] (D ell1 ell2 l1 l2 m1 m2 : F)
    (h1 : D*(l1+m1) = ell1) (h2 : D*(l2+m2) = ell2) :
    m1*ell2+m2*ell1-2*D*m1*m2 =
      l1*ell2+l2*ell1-2*D*l1*l2 := by
  rw [← h1, ← h2]
  ring

/-- In the zero-discriminant case, two different projective scalars in the
same phase and norm force that quotient norm to vanish. -/
theorem phase_zero_parameter_forces_zero_norm
    {F : Type*} [Field F] (ell l m : F)
    (hne : l ≠ m) (hnorm : l*ell = m*ell) : l*ell = 0 := by
  have h : (l-m)*ell = 0 := by linear_combination hnorm
  have hz : ell = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  simp [hz]

/-- Two distinct equal-norm integral vectors congruent modulo an odd p
cannot have squared norm below p-squared/2.  This rules out the identity
branch of the phase equation for a cancelling partner. -/
theorem short_equal_norm_translate_unique
    (p x1 x2 x3 z1 z2 z3 : ℤ) (hp : 0 < p) (hpodd : Odd p)
    (hnorm : ternaryNorm (x1+p*z1) (x2+p*z2) (x3+p*z3) =
      ternaryNorm x1 x2 x3)
    (hshort : 2 * ternaryNorm x1 x2 x3 < p^2) :
    z1 = 0 ∧ z2 = 0 ∧ z3 = 0 := by
  have hmul : p * (2 * ternaryDot x1 x2 x3 z1 z2 z3 +
      p * ternaryNorm z1 z2 z3) = 0 := by
    simp only [ternaryNorm, ternaryDot] at hnorm ⊢
    linear_combination hnorm
  have hpair : 2 * ternaryDot x1 x2 x3 z1 z2 z3 +
      p * ternaryNorm z1 z2 z3 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
  obtain ⟨k, hk⟩ := hpodd
  have heven : ternaryNorm z1 z2 z3 =
      2 * (-ternaryDot x1 x2 x3 z1 z2 z3 - k * ternaryNorm z1 z2 z3) := by
    linear_combination hpair - ternaryNorm z1 z2 z3 * hk
  have hsum : 0 ≤ ternaryNorm (2*x1+p*z1) (2*x2+p*z2) (2*x3+p*z3) := by
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hupper : p^2 * ternaryNorm z1 z2 z3 < p^2 * 2 := by
    simp only [ternaryNorm] at hnorm hshort hsum ⊢
    nlinarith
  have hnlt : ternaryNorm z1 z2 z3 < 2 :=
    (mul_lt_mul_iff_right₀ (sq_pos_of_pos hp)).mp (by simpa [mul_comm] using hupper)
  have hnnonneg : 0 ≤ ternaryNorm z1 z2 z3 :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hnzero : ternaryNorm z1 z2 z3 = 0 := by omega
  simp only [ternaryNorm] at hnzero
  constructor
  · nlinarith [sq_nonneg z2, sq_nonneg z3]
  constructor <;> nlinarith [sq_nonneg z1, sq_nonneg z2, sq_nonneg z3]

end Ramanujan.MultiQuintuple
