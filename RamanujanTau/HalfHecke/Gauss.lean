import Mathlib

/-!
# Quadratic Gauss sums modulo a prime `Q`

`gQ Q = Σ_{x mod Q} (x/Q) e(x/Q)`, the twisted character sum `Σ (x/Q) e(xn/Q) = (n/Q) gQ`,
`gQ² = (−1/Q) Q`, and the sign (Gauss) for the two primes used here:
`gQ 11 = i√11` and `gQ 37 = √37`.  The sign is the only analytic input; it follows from the
monotonicity of `sin` and `cos`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex Finset
open scoped Real

noncomputable section

variable (Q : ℕ) [hQ : Fact Q.Prime]

/-- The quadratic character mod `Q`, with values in `ℂ`. -/
def chiQ : MulChar (ZMod Q) ℂ := (quadraticChar (ZMod Q)).ringHomComp (Int.castRingHom ℂ)

lemma chiQ_apply (x : ZMod Q) : chiQ Q x = ((quadraticChar (ZMod Q) x : ℤ) : ℂ) := rfl

lemma chiQ_natCast (b : ℕ) : chiQ Q (b : ZMod Q) = ((legendreSym Q b : ℤ) : ℂ) := by
  rw [chiQ_apply, legendreSym]; push_cast; rfl

lemma chiQ_intCast (b : ℤ) : chiQ Q (b : ZMod Q) = ((legendreSym Q b : ℤ) : ℂ) := by
  rw [chiQ_apply, legendreSym]

/-- The quadratic Gauss sum. -/
def gQ : ℂ := gaussSum (chiQ Q) ZMod.stdAddChar

lemma chiQ_quad : (chiQ Q).IsQuadratic := (quadraticChar_isQuadratic (ZMod Q)).comp _

lemma two_ne_Q (h3 : 3 ≤ Q) : ringChar (ZMod Q) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

lemma chiQ_ne_one (h3 : 3 ≤ Q) : chiQ Q ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).mpr (quadraticChar_ne_one (two_ne_Q Q h3))

lemma chiQ_sq (x : ZMod Q) (hx : x ≠ 0) : chiQ Q x * chiQ Q x = 1 := by
  have h := (chiQ_quad Q) x
  have hne : chiQ Q x ≠ 0 := by
    intro h0
    have h1 : chiQ Q (x * x⁻¹) = 1 := by rw [mul_inv_cancel₀ hx, MulChar.map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  rcases h with h | h | h
  · exact absurd h hne
  · rw [h, mul_one]
  · rw [h]; ring

/-- **The twisted character sum.** -/
theorem charSum (h3 : 3 ≤ Q) (n : ZMod Q) :
    ∑ x : ZMod Q, chiQ Q x * ZMod.stdAddChar (x * n) = chiQ Q n * gQ Q := by
  by_cases hn : n = 0
  · subst hn
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, zero_mul]
    exact MulChar.sum_eq_zero_of_ne_one (chiQ_ne_one Q h3)
  · have hu : IsUnit n := isUnit_iff_ne_zero.mpr hn
    have h := gaussSum_mulShift (chiQ Q) ZMod.stdAddChar hu.unit
    simp only [IsUnit.unit_spec] at h
    have e : gaussSum (chiQ Q) (AddChar.mulShift ZMod.stdAddChar n) =
        ∑ x : ZMod Q, chiQ Q x * ZMod.stdAddChar (x * n) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.mulShift_apply, mul_comm n x]
    rw [← e, gQ, ← h, ← mul_assoc, chiQ_sq Q n hn, one_mul]

/-- `gQ² = (−1/Q)·Q`. -/
theorem gQ_sq (h3 : 3 ≤ Q) : gQ Q ^ 2 = chiQ Q (-1) * Q := by
  rw [gQ, gaussSum_sq (chiQ_ne_one Q h3) (chiQ_quad Q) (ZMod.isPrimitive_stdAddChar Q), ZMod.card]

/-- The Gauss sum as an explicit sum over `0 ≤ b < Q`. -/
lemma gQ_eq_range : gQ Q = ∑ b ∈ range Q, ((legendreSym Q b : ℤ) : ℂ) * cexp (2 * π * I * b / Q) := by
  have hQ0 : Q ≠ 0 := hQ.out.ne_zero
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  rw [gQ, gaussSum, ← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [← chiQ_natCast, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 2
  · exact (ZMod.natCast_zmod_val x).symm

end

end RamanujanTau.HalfHecke
