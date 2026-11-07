/-
# Exact estimates for the universal short-generator argument

These are the rational inequalities following reduction of a ternary Gram
matrix.  Existence of the reduced integral basis is a separate obligation;
it is not assumed to have been formalized by this file.
-/
import RamanujanTau.MultiQuintupleDualShortGeometry

namespace Ramanujan.MultiQuintuple

/-- The two Gram--Schmidt reduction inequalities bound the first length
cubically and the second quadratically. -/
theorem reduced_ternary_length_bounds
    (p A B C : ℚ) (hA : 1 ≤ A) (hB : 3*A ≤ 4*B)
    (hC : 3*B ≤ 4*C) (hdet : A*B*C = p) :
    27*A^3 ≤ 64*p ∧ 3*B^2 ≤ 4*p := by
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hAB := mul_le_mul_of_nonneg_left hC (le_of_lt (mul_pos hAp hBp))
  have hBs := mul_le_mul_of_nonneg_right hB (show 0 ≤ 3*A+4*B by positivity)
  have hAs := mul_le_mul_of_nonneg_left hBs (le_of_lt hAp)
  have hAs' := mul_le_mul_of_nonneg_right hA (sq_nonneg B)
  constructor <;> nlinarith

/-- The constants 80 and 30 are valid uniformly beyond 1250. -/
theorem reduced_ternary_large_prime_bounds
    (p A B C : ℚ) (hp : 1250 ≤ p) (hA : 1 ≤ A) (hB : 3*A ≤ 4*B)
    (hC : 3*B ≤ 4*C) (hdet : A*B*C = p) :
    A ≤ p/80 ∧ B ≤ p/30 := by
  obtain ⟨hAcube,hBsq⟩ := reduced_ternary_length_bounds p A B C hA hB hC hdet
  have hpp : 0 ≤ p := by linarith
  have hp2 : 1250^2 ≤ p^2 := pow_le_pow_left₀ (by norm_num) hp 2
  have hnum : 0 ≤ 27*p^2-32768000 := by nlinarith
  have hnum' := mul_nonneg hpp hnum
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (show 0 ≤ p/80 by positivity)
    nlinarith
  · apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (show 0 ≤ p/30 by positivity)
    have hnum2 := mul_nonneg hpp (show 0 ≤ p-1200 by linarith)
    nlinarith

/-- Every vector in the small coefficient box lies below the needed strict
p/2 bound in the divided Gram norm. The first and minor parameters really
are integers; this is used in the small-minor branch. -/
theorem short_generator_cost_lt_half
    (p B C : ℚ) (A M : ℤ) (hp : 1250 ≤ p) (hA : 1 ≤ A) (hM : 3 ≤ M)
    (hB : 3*(A : ℚ) ≤ 4*B) (hC : 3*B ≤ 4*C)
    (hminor : (A : ℚ)*B = M) (hdet : (A : ℚ)*B*C = p) :
    C+(49*(A : ℚ)+25*B)/4 < p/2 := by
  have hAq : (1 : ℚ) ≤ A := by exact_mod_cast hA
  have hAp : (0 : ℚ) < A := by linarith
  have hBp : 0 < B := by linarith
  have hCp : 0 < C := by linarith
  have hMC : (M : ℚ)*C = p := by rw [← hminor]; exact hdet
  by_cases hsmall : M < 12
  · have hM11 : (M : ℚ) ≤ 11 := by exact_mod_cast (show M ≤ 11 by omega)
    have hAs := mul_le_mul_of_nonneg_left hB (le_of_lt hAp)
    have hA3 : A ≤ 3 := by
      by_contra hn
      have hA4 : (4 : ℚ) ≤ A := by exact_mod_cast (show 4 ≤ A by omega)
      have hs : (16 : ℚ) ≤ (A : ℚ)^2 := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 4) hA4 2
      nlinarith
    have hA3q : (A : ℚ) ≤ 3 := by exact_mod_cast hA3
    have hB11 : B ≤ 11 := by
      have hh := mul_le_mul_of_nonneg_right hAq (le_of_lt hBp)
      nlinarith
    have hM3 : (3 : ℚ) ≤ M := by exact_mod_cast hM
    have hCC := mul_le_mul_of_nonneg_right hM3 (le_of_lt hCp)
    nlinarith
  · have hM12 : (12 : ℚ) ≤ M := by exact_mod_cast (show 12 ≤ M by omega)
    have hCC := mul_le_mul_of_nonneg_right hM12 (le_of_lt hCp)
    obtain ⟨ha,hb⟩ := reduced_ternary_large_prime_bounds p A B C hp hAq hB hC hdet
    nlinarith

/-- The size-reduction box estimate: |x|,|y|<=2 and z=0 or 1 cost at most
C+49A/4+25B/4 in Gram--Schmidt coordinates. -/
theorem reduced_ternary_box_cost
    (A B C mu nu xi x y z : ℚ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmu : |mu| ≤ 1/2) (hnu : |nu| ≤ 1/2) (hxi : |xi| ≤ 1/2)
    (hx : |x| ≤ 2) (hy : |y| ≤ 2) (hz : z = 0 ∨ z = 1) :
    A*(x+mu*y+nu*z)^2+B*(y+xi*z)^2+C*z^2 ≤ C+(49*A+25*B)/4 := by
  have hza : |z| ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have h1 : |x+mu*y+nu*z| ≤ 7/2 := by
    calc
      |x+mu*y+nu*z| ≤ |x| + |mu| * |y| + |nu| * |z| := by
        grw [abs_add_le, abs_add_le, abs_mul, abs_mul]
      _ ≤ 2+(1/2)*2+(1/2)*1 := by gcongr
      _ = 7/2 := by norm_num
  have h2 : |y+xi*z| ≤ 5/2 := by
    calc
      |y+xi*z| ≤ |y| + |xi| * |z| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2+(1/2)*1 := by gcongr
      _ = 5/2 := by norm_num
  have hs1 : (x+mu*y+nu*z)^2 ≤ (7/2 : ℚ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hs2 : (y+xi*z)^2 ≤ (5/2 : ℚ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hs3 : z^2 ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hA1 := mul_le_mul_of_nonneg_left hs1 hA
  have hB1 := mul_le_mul_of_nonneg_left hs2 hB
  have hC1 := mul_le_mul_of_nonneg_left hs3 hC
  nlinarith

end Ramanujan.MultiQuintuple
