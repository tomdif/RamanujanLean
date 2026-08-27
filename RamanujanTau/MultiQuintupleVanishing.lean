/-
# Multi-quintuple vanishings: completed-square lattice coordinates

For the specialization `Q(q^i,q^p)`, Watson's bilateral quintuple-product sum has two
exponents for every `n : Z`:

  A(n) = p*n*(3*n-1)/2 + 3*i*n,
  B(n) = p*n*(3*n+1)/2 + i*(3*n+1).

To avoid integer-division bookkeeping, `quintExpA2` and `quintExpB2` store twice these
exponents.  The two theorems below put both branches on the same sum-of-squares lattice.
Any affine sign-reversing involution proof of a product-coefficient vanishing can use these
identities without appealing to analytic infinite products.  No general vanishing claim is
made here; `RESEARCH_MULTI_QUINTUPLE.md` records the current experimental boundary.
-/
import Mathlib.Tactic

namespace Ramanujan.MultiQuintuple

/-- Twice the positive-branch exponent in `Q(q^i,q^p)`. -/
def quintExpA2 (p i n : ℤ) : ℤ :=
  p * n * (3 * n - 1) + 6 * i * n

/-- Twice the negative-branch exponent in `Q(q^i,q^p)`. -/
def quintExpB2 (p i n : ℤ) : ℤ :=
  p * n * (3 * n + 1) + 2 * i * (3 * n + 1)

/-- Square completion for the positive branch of the specialized quintuple product. -/
theorem quintExpA2_square_completion (p i n : ℤ) :
    12 * p * quintExpA2 p i n + (6 * i - p) ^ 2
      = (6 * p * n + 6 * i - p) ^ 2 := by
  simp only [quintExpA2]
  ring

/-- Square completion for the negative branch of the specialized quintuple product. -/
theorem quintExpB2_square_completion (p i n : ℤ) :
    12 * p * quintExpB2 p i n + (6 * i - p) ^ 2
      = (6 * p * n + 6 * i + p) ^ 2 := by
  simp only [quintExpB2]
  ring

/-- Select one of the two bilateral branches. `true` is the negative branch. -/
def quintExp2 (negative : Bool) (p i n : ℤ) : ℤ :=
  if negative then quintExpB2 p i n else quintExpA2 p i n

/-- Completed-square coordinate for either bilateral branch. -/
def quintLatticeCoord (negative : Bool) (p i n : ℤ) : ℤ :=
  6 * p * n + 6 * i + if negative then p else -p

/-- Branch-uniform square completion.  The offset `(6*i-p)^2` does not depend on the
branch, while the branch chooses one of the two congruence classes for the coordinate. -/
theorem quintExp2_square_completion (negative : Bool) (p i n : ℤ) :
    12 * p * quintExp2 negative p i n + (6 * i - p) ^ 2
      = quintLatticeCoord negative p i n ^ 2 := by
  cases negative <;>
    simp [quintExp2, quintLatticeCoord, quintExpA2, quintExpB2] <;> ring

/-- Square completion for an arbitrary finite product of specialized quintuple products.
This is the exact quadratic form an exponent-preserving affine involution must preserve. -/
theorem sum_quintExp2_square_completion {α : Type*} (s : Finset α) (negative : α → Bool)
    (p : ℤ) (i n : α → ℤ) :
    12 * p * (∑ a ∈ s, quintExp2 (negative a) p (i a) (n a))
        + ∑ a ∈ s, (6 * i a - p) ^ 2
      = ∑ a ∈ s, quintLatticeCoord (negative a) p (i a) (n a) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => quintExp2_square_completion (negative a) p (i a) (n a)

/-- The first published triple satisfies the proposed isotropy condition. -/
theorem published13a_isotropic : (13 : ℤ) ∣ 1 ^ 2 + 3 ^ 2 + 4 ^ 2 := by norm_num

/-- The earlier second example at `p=13` satisfies the same condition. -/
theorem published13b_isotropic : (13 : ℤ) ∣ 2 ^ 2 + 5 ^ 2 + 6 ^ 2 := by norm_num

/-- The published `p=19` triple also satisfies the proposed isotropy condition. -/
theorem published19_isotropic : (19 : ℤ) ∣ 2 ^ 2 + 3 ^ 2 + 5 ^ 2 := by norm_num

/-- The published `p=31` triple also satisfies the proposed isotropy condition. -/
theorem published31_isotropic : (31 : ℤ) ∣ 1 ^ 2 + 5 ^ 2 + 6 ^ 2 := by norm_num

/-- The published four-factor example satisfies the analogous condition. -/
theorem published41_isotropic : (41 : ℤ) ∣ 1 ^ 2 + 4 ^ 2 + 5 ^ 2 + 9 ^ 2 := by norm_num

/-- Isotropy alone is not asserted to imply vanishing: `(1,4,14)` is the first scanned
counterexample to that implication. -/
theorem counterexample71_isotropic : (71 : ℤ) ∣ 1 ^ 2 + 4 ^ 2 + 14 ^ 2 := by norm_num

end Ramanujan.MultiQuintuple
