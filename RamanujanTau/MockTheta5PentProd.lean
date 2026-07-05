/-
# Euler pentagonal — stone: the finite shifted base-`q³` product `∏(1+z q^{3i+1})`

Mirror of the square-JTP `finite_jtp`, with base change `q ↦ q³` (`E3`) instead of `q ↦ q²` (`E2`):

  **`finite_pent_jtp`:**  `∏_{i<n}(1 + z·q^{3i+1}) = Σ_{k≤n} q^{3·C(k,2)+k}·[n,k]_{q³}·zᵏ`,

over `Polynomial (ℤ⟦q⟧)` (`z = X`), from the q-binomial theorem via `Φ3 = (q↦q³) + (t↦z·q)`. The `zᵏ`
weight carries the pentagonal exponent `3·C(k,2)+k = (3k²−k)/2 = e(k)` (kept in the uncollapsed form
`3·C(k,2)+k` so no `ℕ`-subtraction is needed). No `sorry`.
-/
import RamanujanTau.MockTheta5PentEngine
import RamanujanTau.MockTheta5JacobiFinite

namespace MockTheta5.JTP
open Polynomial MockTheta5.Bailey

/-- The substitution `q ↦ q³`, `t ↦ z·q` on `Polynomial (ℤ⟦q⟧)` (base-`q³` analogue of `Φ`). -/
noncomputable def Φ3 : Polynomial (PowerSeries ℤ) →+* Polynomial (PowerSeries ℤ) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp E3) (Polynomial.X * Polynomial.C qq)

/-- `Φ3` on a product factor: `1 + qⁱ·t ↦ 1 + z·q^{3i+1}`. -/
lemma Φ3_factor (i : ℕ) :
    Φ3 (1 + C (qq ^ i) * Polynomial.X) = 1 + C (qq ^ (3 * i + 1)) * Polynomial.X := by
  simp only [Φ3, map_add, map_one, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
    RingHom.coe_comp, Function.comp_apply, E3_X]
  ring

/-- `Φ3` on a sum term: `q^{C(k,2)}[n,k]_q·tᵏ ↦ q^{3·C(k,2)+k}·[n,k]_{q³}·zᵏ`. -/
lemma Φ3_qcoeff_term (n k : ℕ) :
    Φ3 (C (qcoeff n k) * Polynomial.X ^ k)
      = C (qq ^ (3 * k.choose 2 + k) * E3 (gaussBinom n k)) * Polynomial.X ^ k := by
  simp only [Φ3, qcoeff, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
    RingHom.coe_comp, Function.comp_apply, E3_X]
  ring

/-- **The finite shifted base-`q³` (one-sided) Jacobi triple product.** -/
theorem finite_pent_jtp (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 + C (qq ^ (3 * i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1),
          C (qq ^ (3 * k.choose 2 + k) * E3 (gaussBinom n k)) * Polynomial.X ^ k := by
  have h : Φ3 (qprod n) = Φ3 (qbRHS n) := by rw [qbinom]
  rw [qprod, map_prod, qbRHS, map_sum,
      Finset.prod_congr rfl (fun i _ => Φ3_factor i),
      Finset.sum_congr rfl (fun k _ => Φ3_qcoeff_term n k)] at h
  exact h

end MockTheta5.JTP
