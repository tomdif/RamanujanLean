/-
# Jacobi triple product campaign, Rung 3: the finite (one-sided) Jacobi triple product

The finite one-sided JTP `∏_{i<n}(1 + z·q^{2i+1}) = Σ_{k≤n} q^{k²}·[n,k]_{q²}·zᵏ` is obtained from the
q-binomial theorem `qbinom` (already proved) by **base change `q ↦ q²`** and the substitution `t ↦ z·q`.
Concretely we apply the ring homomorphism `Φ` — base-change the coefficients (`q ↦ q²`, via Mathlib's
`PowerSeries.expand 2`) and send the bookkeeping variable `t = X` to `z·q` — to both sides of `qbinom`.
Under `Φ` the Gauss exponent `q^{C(k,2)}` becomes `q^{2·C(k,2)+k} = q^{k²}` (the theta exponent), and the
Gaussian binomial `[n,k]_q` becomes `[n,k]_{q²} = E2 [n,k]_q`.

Here `z = Polynomial.X` (only non-negative powers appear in the one-sided product, so no Laurent variable is
needed yet — that enters at Rung 4 with the `z⁻¹` factor), `q = qq = PowerSeries.X`, `C = Polynomial.C`.
No `sorry`.

This is Rung 3 of the JTP campaign. Rung 4 (the limit `n→∞` and the bilateral symmetrization combining with
`(q²;q²)_∞` to reach the full `Σ_{n∈ℤ}` form, `MockTheta5JacobiBilateral`) is the remaining hard step.
-/
import RamanujanTau.MockTheta5QBinom
import Mathlib.RingTheory.PowerSeries.Expand

namespace MockTheta5.Bailey
open Polynomial

/-- Base change `q ↦ q²` on `ℤ⟦q⟧`, i.e. `PowerSeries.expand 2`. -/
noncomputable def E2 : PowerSeries ℤ →+* PowerSeries ℤ := (PowerSeries.expand 2 (by norm_num)).toRingHom

lemma E2_X : E2 qq = qq ^ 2 := PowerSeries.expand_X 2 (by norm_num)

/-- The substitution homomorphism: base-change coefficients (`q ↦ q²`) and send `t ↦ z·q`. -/
noncomputable def Φ : Polynomial (PowerSeries ℤ) →+* Polynomial (PowerSeries ℤ) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp E2) (Polynomial.X * Polynomial.C qq)

/-- The exponent collapse `2·C(k,2) + k = k²` (Gauss exponent under base change becomes the theta exponent). -/
lemma two_choose_two_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith [ih]

/-- `Φ` on a product factor: `1 + q^i·t ↦ 1 + z·q^{2i+1}`. -/
lemma Φ_factor (i : ℕ) :
    Φ (1 + C (qq ^ i) * Polynomial.X) = 1 + C (qq ^ (2 * i + 1)) * Polynomial.X := by
  simp only [Φ, map_add, map_one, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
    RingHom.coe_comp, Function.comp_apply, E2_X]
  ring

/-- `Φ` on a sum term: `q^{C(k,2)}[n,k]_q·tᵏ ↦ q^{k²}·[n,k]_{q²}·zᵏ`. -/
lemma Φ_qcoeff_term (n k : ℕ) :
    Φ (C (qcoeff n k) * Polynomial.X ^ k)
      = C (qq ^ (k ^ 2) * E2 (gaussBinom n k)) * Polynomial.X ^ k := by
  simp only [Φ, qcoeff, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
    RingHom.coe_comp, Function.comp_apply, E2_X]
  rw [← two_choose_two_add k]; ring

/-- **The finite (one-sided) Jacobi triple product**
`∏_{i<n}(1 + z·q^{2i+1}) = Σ_{k≤n} q^{k²}·[n,k]_{q²}·zᵏ`, over `Polynomial (ℤ⟦q⟧)` (`z = X`).
Obtained from the q-binomial theorem by the base change `q ↦ q²` and `t ↦ z·q`. -/
theorem finite_jtp (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 + C (qq ^ (2 * i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1), C (qq ^ (k ^ 2) * E2 (gaussBinom n k)) * Polynomial.X ^ k := by
  have h : Φ (qprod n) = Φ (qbRHS n) := by rw [qbinom]
  rw [qprod, map_prod, qbRHS, map_sum,
      Finset.prod_congr rfl (fun i _ => Φ_factor i),
      Finset.sum_congr rfl (fun k _ => Φ_qcoeff_term n k)] at h
  exact h

end MockTheta5.Bailey
