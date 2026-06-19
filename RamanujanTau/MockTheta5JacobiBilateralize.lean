/-
# Jacobi triple product campaign, Rung 4 step L6 + the bilateralization analysis (L5, L7)

This file completes **L6** and records the precise remaining mathematics for the full bilateral JTP.

**L6 (done):** `(q²;q²)_∞ = ∏_{n≥1}(1-q^{2n})`, obtained as the base change `E2((q;q)_∞)` of the infinite
product from Rung 1. Constant term 1 and unit, transported from `qfacInf`.

**Where the campaign stands.** Proved and committed (all axiom-clean): Rungs 1–3, and Rung 4 steps L1, L2, L4
(the one-sided Cauchy/Euler identity `∏_{i≥0}(1+z q^{2i+1}) = Σ_k q^{k²}zᵏ/(q²;q²)_k`) and L6.

**The two remaining steps, stated precisely (NO `sorry` committed):**

* **L5 (engineering):** transport `oneSidedCauchy` from `ℤ⟦q⟧⟦z⟧` (where the `z`-variable is an outer power
  series) to `ℤ⟦q⟧` over `ℤ[z;z⁻¹]` (where `z = T 1`), and form the `z⁻¹` mirror. This is a coefficient
  transport (well-defined because the `zᵏ`-coefficient has minimal `q`-degree `k² → ∞`), not new mathematics.

* **L7 (the hard new identity):** the bilateralization
  `(q²;q²)_∞ · (Σ_{k≥0} q^{k²}zᵏ/(q²;q²)_k) · (Σ_{j≥0} q^{j²}z⁻ʲ/(q²;q²)_j) = Σ_{n∈ℤ} zⁿ q^{n²}`.
  Matching the `zⁿ`-coefficient (diagonal `k−j=n`, set `k=j+n`, factor `q^{n²}`) reduces it **exactly** to the
  **Durfee rectangle identity** (here `Q = q²`):

      Σ_{j≥0}  Q^{j(j+n)} / ((Q;Q)_{j+n} · (Q;Q)_j)  =  1 / (Q;Q)_∞      (for every n ≥ 0).

  This reduction is verified numerically (q-series to order 40, n = 0..4). The Durfee rectangle identity is a
  genuine infinite q-series theorem (its `n=0` case is the classical Durfee square identity); proving it is a
  self-contained sub-campaign (infinite sums over `j`, the `(Q;Q)_∞` limit) — the single hard piece left.

* **L8:** assemble L5 + L6 + L7 with `coeff_bilateralTheta` to conclude
  `∏_{n≥1}(1-q^{2n})(1+z q^{2n-1})(1+z⁻¹ q^{2n-1}) = bilateralTheta`.

No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiCauchy
import RamanujanTau.MockTheta5JacobiTriple

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **L6**: `(q²;q²)_∞ = ∏_{n≥1}(1 - q^{2n})`, the base change of `(q;q)_∞`. -/
noncomputable def qfac2Inf : PowerSeries ℤ := E2 qfacInf

@[simp] lemma coeff_zero_qfac2Inf : coeff 0 qfac2Inf = 1 := by
  rw [qfac2Inf, coeff_E2]; simp [coeff_zero_qfacInf]

/-- `(q²;q²)_∞` is a unit, so it can serve as the JTP prefactor. -/
lemma isUnit_qfac2Inf : IsUnit qfac2Inf := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_qfac2Inf]
  exact isUnit_one

end MockTheta5.JTP
