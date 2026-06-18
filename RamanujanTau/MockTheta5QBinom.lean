/-
# Bailey campaign, Tier-1 capstone: the q-binomial theorem (finite Cauchy / Rothe)

Goal: `∏_{i<n} (1 + qⁱ·t) = ∑_{k≤n} q^{C(k,2)}·[n,k]_q·tᵏ`, the finite q-binomial theorem, the bridge from the
Gaussian binomial `gaussBinom` (rung 1) to the product side that the Bailey machinery needs.

Worked over `Polynomial (PowerSeries ℤ)`: the outer indeterminate `X` is the bookkeeping variable `t`, and the
coefficients live in `PowerSeries ℤ` with `q := PowerSeries.X` (here `qq`). The clean proof route is the
**functional equation** `Pₙ₊₁(t) = (1+t)·Pₙ(q·t)` (substituting `t ↦ q·t` reproduces q-Pascal exactly when the
`tᵏ` coefficients are matched). This file builds that functional equation; the coefficient match (with the
triangular exponent `C(k,2)`) is the next rung on top of it.

No `sorry`.
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import RamanujanTau.MockTheta5Bailey

namespace MockTheta5.Bailey
open Polynomial

/-- `q := PowerSeries.X`, the coefficient-ring indeterminate (the outer `Polynomial.X` is the variable `t`). -/
noncomputable abbrev qq : PowerSeries ℤ := PowerSeries.X

/-- `Pₙ(t) = ∏_{i<n} (1 + qⁱ·t)`, in `Polynomial (PowerSeries ℤ)` (`X` is `t`). -/
noncomputable def qprod (n : ℕ) : Polynomial (PowerSeries ℤ) :=
  ∏ i ∈ Finset.range n, (1 + C (qq ^ i) * X)

/-- A single factor under the substitution `t ↦ q·t`: `(1 + qⁱ·t)|_{t↦q·t} = 1 + qⁱ⁺¹·t`. -/
lemma factor_comp (i : ℕ) :
    (1 + C (qq ^ i) * X).comp (C qq * X) = 1 + C (qq ^ (i + 1)) * X := by
  simp only [add_comp, mul_comp, C_comp, X_comp, one_comp, pow_succ, map_mul]
  ring

/-- `Pₙ(q·t) = ∏_{i<n} (1 + qⁱ⁺¹·t)` — the substitution shifts every exponent up by one. -/
lemma qprod_comp (n : ℕ) :
    (qprod n).comp (C qq * X) = ∏ i ∈ Finset.range n, (1 + C (qq ^ (i + 1)) * X) := by
  rw [qprod, prod_comp]
  exact Finset.prod_congr rfl (fun i _ => factor_comp i)

/-- **The functional equation** `Pₙ₊₁(t) = (1 + t)·Pₙ(q·t)`. -/
lemma qprod_succ (n : ℕ) :
    qprod (n + 1) = (1 + X) * (qprod n).comp (C qq * X) := by
  rw [qprod_comp, qprod, Finset.prod_range_succ']
  simp only [pow_zero, map_one, one_mul]
  ring

end MockTheta5.Bailey
