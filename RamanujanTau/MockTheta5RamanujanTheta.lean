/-
# Ramanujan's theta functions, as Jacobi-triple-product specializations

Ramanujan's general theta `f(a,b) = Σ_{n∈ℤ} a^{n(n+1)/2} b^{n(n-1)/2} = (−a;ab)_∞(−b;ab)_∞(ab;ab)_∞`
specializes to the three classical one-variable theta functions. This file records the three, using the
square Jacobi triple product `bilateralTheta = Σ_{n∈ℤ} zⁿ q^{n²}` (already proved in the repo) and Euler's
pentagonal number theorem:

  * **`f(−q) = (q;q)_∞`**  — `ramanujan_f_neg` (Euler pentagonal; `pentSeries = Σ (−1)ⁿ q^{n(3n−1)/2}`),
  * **`φ(q) = Σ q^{n²} = (q²;q²)_∞ (−q;q²)_∞²`**  — `phi_product` (JTP at `z = 1`),
  * **`φ(−q) = Σ (−1)ⁿ q^{n²} = (q²;q²)_∞ (q;q²)_∞²`**  — `phiNeg_product` (JTP at `z = −1`),
  * **`ψ(q) = (q²;q²)_∞ / (q;q²)_∞`**  — `psi`, with its defining relation `psi_mul_oddPochInf`.

`(q²;q²)_∞ = qfac2Inf`, `(−q;q²)_∞ = negOddPochInf = ∏(1+q^{2k+1})`, `(q;q²)_∞ = oddPochInf = ∏(1−q^{2k+1})`.
The series form of `ψ`, Gauss's `ψ(q) = Σ_{n≥0} q^{n(n+1)/2}`, is a one-sided (base-`q⁴`) triple product —
a separate build not included here. No `sorry`.
-/
import RamanujanTau.MockTheta5GaussProduct
import RamanujanTau.MockTheta5AltProduct
import RamanujanTau.MockTheta5PentagonalRecurrence

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-! ### `f(−q) = (q;q)_∞` -/

/-- **`f(−q) = (q;q)_∞`.** Ramanujan's `f(−q) = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}` (`= pentSeries`) equals the
Euler product `(q;q)_∞` — Euler's pentagonal number theorem. -/
theorem ramanujan_f_neg : pentSeries = qfacInf := euler_pentagonal.symm

/-! ### `φ(q) = Σ q^{n²}` (Ramanujan's `φ`, Jacobi's `θ₃`) -/

/-- **`φ(q) = Σ_{n∈ℤ} q^{n²}`**, the `z = 1` value of the bilateral square theta `Σ zⁿ q^{n²}`. -/
noncomputable def phi : PowerSeries ℤ := PowerSeries.map ev1 bilateralTheta

@[simp] lemma coeff_zero_phi : coeff 0 phi = 1 := by
  rw [phi, PowerSeries.coeff_map, coeff_zero_bilateralTheta, map_one]

/-- **`φ(q) = (q²;q²)_∞ · (−q;q²)_∞²`.** The classical product form (Jacobi triple product at `z = 1`). -/
theorem phi_product : phi = qfac2Inf * negOddPochInf ^ 2 := gauss_theta_product

/-- **`φ(−q) = Σ_{n∈ℤ} (−1)ⁿ q^{n²}`**, the alternating square theta (`z = −1`). -/
noncomputable def phiNeg : PowerSeries ℤ := PowerSeries.map evm1 bilateralTheta

/-- **`φ(−q) = (q²;q²)_∞ · (q;q²)_∞²`.** -/
theorem phiNeg_product : phiNeg = qfac2Inf * oddPochInf ^ 2 := alternating_theta_product

/-! ### `ψ(q) = (q²;q²)_∞ / (q;q²)_∞` (Ramanujan's `ψ`) -/

/-- **`ψ(q) = (q²;q²)_∞ / (q;q²)_∞`**, Ramanujan's theta `ψ`. Its Gauss series form
`ψ(q) = Σ_{n≥0} q^{n(n+1)/2}` is the one-sided base-`q⁴` triple product (not built here). -/
noncomputable def psi : PowerSeries ℤ := qfac2Inf * Ring.inverse oddPochInf

/-- **`ψ(q) · (q;q²)_∞ = (q²;q²)_∞`** — the defining product relation for `ψ`. -/
theorem psi_mul_oddPochInf : psi * oddPochInf = qfac2Inf := by
  rw [psi, mul_assoc, Ring.inverse_mul_cancel _ isUnit_oddPochInf, mul_one]

end MockTheta5.JTP
