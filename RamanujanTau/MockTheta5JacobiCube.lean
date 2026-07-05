/-
# Jacobi's cube identity `(q;q)_∞³ = Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}`

This is the missing classical input for Ramanujan's partition congruence `p(5n+4) ≡ 0 (mod 5)`
(`PartitionCongruenceMod5.lean` proves the arithmetic heart; this supplies the `(q;q)³` expansion it needs).

**What this file establishes (all verified, no `sorry`):**
1. `jacobiCubeSum : PowerSeries ℤ` — the RHS `Σ (−1)ᵐ (2m+1) q^{m(m+1)/2}`, as a genuine infinite power
   series via coefficient stabilization (the `m`-th term has `q`-order `m(m+1)/2 ≥ m`).
2. `coeff_zero_jacobiCubeSum` — base case (constant term `1`).
3. `jacobi_cube_identity_of_coeff` — the identity `qfacInf³ = jacobiCubeSum` reduced to its per-coefficient
   form (the `PowerSeries.ext` bookkeeping supplied; this pins the exact remaining goal).
4. `jacobi_cube_rung2` — a machine-checked (`native_decide`) verification that `(q;q)³` and the triangular
   `(2m+1)`-weighted sum agree to order `q⁴⁸`, reusing the self-contained truncated-series arithmetic of
   `MockTheta5.lean`. (Rung-2 evidence, like the R1/R2 mock-theta checks.)

**Remaining wall (the rung-3 proof of the coefficient identity).** Jacobi's cube is *not* a specialization
of the repo's square-form JTP (`Σ zⁿ q^{n²}`): the `(2m+1)` weight and triangular exponents come from
**differentiating a TRIANGULAR bilateral JTP** `Σ(−1)ⁿ zⁿ q^{n(n−1)/2} = ∏(1−qⁿ)(1−z qⁿ⁻¹)(1−z⁻¹ qⁿ)`
in `z` and evaluating at `z = 1`. Good news: `z = 1` is a **unit**, so this sidesteps the non-unit `ℤ((q))`
wall that blocks the pentagonal/RR products; and the base-`q` Cauchy identity `euler_cauchy` is the ingredient
for building the triangular JTP. The two remaining pieces are (A) the triangular bilateral JTP (mirror of the
square-JTP chain, from `euler_cauchy`) and (B) the `d/dz|_{z=1}` functional (buildable from `zProj` as
`Σ_κ κ · zProj_κ`, no new calculus machinery). Multi-session; tracked here.
-/
import RamanujanTau.MockTheta5R1
import RamanujanTau.MockTheta5JacobiTriple
import RamanujanTau.MockTheta5

namespace MockTheta5.JTP
open PowerSeries

/-- the `m`-th term order `m(m+1)/2` dominates `m` (so partial sums stabilize per coefficient). -/
lemma tri_ge (m : ℕ) : m ≤ m * (m + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · calc m * 2 ≤ m * (m + 1) := Nat.mul_le_mul_left m (by omega)
      _ = m * (m + 1) := rfl

/-- **RHS of Jacobi's cube identity**: `Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}` as a formal power series. -/
noncomputable def jacobiCubeSum : PowerSeries ℤ :=
  mtSum (fun m => m * (m + 1) / 2) (fun m => C ((-1 : ℤ) ^ m * (2 * m + 1)))

/-- `coeff k jacobiCubeSum` is the finite sum over the first `M ≥ k+1` triangular terms. -/
lemma coeff_jacobiCubeSum {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k jacobiCubeSum
      = ∑ m ∈ Finset.range M, coeff k (X ^ (m * (m + 1) / 2) * C ((-1 : ℤ) ^ m * (2 * m + 1))) :=
  coeff_mtSum _ _ tri_ge hM

/-- base case: the constant term is `1` (the `m = 0` term, `q⁰·1`). -/
lemma coeff_zero_jacobiCubeSum : coeff 0 jacobiCubeSum = 1 := by
  rw [coeff_jacobiCubeSum (le_refl 1), Finset.sum_range_one]
  simp

/-- **Jacobi's cube identity, reduced to its coefficient form.**
`(q;q)_∞³ = Σ (−1)ᵐ(2m+1)q^{m(m+1)/2}` follows from the per-coefficient equality for all `k`. That
coefficient identity is the genuine remaining content (triangular JTP + `d/dz|_{z=1}`, see header); the
`PowerSeries.ext` reduction is supplied here, no `sorry`. -/
theorem jacobi_cube_identity_of_coeff
    (h : ∀ k, coeff k (qfacInf ^ 3) = coeff k jacobiCubeSum) : qfacInf ^ 3 = jacobiCubeSum :=
  PowerSeries.ext h

/-! ### Rung-2 certificate: `(q;q)³` vs the triangular sum, machine-checked to order `q⁴⁸`. -/

namespace Rung2
open MockTheta5

/-- truncated `(q;q)_∞ = ∏_{k≥1}(1 − qᵏ)` to order `q^N`. -/
def qqInf : List Int := pprod ((List.range N).map (fun i => factor (i + 1) (-1)))

/-- truncated `(q;q)_∞³`. -/
def qqCube : List Int := pmul (pmul qqInf qqInf) qqInf

/-- truncated `Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}` (10 terms cover all exponents `< 48`). -/
def triSum : List Int :=
  sumN (fun m => pshift (pscale ((-1 : Int) ^ m * (2 * (m : Int) + 1)) pone) (m * (m + 1) / 2)) 10

def resCube : List Int := psub qqCube triSum

/-- **Jacobi's cube identity `(q;q)³ = Σ (−1)ᵐ(2m+1)q^{m(m+1)/2}`, verified to order `q⁴⁸`.** -/
theorem jacobi_cube_rung2 : allZero resCube = true := by native_decide

end Rung2

end MockTheta5.JTP
