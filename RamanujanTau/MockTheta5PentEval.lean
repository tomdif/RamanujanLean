/-
# Euler pentagonal — the `z = −1` evaluation (products → residue-class products; theta → pentagonal series)

Applying `map evm1` (`z ↦ −1`, a unit) to `bilateral_pent_JTP`:
  * `map evm1 qfacInfL_q3 = (q³;q³)_∞`,
  * `map evm1 pentProdAInf = ∏_{i≥0}(1−q^{3i+1})`, `map evm1 (map invert pentProdBInf) = ∏_{i≥0}(1−q^{3i+2})`,
  * `map evm1 pentTheta = Σ_{n∈ℤ}(−1)ⁿ q^{(3n²−n)/2}` (the pentagonal series `pentSeries`).
This file builds these evaluations (mirror of `MockTheta5JacobiCubeProof`). No `sorry`.
-/
import RamanujanTau.MockTheta5PentBilateral
import RamanujanTau.MockTheta5JacobiCubeProof

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- `map evm1` of a `z`-factor `1 + z q^e` is `1 − q^e`. -/
lemma map_evm1_factorE (e : ℕ) :
    PowerSeries.map evm1 (1 + X ^ e * PowerSeries.C (T 1)) = 1 - X ^ e := by
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C, evm1_T_eq_sgn,
      show sgn 1 = -1 from by decide, map_neg, map_one, mul_neg, mul_one]
  ring

lemma map_evm1_pentProdA (n : ℕ) :
    PowerSeries.map evm1 (pentProdA n) = ∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1)) := by
  rw [pentProdA, map_prod]; exact Finset.prod_congr rfl (fun i _ => map_evm1_factorE (3 * i + 1))

lemma map_evm1_pentProdB (n : ℕ) :
    PowerSeries.map evm1 (pentProdB n) = ∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 2)) := by
  rw [pentProdB, map_prod]; exact Finset.prod_congr rfl (fun i _ => map_evm1_factorE (3 * i + 2))

/-- `∏_{i≥0}(1 − q^{3i+1})`. -/
noncomputable def FAInf : PowerSeries ℤ := mk fun k => coeff k (∏ i ∈ Finset.range (k + 1), (1 - X ^ (3 * i + 1)))
/-- `∏_{i≥0}(1 − q^{3i+2})`. -/
noncomputable def FBInf : PowerSeries ℤ := mk fun k => coeff k (∏ i ∈ Finset.range (k + 1), (1 - X ^ (3 * i + 2)))

lemma map_evm1_pentProdAInf : PowerSeries.map evm1 pentProdAInf = FAInf := by
  ext m
  rw [PowerSeries.coeff_map, coeff_pentProdAInf (le_refl (m + 1)), ← PowerSeries.coeff_map,
      map_evm1_pentProdA]
  rw [FAInf, coeff_mk]

lemma map_evm1_pentProdBInf : PowerSeries.map evm1 pentProdBInf = FBInf := by
  ext m
  rw [PowerSeries.coeff_map, coeff_pentProdBInf (le_refl (m + 1)), ← PowerSeries.coeff_map,
      map_evm1_pentProdB]
  rw [FBInf, coeff_mk]

lemma map_evm1_qfacInfL_q3 : PowerSeries.map evm1 qfacInfL_q3 = E3 qfacInf := by
  ext n
  rw [qfacInfL_q3, PowerSeries.coeff_map, PowerSeries.coeff_map, evm1_C]

/-! ### the theta series at `z = −1`: `map evm1 pentTheta = pentSeries` -/

/-- the pentagonal series `Σ_{n∈ℤ} (−1)ⁿ q^{(3n²−n)/2}`, as `map evm1 pentTheta`. -/
noncomputable def pentSeries : PowerSeries ℤ := PowerSeries.map evm1 pentTheta

/-- `map evm1 pentTheta = pentSeries` (definitional; the pentagonal number series). -/
lemma map_evm1_pentTheta : PowerSeries.map evm1 pentTheta = pentSeries := rfl

end MockTheta5.JTP
