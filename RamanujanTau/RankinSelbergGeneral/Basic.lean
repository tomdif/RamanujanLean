/-
# An abstract bounded continuous `SL₂(ℤ)`-invariant function on `ℍ`

The horocycle-equidistribution proof of `EisensteinReal/Horo*` uses only that
`G = |Δ|²y¹²` is continuous, nonnegative, bounded and `SL₂(ℤ)`-invariant (no decay at the
cusp is needed: the cusp rectangle is handled by the sup bound `M`). We package those four
properties in a class `HoroFn`, so that the copied proof (`GMain`, `GFinal`, `GIdent`) runs
verbatim for any such function, in particular for `G_f = |f|²y^k`, `f` a level-one cusp form.
-/
import RamanujanTau.EisensteinReal.HoroSandwich
import RamanujanTau.EisensteinReal.Asymptotic

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergGeneral

open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- A continuous, nonnegative, bounded, `SL₂(ℤ)`-invariant function on `ℍ`. -/
class HoroFn where
  G : ℍ → ℝ
  continuous_G : Continuous G
  G_nonneg : ∀ z, 0 ≤ G z
  exists_G_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, G z ≤ M
  G_smul : ∀ (g : SL(2, ℤ)) (z : ℍ), G (g • z) = G z

open HoroFn

variable [HoroFn]

/-- `∫_𝓕 G dx dy / y²` over the standard fundamental domain `|x| ≤ 1/2, x² + y² ≥ 1`. -/
noncomputable def petNormSq : ℝ :=
  ∫ p : ℝ × ℝ in {p : ℝ × ℝ | 0 < p.2 ∧ |p.1| ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2},
    G (UpperHalfPlane.ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) / p.2 ^ 2

end RamanujanTau.RankinSelbergGeneral
