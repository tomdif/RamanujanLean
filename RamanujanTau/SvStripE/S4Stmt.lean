/-
# `SvStripE`: the named S4 hypothesis (stable statement; proved in `SvStripD`)

**`S4Bound c₁`**: there are `A ≥ 0` and `0 < δ₀ < 1` such that for all `y ≥ 2` and `z ∈ stripR δ₀`

    Σ_{d≤y²} ‖W^{[1−iz]}(d)‖ · (Σ_{u₁,u₂≤y} ‖Γ^z_d(u₁,u₂)‖)²  ≤  A · y^{c₁|Im z|} · log y.

The real case (`z = 0`) is `QFProof.QEuler Wd (Γc Ud) 1`.  `SvStripD.s4_mass` (under
`[DeligneBound]`) has exactly this shape with `c₁ = 4` on `−1/4 ≤ Im z ≤ 0` (so `δ₀ = 1/4`).
-/
import RamanujanTau.SvStripC.Defs
import RamanujanTau.SKQFProof.Bound

set_option autoImplicit false

namespace RamanujanTau.SvStripE

open Complex Finset
open RamanujanTau.SvStripA (WdC)
open RamanujanTau.SvStripC (Γz)
open RamanujanTau.SKQFProof (stripR)

/-- **The twisted Euler-mass bound (S4)**, with `y`-exponent `c₁|Im z|`. -/
def S4Bound (c₁ : ℝ) : Prop :=
  ∃ A δ₀ : ℝ, 0 ≤ A ∧ 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ y : ℕ, 2 ≤ y → ∀ z ∈ stripR δ₀,
    ∑ d ∈ Icc 1 (y ^ 2), ‖WdC (1 - z * I) d‖ *
        (∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖Γz z d u₁ u₂‖) ^ 2 ≤
      A * Real.exp (c₁ * |z.im| * Real.log y) * Real.log y

end RamanujanTau.SvStripE
