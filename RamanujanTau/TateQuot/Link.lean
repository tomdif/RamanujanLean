/-
# `veluA`/`veluB` are Vélu's `A'`/`B'` (`RamanujanTau.Velu`)

For a Vélu kernel `κ` of `y² = x³ + Ax + B` over a field, `κ.A' = veluA A κ.S xc` and
`κ.B' = veluB A B κ.S xc yc`: the formulas used for the Tate quotients are Vélu's.
-/
import RamanujanTau.TateQuot.MuQuot
import RamanujanTau.Velu.Defs

set_option autoImplicit false

namespace TateQuot

variable {F : Type*} [Field F] [DecidableEq F] {A B : F}

theorem kernel_A' (κ : Velu.Kernel A B) : κ.A' = veluA A κ.S Velu.xc := by
  simp only [Velu.Kernel.A', Velu.Kernel.t, Velu.Kernel.tQ, veluA]

theorem kernel_B' (κ : Velu.Kernel A B) : κ.B' = veluB A B κ.S Velu.xc Velu.yc := by
  simp only [Velu.Kernel.B', Velu.Kernel.w, Velu.Kernel.uQ, Velu.Kernel.tQ, veluB]

/-- The Vélu curve of `κ` is `shortW (veluA …) (veluB …)` (same coefficients). -/
theorem kernel_curve (κ : Velu.Kernel A B) :
    (κ.curve : WeierstrassCurve F) = ⟨0, 0, 0, veluA A κ.S Velu.xc, veluB A B κ.S Velu.xc Velu.yc⟩ := by
  rw [← kernel_A', ← kernel_B']; rfl

end TateQuot
