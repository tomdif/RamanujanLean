/-
# `SvStripD` headline: `S4Bound 4` under `[DeligneBound]` (level 2)

`s4Bound_deligne : S4Bound 4` with `δ₀ = 1/4`, from `s4_mass` (`Bridge.lean`).
-/
import RamanujanTau.SvStripD.Bridge
import RamanujanTau.SvStripE.S4Stmt

set_option autoImplicit false

namespace RamanujanTau.SvStripD

open RamanujanTau.SvStripE (S4Bound)

/-- **S4 under Deligne**: `S4Bound 4`. -/
theorem s4Bound_deligne [DeligneBound] : S4Bound 4 := by
  obtain ⟨A, hA0, hA⟩ := s4_mass
  refine ⟨A, 1 / 4, hA0, by norm_num, by norm_num, fun y hy z hz => ?_⟩
  exact hA z (by have := hz.2.1; linarith) hz.2.2 y hy

end RamanujanTau.SvStripD
