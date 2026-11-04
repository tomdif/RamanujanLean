/-
# Headline: `τ(n) = O(n^{47/8+ε})` conditional only on `PoincareIsCuspForm`

`PoincareUnfolding` (`Unfold.lean`) and `PoincareFirstCoeffNeZero` (`Numerics.lean`) are proved;
the Kloosterman bound is proved (`KlAssembly.lean`).
-/
import RamanujanTau.TauBound.Numerics

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Filter Asymptotics

/-- **Kloosterman's sub-Hecke bound**, conditional only on `P₁` being a cusp form. -/
theorem tau_isBigO_47_8_of_cuspForm (hA : PoincareIsCuspForm) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) :=
  tau_isBigO_47_8_of_cusp_and_coeff hA poincareFirstCoeffNeZero ε hε

end RamanujanTau.TauBound
