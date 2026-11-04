/-
# Sub-Hecke bound for τ — headline (conditional only on the Poincaré-series formula)

`tau_isBigO_47_8_of_poincare`: if `PoincareFormula` holds, then `τ(n) = O(n^{47/8 + ε})` for all
`ε > 0`. The Kloosterman-sum input (Kloosterman 1927, `|S(1,n;c)| ≪ c^{3/4+δ}`) is fully proved
(`kloostermanBound_three_quarters`).
-/
import RamanujanTau.TauBound.KlAssembly

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Filter Asymptotics

/-- **Kloosterman's sub-Hecke bound**, conditional on the Poincaré-series formula only. -/
theorem tau_isBigO_47_8_of_poincare (hP : PoincareFormula) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) :=
  tau_isBigO_47_8 kloostermanBound_three_quarters hP ε hε

end RamanujanTau.TauBound
