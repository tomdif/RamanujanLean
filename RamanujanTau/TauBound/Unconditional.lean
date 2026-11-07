/-
# Kloosterman's sub-Hecke bound for Ramanujan's τ, unconditionally

`τ(n) = O(n^{47/8+ε})` for every `ε > 0` (Kloosterman 1927). All inputs are proved:
* the Kloosterman-sum bound `|S(1,n;c)| ≪ c^{3/4+δ}` (`KlAssembly.lean`);
* the Poincaré unfolding (`Unfold.lean`) and `a₁(P₁) ≠ 0` (`Numerics.lean`);
* `P₁` is a weight-12 cusp form for `SL₂(ℤ)` (`CuspForm.lean`).
-/
import RamanujanTau.TauBound.Final
import RamanujanTau.TauBound.CuspForm

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Filter Asymptotics

/-- **Kloosterman's bound `τ(n) = O(n^{47/8+ε})`, unconditional.** -/
theorem tau_isBigO_47_8_unconditional (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) :=
  tau_isBigO_47_8_of_cuspForm poincareIsCuspForm ε hε

end RamanujanTau.TauBound

#print axioms RamanujanTau.TauBound.tau_isBigO_47_8_unconditional
#print axioms RamanujanTau.TauBound.poincareIsCuspForm
