import RamanujanTau.TateFormal.Expand
import RamanujanTau.TateFormal.Core
import RamanujanTau.HasseInv.Modular

/-!
# Deligne's congruence for the Tate curve: `H(Tate ⊗ 𝔽_p) = 1`

The Tate parametrization `x(u, q)`, `y(u, q)` (proved from Mathlib's `℘'² = 4℘³ − g₂℘ − g₃` via the
`q`-expansions of `℘`, `℘'`, `G₄`, `G₆`, then transferred to a formal identity over `ℤ[u,u⁻¹]⟦q⟧`)
expanded at `u = 1 + T` gives a point of `TateBar p` over `𝔽_p⟦q⟧((T))` with `(1+T) dx/dT = 2y + x`,
i.e. the formal group of the Tate curve is multiplicative; the Cartier lemma then gives `H = 1`.
-/

set_option autoImplicit false

namespace TateFormal
open MvPowerSeries

/-- **Deligne's congruence for the Tate curve**: the Hasse invariant of the Tate curve over
`𝔽_p⟦q⟧` is `1` (`p ≥ 5`). -/
theorem hasseH_TateBar (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    HasseInv.hasseH p (HasseInv.TateBar p) = 1 := by
  haveI := HasseInv.charP_PS p
  have hE := E4_K (K := ZMod p)
  have hD := D_K (K := ZMod p)
  refine hasseH_eq_one_of_param p (by omega) (HasseInv.TateBar p) ?_ ?_ ?_
    (Xs (ZMod p)) (Qs (ZMod p)) cc_Xs cc_Qs ?_ hD
  · simp [HasseInv.TateBar, TateCurve.Tate]
  · simp [HasseInv.TateBar, TateCurve.Tate]
  · simp [HasseInv.TateBar, TateCurve.Tate]
  · simpa [HasseInv.TateBar, TateCurve.Tate] using hE

end TateFormal

/-- the statement in the `HasseInv` namespace, as in `HasseInv/Modular_WIP.lean`. -/
theorem HasseInv.hasseH_TateBar' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    HasseInv.hasseH p (HasseInv.TateBar p) = 1 :=
  TateFormal.hasseH_TateBar p hp5

