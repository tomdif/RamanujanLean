/-
# Hafner's theorem for `L(Δ,s)` under Deligne's bound

`tauL_positive_proportion_deligne`: assuming only `[DeligneBound]` (`τ(p)² ≤ 4p¹¹` at primes,
Deligne 1974), a positive proportion of the nontrivial zeros of `L(Δ,s)` lie on `Re s = 6`:
for some `c > 0` and all large `T`, there are at least `c·N(3T)` distinct zeros `6 + iγ`,
`0 < γ ≤ 3T`, where `N` is the Riemann–von Mangoldt count of all nontrivial zeros.

Composition of `SvStripD.s4Bound_deligne` (Euler-mass bound in the strip) with
`SvStripE.tauL_positive_proportion_deligne_S4` (Selberg's method: mollified second moment,
key lemma off-diagonal, diagonal, and the arithmetic hypothesis via the strip contour).
-/
import RamanujanTau.SvStripD.Main
import RamanujanTau.SvStripE.Main

set_option autoImplicit false

namespace RamanujanTau.HafnerFinal

open Complex RamanujanTau.HeckeL

theorem tauL_positive_proportion_deligne [DeligneBound] :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  SvStripE.tauL_positive_proportion_deligne_S4 (by norm_num) SvStripD.s4Bound_deligne

end RamanujanTau.HafnerFinal

#print axioms RamanujanTau.HafnerFinal.tauL_positive_proportion_deligne
