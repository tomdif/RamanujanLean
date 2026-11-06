/-
# Assembly with the off-diagonal side (`SelbergKey5`)

* `diagHypT_of_SKQF`: `SKQFHyp θ ∧ DiagApproxHyp θ ⟹ SelbergKey5.DiagHypT θ` (the diagonal clause
  for the window `φ_T` on `[T/2, 3T]`, `h = K/log T`);
* `sk_of_SKQF`: with `SelbergKey5.QuadOffHyp η B` (`4θ(1+B) < η`), `SKSplitHyp' θ`;
* `tauL_positive_proportion_of_SKQF`: with `QFHyp` and `0 < θ ≤ 1/81600`, a positive proportion of the
  zeros of `L(Δ,s)` lie on the critical line.
Level 2 on the named hypotheses.
-/
import RamanujanTau.SelbergKeyDiag.Reduce
import RamanujanTau.SelbergKey5.Reduce

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag

open Complex RamanujanTau.SelbergKey RamanujanTau.HeckeL

/-- **The diagonal clause `DiagHypT θ`** from `SKQFHyp θ` and the diagonal evaluation. -/
theorem diagHypT_of_SKQF {θ : ℝ} (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) :
    SelbergKey5.DiagHypT θ :=
  diagLag_bound_phiT hS hD

theorem sk_of_SKQF {θ η B : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hηθ : 4 * θ * (1 + B) < η)
    (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) (hO : SelbergKey5.QuadOffHyp η B) :
    SelbergKey2.SKSplitHyp' θ :=
  SelbergKey5.skSplitHyp'_of_diag hB hθ0 hηθ (diagHypT_of_SKQF hS hD) hO

/-- **Positive proportion for `L(Δ,s)`** on
`QFHyp ∧ SKQFHyp θ ∧ DiagApproxHyp θ ∧ QuadOffHyp η B`. -/
theorem tauL_positive_proportion_of_SKQF {θ η B : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hB : 0 ≤ B) (hηθ : 4 * θ * (1 + B) < η)
    (hQ : HafnerBridge.QFHyp) (hS : SKQFHyp θ) (hD : DiagApproxHyp θ)
    (hO : SelbergKey5.QuadOffHyp η B) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  SelbergKey2.tauL_positive_proportion_of_QF_split' hθ0 hθ hQ
    (sk_of_SKQF hB hθ0.le hηθ hS hD hO)

end RamanujanTau.SelbergKeyDiag
