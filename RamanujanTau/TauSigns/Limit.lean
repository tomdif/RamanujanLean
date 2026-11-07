/-
# Sign changes of τ at the Hecke × Weil limit (`x^{3/4+ε}` windows)

Feeds `Stirling.rankinSelberg_power_saving_third` (Rankin–Selberg error `O(N^{1−δ})` for every
`0 < δ < 1/3`) into the δ-parametrized `WindowGeneral` / `CountGeneral`. Since `δ` can be taken
above `1/4`, the Rankin–Selberg error is no longer the bottleneck and both results reach the
Hecke × Weil limit of this method:

* `tau_sign_change_short_interval_limit`: for every `θ ∈ (3/4, 1]`, both signs of τ occur in
  every `(x, x+h]` with `A·x^θ ≤ h ≤ x`, `x ≥ X₀`.          (windows `x^{3/4+ε}`)
* `card_signChanges_ge_limit`: for every `η ∈ (0, 1/4)`, `#signChanges X ≥ c·X^η`.
                                                          (`≫ X^{1/4−ε}` sign changes)

Going below `x^{3/4}` would need Deligne's bound in place of Weil's.
-/
import RamanujanTau.TauSigns.CountGeneral
import RamanujanTau.Stirling.Main

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Finset
open scoped Real

/-- **Both signs in every `(x, x + A x^θ]`, any `θ > 3/4`.** -/
theorem tau_sign_change_short_interval_limit {θ : ℝ} (hθ : 3 / 4 < θ) (hθ1 : θ ≤ 1) :
    ∃ A X₀ : ℝ, 0 < A ∧ ∀ x h : ℕ, X₀ ≤ x → A * (x : ℝ) ^ θ ≤ h → h ≤ x →
      (∃ m ∈ Ioc x (x + h), 0 < tau m) ∧ (∃ n ∈ Ioc x (x + h), tau n < 0) :=
  tau_sign_change_short_interval_of_power_saving (δ := 3 / 10) hθ hθ1 (by linarith)
    (Stirling.rankinSelberg_power_saving_third (by norm_num) (by norm_num))

/-- **`≫ X^η` sign changes of τ in `[1, X]`, any `η < 1/4`.** -/
theorem card_signChanges_ge_limit {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ^ η ≤ (signChanges X).card := by
  have h := card_signChanges_ge_of_power_saving (δ := 3 / 10) (θ := 1 - η) (by linarith)
    (by linarith) (by linarith)
    (Stirling.rankinSelberg_power_saving_third (by norm_num) (by norm_num))
  simpa using h

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.tau_sign_change_short_interval_limit
#print axioms RamanujanTau.TauSigns.card_signChanges_ge_limit
