/-
# Sign changes of τ with the sharp Rankin–Selberg exponent (`δ < 1/5`)

Feeds `RankinSharp.rankinSelberg_power_saving_sharp` (`O(N^{1−δ})` for every `0 < δ < 1/5`)
into the δ-parametrized `WindowGeneral` / `CountGeneral`:

* `tau_sign_change_short_interval_sharp`: for every `θ ∈ (4/5, 1]`, both signs of τ occur in
  every `(x, x+h]` with `A·x^θ ≤ h ≤ x`, `x ≥ X₀`.          (windows `x^{4/5+ε}`)
* `card_signChanges_ge_sharp`: for every `η ∈ (0, 1/5)`, `#signChanges X ≥ c·X^η`.
                                                          (`≫ X^{1/5−ε}` sign changes)

The Hecke × Weil loss is `x^{3/4+ε}`, so with `δ < 1/5` the RS error is still the bottleneck;
any `δ > 1/4` would give windows `x^{3/4+ε}` and `≫ X^{1/4−ε}` (the Hecke × Weil limit).
-/
import RamanujanTau.TauSigns.CountGeneral
import RamanujanTau.RankinSharp.Sharp

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Finset
open scoped Real

/-- **Both signs in every `(x, x + A x^θ]`, any `θ > 4/5`.** -/
theorem tau_sign_change_short_interval_sharp {θ : ℝ} (hθ : 4 / 5 < θ) (hθ1 : θ ≤ 1) :
    ∃ A X₀ : ℝ, 0 < A ∧ ∀ x h : ℕ, X₀ ≤ x → A * (x : ℝ) ^ θ ≤ h → h ≤ x →
      (∃ m ∈ Ioc x (x + h), 0 < tau m) ∧ (∃ n ∈ Ioc x (x + h), tau n < 0) := by
  set δ : ℝ := ((1 - θ) + 1 / 5) / 2
  exact tau_sign_change_short_interval_of_power_saving (δ := δ) (by linarith) hθ1
    (by simp only [δ]; linarith)
    (RankinSharp.rankinSelberg_power_saving_sharp (by simp only [δ]; linarith)
      (by simp only [δ]; linarith))

/-- **`≫ X^η` sign changes of τ in `[1, X]`, any `η < 1/5`.** -/
theorem card_signChanges_ge_sharp {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 5) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ^ η ≤ (signChanges X).card := by
  have h := card_signChanges_ge_of_power_saving (δ := η) (θ := 1 - η) (by linarith)
    (by linarith) le_rfl (RankinSharp.rankinSelberg_power_saving_sharp hη0 hη)
  simpa using h

/-- Concrete instance: windows `x^{81/100}`. -/
example : ∃ A X₀ : ℝ, 0 < A ∧ ∀ x h : ℕ, X₀ ≤ x → A * (x : ℝ) ^ (81 / 100 : ℝ) ≤ h → h ≤ x →
    (∃ m ∈ Ioc x (x + h), 0 < tau m) ∧ (∃ n ∈ Ioc x (x + h), tau n < 0) :=
  tau_sign_change_short_interval_sharp (by norm_num) (by norm_num)

/-- Concrete instance: `≫ X^{19/100}` sign changes. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
    c * (X : ℝ) ^ (19 / 100 : ℝ) ≤ (signChanges X).card :=
  card_signChanges_ge_sharp (by norm_num) (by norm_num)

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.tau_sign_change_short_interval_sharp
#print axioms RamanujanTau.TauSigns.card_signChanges_ge_sharp
