/-
# Sign pattern of `f(q)` for every `n ≥ 1`, together with Dragonette's asymptotic

`Andrews.alpha_sign` (elementary, `Andrews/Sign.lean`) upgrades `Dragonette.dragonette_sign`
(`∀ᶠ n in atTop`, from the circle method) to every `n ≥ 1`.
-/
import RamanujanTau.Andrews.Sign
import RamanujanTau.Dragonette.Main

set_option autoImplicit false

namespace Andrews
open Filter

/-- `(−1)^{n+1} α(n) > 0` for every `n ≥ 1`, in the real-valued normalization of `Dragonette`. -/
theorem dragonette_sign_all {n : ℕ} (hn : 1 ≤ n) : 0 < (-1) ^ (n + 1) * (Dragonette.α n : ℝ) := by
  have h := alpha_sign hn
  have : ((-1) ^ (n + 1) * α n : ℤ) = (-1) ^ (n + 1) * Dragonette.α n := rfl
  exact_mod_cast this ▸ h

/-- Both statements at once: `α(n) ~ (−1)^{n+1} e^{π√(n/6)}/(2√n)`, and the sign holds for every `n ≥ 1`. -/
theorem dragonette_with_sign :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (Dragonette.α n : ℝ))
      (fun n : ℕ => (-1) ^ (n + 1) * Real.exp (Real.pi * √(n / 6)) / (2 * √(n : ℝ))) ∧
    ∀ n : ℕ, 1 ≤ n → 0 < (-1) ^ (n + 1) * (Dragonette.α n : ℝ) :=
  ⟨Dragonette.dragonette_isEquivalent, fun _ hn => dragonette_sign_all hn⟩

end Andrews
