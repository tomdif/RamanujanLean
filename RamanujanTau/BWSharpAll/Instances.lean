import RamanujanTau.BWSharpAll.FirstStep
import RamanujanTau.FiniteArithmetic.Rank607Threshold
import RamanujanTau.FiniteArithmetic.ExactThreshold

/-!
# Instances of the first-step non-congruence

From the existing kernel-checked thresholds `b₆₀₇(2) = 3` and `b₂₉(m) = 2m − 1`: there is no
congruence `p(ℓn − (ℓ²−1)/24) ≡ Σ cᵢ p(ℓ^{2i+3}n − (ℓ^{2i+4}−1)/24) (mod ℓ²)` at `ℓ = 607`
or `ℓ = 29`. In particular the rank anomaly at 607 does not affect the first sharpness step.
-/

set_option autoImplicit false

namespace RamanujanTau.BWSharpAll
open BoylanWebb

theorem no_first_step_congruence_607 : ¬ ∃ c : ℕ →₀ ZMod (607 ^ 2), ∀ n : ℕ,
    ((pZ ((607 : ℤ) * n - ek 607 1) : ℤ) : ZMod (607 ^ 2)) =
      c.sum fun i a => a * ((pZ ((607 : ℤ) ^ (2 * (1 + i) + 1) * n - ek 607 (i + 2)) : ℤ) :
        ZMod (607 ^ 2)) :=
  (bEll_two_eq_three_iff (ℓ := 607) (by norm_num)).mp
    FiniteArithmetic.Rank607Threshold.bEll_607_two

theorem no_first_step_congruence_29 : ¬ ∃ c : ℕ →₀ ZMod (29 ^ 2), ∀ n : ℕ,
    ((pZ ((29 : ℤ) * n - ek 29 1) : ℤ) : ZMod (29 ^ 2)) =
      c.sum fun i a => a * ((pZ ((29 : ℤ) ^ (2 * (1 + i) + 1) * n - ek 29 (i + 2)) : ℤ) :
        ZMod (29 ^ 2)) :=
  (bEll_two_eq_three_iff (ℓ := 29) (by norm_num)).mp
    (FiniteArithmetic.Exact29.bEll_29 2 (by norm_num))

end RamanujanTau.BWSharpAll
