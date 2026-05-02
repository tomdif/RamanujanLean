import RamanujanTau.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # Multiplicativity of τ

`τ : ℕ → ℤ` is **multiplicative**: `τ(mn) = τ(m) · τ(n)` for coprime `m, n`.
Mordell (1917) — proved via Hecke operators acting on the cusp form Δ.

In Mathlib, `Nat.ArithmeticFunction.IsMultiplicative` packages this property.
We state the multiplicativity theorem and expose it as a hypothesis class for
downstream use; the full Hecke-theoretic proof is deferred.
-/

namespace RamanujanTau

/-- Hypothesis class: `τ` is multiplicative.

The proof requires Hecke operators on the cusp form Δ, which depend on
infrastructure not yet in Mathlib (Hecke algebra acting on weight-12 forms,
eigenform decomposition, the fact that the space of weight-12 cusp forms is
1-dimensional spanned by Δ).

Once that infrastructure lands, this class is discharged by an `instance`. -/
class TauMultiplicative : Prop where
  /-- `τ(1) = 1` (already proven, restated for the multiplicative-function shape). -/
  tau_one_eq : τ 1 = 1
  /-- For coprime `m, n`: `τ(mn) = τ(m) · τ(n)`. -/
  mul_coprime : ∀ {m n : ℕ}, Nat.Coprime m n → τ (m * n) = τ m * τ n

/-- The trivial part — `τ(1) = 1` — is already proved. -/
theorem tauMultiplicative_one : τ 1 = 1 := tau_one

/-- Under `TauMultiplicative`, `τ` extends to a multiplicative arithmetic function
in the Mathlib sense. -/
def tauArith [TauMultiplicative] : ArithmeticFunction ℤ where
  toFun := fun n => if n = 0 then 0 else τ n
  map_zero' := by simp

theorem tauArith_apply [TauMultiplicative] {n : ℕ} (hn : n ≠ 0) :
    tauArith n = τ n := by
  simp [tauArith, hn]

/-- The Mathlib-style multiplicativity statement under our hypothesis. -/
theorem tauArith_isMultiplicative [TauMultiplicative] :
    tauArith.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · -- tauArith 1 = 1
    simp [tauArith_apply (one_ne_zero), tau_one]
  · -- coprime case
    intro m n hmn
    by_cases hm : m = 0
    · subst hm; simp [tauArith]
    by_cases hn : n = 0
    · subst hn; simp [tauArith]
    have hmn' : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    rw [tauArith_apply hmn', tauArith_apply hm, tauArith_apply hn]
    exact TauMultiplicative.mul_coprime hmn

end RamanujanTau
