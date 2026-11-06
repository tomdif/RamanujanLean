/-
# `[SL₂(ℤ) : Γ₀(q)] ≤ q⁴` (crude, for the coset count in the Hölder step)

`Γ(q) ≤ Γ₀(q)` and `Γ(q) = ker(SL₂(ℤ) → SL₂(ℤ/q))`, so the index of `Γ₀(q)` divides that of
`Γ(q)`, which is at most `|SL₂(ℤ/q)| ≤ |M₂(ℤ/q)| = q⁴`.
-/
import RamanujanTau.SCS2Coprime.Gamma0

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open CongruenceSubgroup
open scoped MatrixGroups

lemma Gamma_le_Gamma0 (q : ℕ) : Gamma q ≤ Gamma0 q := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma0_mem]
  exact hγ.2.2.1

theorem index_Gamma_le (q : ℕ) (hq : 1 ≤ q) : (Gamma q).index ≤ q ^ 4 := by
  haveI : NeZero q := ⟨by omega⟩
  unfold Gamma
  rw [Subgroup.index_ker]
  calc Nat.card (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).range
      ≤ Nat.card (SL(2, ZMod q)) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card (Matrix (Fin 2) (Fin 2) (ZMod q)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = q ^ 4 := by
        show Nat.card (Fin 2 → Fin 2 → ZMod q) = q ^ 4
        rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin]; ring

/-- **`[SL₂(ℤ) : Γ₀(q)] ≤ q⁴`**. -/
theorem index_Gamma0_le (q : ℕ) (hq : 1 ≤ q) : (Gamma0 q).index ≤ q ^ 4 := by
  haveI : NeZero q := ⟨by omega⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero))
    (Subgroup.index_dvd_of_le (Gamma_le_Gamma0 q))).trans (index_Gamma_le q hq)

/-- The number of right cosets `Γ₀(q)\SL₂(ℤ)` is at most `q⁴`. -/
theorem card_RCos_Gamma0_le (q : ℕ) (hq : 1 ≤ q) : Nat.card (RCos (Gamma0 q)) ≤ q ^ 4 := by
  have e : Nat.card (RCos (Gamma0 q)) = (Gamma0 q).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)
  rw [e]; exact index_Gamma0_le q hq

end RamanujanTau.SCS2Coprime
