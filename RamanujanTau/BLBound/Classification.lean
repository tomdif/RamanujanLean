import RamanujanTau.BLBound.AhlgrenBoylan
import RamanujanTau.LogConcaveTable
import RamanujanTau.PartitionCongruenceMod11

/-!
# Every Ramanujan congruence

For a prime `ℓ` and `β < ℓ`, `ℓ ∣ p(ℓn + β)` for all `n` exactly when `(ℓ, β)` is `(5, 4)`, `(7, 5)` or `(11, 6)`.
Primes `ℓ ≥ 13` are `ahlgren_boylan`; below `13` every other class has a small witness.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound

/-- A witness that a class is not a congruence, read from the table of `p(n)`. -/
private lemma not_dvd_of_table {ℓ β n : ℕ} (hm : ℓ * n + β ≤ 19)
    (hd : ¬ (ℓ : ℤ) ∣ LogConcave.getP (LogConcave.ptab 19) 19 (ℓ * n + β)) :
    ¬ ∀ n : ℕ, ℓ ∣ Fintype.card (Nat.Partition (ℓ * n + β)) := by
  intro hall
  apply hd
  rw [LogConcave.getP_eq hm]
  exact_mod_cast hall n

/-- **The classification of Ramanujan congruences.** -/
theorem ramanujan_congruence_iff {ℓ β : ℕ} (hp : ℓ.Prime) (hβ : β < ℓ) :
    (∀ n : ℕ, ℓ ∣ Fintype.card (Nat.Partition (ℓ * n + β))) ↔
      (ℓ = 5 ∧ β = 4) ∨ (ℓ = 7 ∧ β = 5) ∨ (ℓ = 11 ∧ β = 6) := by
  constructor
  · intro hall
    by_cases h13 : 13 ≤ ℓ
    · haveI : Fact ℓ.Prime := ⟨hp⟩
      exact absurd hall (ahlgren_boylan h13 hβ)
    · have hl : ℓ < 13 := by omega
      have hc : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 11 := by
        interval_cases ℓ <;> revert hp <;> norm_num
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> interval_cases β <;> first
        | (simp; done)
        | exact absurd hall (not_dvd_of_table (n := 0) (by norm_num) (by decide +kernel))
        | exact absurd hall (not_dvd_of_table (n := 1) (by norm_num) (by decide +kernel))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact MockTheta5.JTP.five_dvd_partition_card
    · exact MockTheta5.JTP.seven_dvd_partition_card
    · exact MockTheta5.JTP.eleven_dvd_partition_card

end RamanujanTau.BLBound
