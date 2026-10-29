import RamanujanTau.FiniteArithmetic.CertifyError29
import RamanujanTau.FiniteArithmetic.Sharp29
import RamanujanTau.FiniteArithmetic.SeriesDivisibility
import RamanujanTau.FiniteArithmetic.PartitionObstruction29

/-! The all-power recurrence and its exact starting threshold for prime 29. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Complete29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

/-- A scalar recurrence holds from B onward modulo 29^m exactly when B ≥ 2m−1. -/
theorem threshold (m B : ℕ) (hm : 1 ≤ m) :
    (∃ c : ℤ_[29], ∀ b : ℕ, B ≤ b →
      Dvd (29 : ℤ_[29]) m (Ll 29 (b + 2) - c • Ll 29 b)) ↔ 2 * m - 1 ≤ B :=
  Sharp29.threshold_of_data CertifyError29.data m B hm

/-- At every precision ≥ 2, every scalar fails at the preceding even index. -/
theorem preceding_index_fails (n : ℕ) (c : ℤ_[29]) :
    ¬ Dvd (29 : ℤ_[29]) (n + 2) (Ll 29 (2 * n + 4) - c • Ll 29 (2 * n + 2)) :=
  Sharp29.optimal_of_data CertifyError29.data n c

theorem partition_count_obstruction (n : ℕ) (c : ℤ_[29]) :
    ∃ a : ℕ, 24 ∣ 29 ^ (2 * n + 2) * a + 1 ∧
      ¬ (29 : ℤ_[29]) ^ (n + 2) ∣
        (Fintype.card (Nat.Partition ((29 ^ (2 * n + 4) * a + 1) / 24)) : ℤ_[29]) -
          c * (Fintype.card (Nat.Partition ((29 ^ (2 * n + 2) * a + 1) / 24)) : ℤ_[29]) :=
  PartitionObstruction29.count_obstruction_of_data CertifyError29.data n c

/-- The obstruction concerns actual partition coefficients, after cancelling
the common Euler product. `pZ` is the partition count, extended by zero at negative indices. -/
theorem partition_obstruction (n : ℕ) (c : ℤ_[29]) : ∃ t : ℕ,
    ¬ (29 : ℤ_[29]) ^ (n + 2) ∣
      (pZ ((29 : ℤ) ^ (2 * n + 4) * t - eB 29 (2 * n + 4)) : ℤ_[29]) -
        c * (pZ ((29 : ℤ) ^ (2 * n + 2) * t - eB 29 (2 * n + 2)) : ℤ_[29]) := by
  by_contra hn
  push_neg at hn
  apply preceding_index_fails n c
  apply (partition_series_dvd_iff (by decide : 24 * δ 29 + 1 = 29 ^ 2)
    (n + 2) (2 * n + 2) c).mpr
  simpa only [Nat.add_assoc] using hn

/-- The same 29-adic multiplier has an error of exactly the predicted order
at every even index. -/
theorem even_exact : ∃ κ : ℤ_[29], (∃ d : ℤ_[29], κ = 3 + 29 * d) ∧
    ∀ n : ℕ,
      Dvd (29 : ℤ_[29]) (n + 1) (Ll 29 (2 * n + 4) - κ • Ll 29 (2 * n + 2)) ∧
      ¬ Dvd (29 : ℤ_[29]) (n + 2) (Ll 29 (2 * n + 4) - κ • Ll 29 (2 * n + 2)) :=
  Sharp29.even_exact_of_data CertifyError29.data

/-- The exact threshold for actual partition counts modulo every power of 29. -/
theorem partition_threshold (m B : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    (∃ c : ℤ_[29], ∀ b : ℕ, B ≤ b → ∀ a : ℕ, 24 ∣ 29 ^ b * a + 1 →
      (29 : ℤ_[29]) ^ m ∣
        (Fintype.card (Nat.Partition ((29 ^ (b + 2) * a + 1) / 24)) : ℤ_[29]) -
          c * (Fintype.card (Nat.Partition ((29 ^ b * a + 1) / 24)) : ℤ_[29])) ↔
      2 * m - 1 ≤ B :=
  PartitionObstruction29.count_threshold_of_data CertifyError29.data m B hm hB

end RamanujanTau.FiniteArithmetic.Complete29
