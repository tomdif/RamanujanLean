import RamanujanTau.FiniteArithmetic.CertifyError31
import RamanujanTau.FiniteArithmetic.Sharp31
import RamanujanTau.FiniteArithmetic.SeriesDivisibility
import RamanujanTau.FiniteArithmetic.PartitionObstruction31

/-! The all-power recurrence and its exact starting threshold for prime 31. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Complete31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

/-- A scalar recurrence holds from B onward modulo 31^m exactly when B ≥ 2m−1. -/
theorem threshold (m B : ℕ) (hm : 1 ≤ m) :
    (∃ c : ℤ_[31], ∀ b : ℕ, B ≤ b →
      Dvd (31 : ℤ_[31]) m (Ll 31 (b + 2) - c • Ll 31 b)) ↔ 2 * m - 1 ≤ B :=
  Sharp31.threshold_of_data CertifyError31.data m B hm

/-- At every precision ≥ 2, every scalar fails at the preceding even index. -/
theorem preceding_index_fails (n : ℕ) (c : ℤ_[31]) :
    ¬ Dvd (31 : ℤ_[31]) (n + 2) (Ll 31 (2 * n + 4) - c • Ll 31 (2 * n + 2)) :=
  Sharp31.optimal_of_data CertifyError31.data n c

theorem partition_count_obstruction (n : ℕ) (c : ℤ_[31]) :
    ∃ a : ℕ, 24 ∣ 31 ^ (2 * n + 2) * a + 1 ∧
      ¬ (31 : ℤ_[31]) ^ (n + 2) ∣
        (Fintype.card (Nat.Partition ((31 ^ (2 * n + 4) * a + 1) / 24)) : ℤ_[31]) -
          c * (Fintype.card (Nat.Partition ((31 ^ (2 * n + 2) * a + 1) / 24)) : ℤ_[31]) :=
  PartitionObstruction31.count_obstruction_of_data CertifyError31.data n c

/-- The obstruction concerns actual partition coefficients, after cancelling
the common Euler product. `pZ` is the partition count, extended by zero at negative indices. -/
theorem partition_obstruction (n : ℕ) (c : ℤ_[31]) : ∃ t : ℕ,
    ¬ (31 : ℤ_[31]) ^ (n + 2) ∣
      (pZ ((31 : ℤ) ^ (2 * n + 4) * t - eB 31 (2 * n + 4)) : ℤ_[31]) -
        c * (pZ ((31 : ℤ) ^ (2 * n + 2) * t - eB 31 (2 * n + 2)) : ℤ_[31]) := by
  by_contra hn
  push_neg at hn
  apply preceding_index_fails n c
  apply (partition_series_dvd_iff (by decide : 24 * δ 31 + 1 = 31 ^ 2)
    (n + 2) (2 * n + 2) c).mpr
  simpa only [Nat.add_assoc] using hn

/-- The same 31-adic multiplier has an error of exactly the predicted order
at every even index. -/
theorem even_exact : ∃ κ : ℤ_[31], (∃ d : ℤ_[31], κ = 30 + 31 * d) ∧
    ∀ n : ℕ,
      Dvd (31 : ℤ_[31]) (n + 1) (Ll 31 (2 * n + 4) - κ • Ll 31 (2 * n + 2)) ∧
      ¬ Dvd (31 : ℤ_[31]) (n + 2) (Ll 31 (2 * n + 4) - κ • Ll 31 (2 * n + 2)) :=
  Sharp31.even_exact_of_data CertifyError31.data

/-- The exact threshold for actual partition counts modulo every power of 31. -/
theorem partition_threshold (m B : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    (∃ c : ℤ_[31], ∀ b : ℕ, B ≤ b → ∀ a : ℕ, 24 ∣ 31 ^ b * a + 1 →
      (31 : ℤ_[31]) ^ m ∣
        (Fintype.card (Nat.Partition ((31 ^ (b + 2) * a + 1) / 24)) : ℤ_[31]) -
          c * (Fintype.card (Nat.Partition ((31 ^ b * a + 1) / 24)) : ℤ_[31])) ↔
      2 * m - 1 ≤ B :=
  PartitionObstruction31.count_threshold_of_data CertifyError31.data m B hm hB

end RamanujanTau.FiniteArithmetic.Complete31
