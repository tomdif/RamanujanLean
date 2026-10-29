import RamanujanTau.FiniteArithmetic.Sharp29
import RamanujanTau.FiniteArithmetic.SeriesDivisibility

/-! Translate the even-index obstruction into actual partition cardinalities. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.PartitionObstruction29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal ErrorDynamics29

lemma eB_even (k : ℕ) : eB 29 (2 * k) = ek 29 k := by
  unfold eB
  congr 1
  omega

lemma ek_pos (k : ℕ) (hk : 1 ≤ k) : 0 < ek 29 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [ek_succ 29 (by decide)]
  have hp : 0 < (29 : ℤ) ^ (2 * j) := pow_pos (by norm_num) _
  have hn := BoylanWebb.ek_nonneg 29 j
  change 0 < (29 : ℤ) ^ (2 * j) * 35 + ek 29 j
  omega

lemma natural_index (k t : ℕ) (ht : 1 ≤ t) :
    ((29 : ℤ) ^ (2 * k) * t - ek 29 k) =
      (((29 ^ (2 * k) * (24 * t - 1) + 1) / 24 : ℕ) : ℤ) := by
  have h := ek_mul 29 (by decide) k
  have ht' : (1 : ℕ) ≤ 24 * t := by omega
  push_cast
  rw [Nat.cast_sub ht']
  push_cast
  have he : (29 : ℤ) ^ (2 * k) * (24 * t - 1) + 1 =
      24 * ((29 : ℤ) ^ (2 * k) * t - ek 29 k) := by linear_combination h
  rw [he, Int.mul_ediv_cancel_left _ (by norm_num)]

lemma index_valid (k t : ℕ) (ht : 1 ≤ t) : 24 ∣ 29 ^ (2 * k) * (24 * t - 1) + 1 := by
  have h := ek_mul 29 (by decide) k
  have ht' : (1 : ℕ) ≤ 24 * t := by omega
  have he : (29 : ℤ) ^ (2 * k) * ((24 * t - 1 : ℕ) : ℤ) + 1 =
      24 * ((29 : ℤ) ^ (2 * k) * t - ek 29 k) := by
    rw [Nat.cast_sub ht']
    push_cast
    linear_combination h
  have hd : (24 : ℤ) ∣ (29 : ℤ) ^ (2 * k) * ((24 * t - 1 : ℕ) : ℤ) + 1 := ⟨_, he⟩
  exact_mod_cast hd

/-- Every attempted multiplier has a counterexample in the partition progression
one index before the sufficient threshold. -/
theorem count_obstruction_of_data (data : Data) (n : ℕ) (c : ℤ_[29]) :
    ∃ a : ℕ, 24 ∣ 29 ^ (2 * n + 2) * a + 1 ∧
      ¬ (29 : ℤ_[29]) ^ (n + 2) ∣
        (Fintype.card (Nat.Partition ((29 ^ (2 * n + 4) * a + 1) / 24)) : ℤ_[29]) -
          c * (Fintype.card (Nat.Partition ((29 ^ (2 * n + 2) * a + 1) / 24)) : ℤ_[29]) := by
  have hex : ∃ t : ℕ, ¬ (29 : ℤ_[29]) ^ (n + 2) ∣
      (pZ ((29 : ℤ) ^ (2 * n + 4) * t - eB 29 (2 * n + 4)) : ℤ_[29]) -
        c * (pZ ((29 : ℤ) ^ (2 * n + 2) * t - eB 29 (2 * n + 2)) : ℤ_[29]) := by
    by_contra hn
    push_neg at hn
    apply Sharp29.optimal_of_data data n c
    apply (partition_series_dvd_iff (by decide : 24 * δ 29 + 1 = 29 ^ 2)
      (n + 2) (2 * n + 2) c).mpr
    simpa only [Nat.add_assoc] using hn
  obtain ⟨t, ht⟩ := hex
  have h2 : 2 * n + 2 = 2 * (n + 1) := by omega
  have h4 : 2 * n + 4 = 2 * (n + 2) := by omega
  rw [h2, h4, eB_even, eB_even] at ht
  have htpos : 1 ≤ t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0] at ht
    simp only [Nat.cast_zero, mul_zero, zero_sub,
      pZ_neg (neg_neg_of_pos (ek_pos (n + 2) (by omega))),
      pZ_neg (neg_neg_of_pos (ek_pos (n + 1) (by omega))),
      Int.cast_zero, mul_zero, sub_zero, dvd_zero, not_true_eq_false] at ht
  refine ⟨24 * t - 1, ?_, ?_⟩
  · rw [h2]
    exact index_valid (n + 1) t htpos
  · rw [natural_index (n + 2) t htpos, natural_index (n + 1) t htpos,
      pZ_natCast, pZ_natCast] at ht
    rw [h2, h4]
    exact_mod_cast ht

/-- Exact threshold for the partition congruence itself, with positive starting indices. -/
theorem count_threshold_of_data (data : Data) (m B : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    (∃ c : ℤ_[29], ∀ b : ℕ, B ≤ b → ∀ a : ℕ, 24 ∣ 29 ^ b * a + 1 →
      (29 : ℤ_[29]) ^ m ∣
        (Fintype.card (Nat.Partition ((29 ^ (b + 2) * a + 1) / 24)) : ℤ_[29]) -
          c * (Fintype.card (Nat.Partition ((29 ^ b * a + 1) / 24)) : ℤ_[29])) ↔
      2 * m - 1 ≤ B := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra h
    have hm2 : 2 ≤ m := by omega
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    obtain ⟨a, ha, hfail⟩ := count_obstruction_of_data data n c
    apply hfail
    simpa only [Nat.add_assoc] using hc (2 * n + 2) (by omega) a ha
  · intro hb
    obtain ⟨κ, _, hκ⟩ := AllPowers29.partition_padic
    exact ⟨κ, fun b hb' a ha => hκ m hm b (by omega) a ha⟩

end RamanujanTau.FiniteArithmetic.PartitionObstruction29
