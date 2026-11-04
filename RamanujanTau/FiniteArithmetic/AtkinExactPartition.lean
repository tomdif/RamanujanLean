import RamanujanTau.FiniteArithmetic.AtkinExact

/-!
# Exactness of Atkin–O'Brien at 13, 17, 19, 23, stated for partition numbers

Atkin–O'Brien (with `AtkinOBrienFinal.atkin_obrien_generic` and the unconditional
`SmallThreshold.ub_db`) give `κ ∈ ℤ_ℓ` with
`ℓ^b ∣ p((ℓ^(b+2) n + 1)/24) − κ p((ℓ^b n + 1)/24)` whenever `24 ∣ ℓ^b n + 1`.

Here: the modulus `ℓ^b` cannot be raised to `ℓ^(b+1)`, for any `ℓ`-adic multiplier `c`.
For every `b ≥ 1` and every `c ∈ ℤ_ℓ` there is an explicit `n` with `24 ∣ ℓ^b n + 1` and
`ℓ^(b+1) ∤ p((ℓ^(b+2) n + 1)/24) − c p((ℓ^b n + 1)/24)`
(`partition_13`, …, `partition_23`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.AtkinExactPartition

open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal

section
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- Coefficientwise divisibility of the partition series lifts to the `L`-series. -/
theorem Ll_dvd_of_pZ (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b e : ℕ) (c : ℤ_[ℓ])
    (h : ∀ t : ℕ, (ℓ : ℤ_[ℓ]) ^ e ∣ ((pZ ((ℓ : ℤ) ^ (b + 2) * t - eB ℓ (b + 2)) : ℤ) : ℤ_[ℓ]) -
      c * ((pZ ((ℓ : ℤ) ^ b * t - eB ℓ b) : ℤ) : ℤ_[ℓ])) :
    Dvd (ℓ : ℤ_[ℓ]) e (Ll ℓ (b + 2) - c • Ll ℓ b) := by
  obtain ⟨Q, -, h1, h2⟩ := L_factor h24 b
  choose y hy using h
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ])
  refine ⟨φ Q * PowerSeries.mk y, ?_⟩
  have hL : ∀ k, Ll ℓ k = φ (L ℓ k) := fun k => rfl
  have hP : φ (Pser ℓ (b + 2)) - c • φ (Pser ℓ b) = (ℓ : ℤ_[ℓ]) ^ e • PowerSeries.mk y := by
    ext t
    rw [map_sub, coeff_smul, coeff_smul, coeff_map, coeff_map, Pser, Pser, coeff_mk, coeff_mk,
      coeff_mk, smul_eq_mul, smul_eq_mul, eq_intCast, eq_intCast]
    exact hy t
  rw [hL, hL, h1, h2, map_mul, map_mul, ← mul_smul_comm, ← mul_sub, hP, mul_smul_comm]

lemma div24_cast {N : ℕ} {X : ℤ} (h : (N : ℤ) = 24 * X) : 24 ∣ N ∧ ((N / 24 : ℕ) : ℤ) = X := by
  have hd : (24 : ℕ) ∣ N := Int.natCast_dvd_natCast.mp (by rw [h]; exact dvd_mul_right _ _)
  refine ⟨hd, ?_⟩
  rw [Int.natCast_ediv, h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- The partition index attached to `t`: `ℓ^b n + 1 = 24 (ℓ^b t − e_b)`. -/
lemma index_of_t (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (hℓ24 : ℓ ≤ 24) (b t : ℕ) (ht : 1 ≤ t) :
    ∃ n : ℕ, 24 ∣ ℓ ^ b * n + 1 ∧
      (((ℓ ^ b * n + 1) / 24 : ℕ) : ℤ) = (ℓ : ℤ) ^ b * t - eB ℓ b ∧
      (((ℓ ^ (b + 2) * n + 1) / 24 : ℕ) : ℤ) = (ℓ : ℤ) ^ (b + 2) * t - eB ℓ (b + 2) := by
  set k := (b + 1) / 2 with hk
  have hkb : b ≤ 2 * k := by omega
  have hkb' : 2 * k ≤ b + 1 := by omega
  set s : ℕ := ℓ ^ (2 * k - b) with hs
  have hs24 : s ≤ 24 := by
    rcases Nat.lt_or_ge (2 * k - b) 1 with h | h
    · rw [hs, show 2 * k - b = 0 by omega]; norm_num
    · rw [hs, show 2 * k - b = 1 by omega, pow_one]; exact hℓ24
  have hls : (ℓ : ℤ) ^ b * s = (ℓ : ℤ) ^ (2 * k) := by
    rw [hs]; push_cast; rw [← pow_add]; congr 1; omega
  have hls' : (ℓ : ℤ) ^ (b + 2) * s = (ℓ : ℤ) ^ (2 * (k + 1)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_add, ← hls]; ring
  have he := ek_mul ℓ h24 k
  have he' := ek_mul ℓ h24 (k + 1)
  have hn : (((24 * t - s : ℕ)) : ℤ) = 24 * t - s := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : ((ℓ ^ b * (24 * t - s) + 1 : ℕ) : ℤ) = 24 * ((ℓ : ℤ) ^ b * t - eB ℓ b) := by
    push_cast [hn]; rw [eB, ← hk]; linear_combination -hls + he
  have h2 : ((ℓ ^ (b + 2) * (24 * t - s) + 1 : ℕ) : ℤ) =
      24 * ((ℓ : ℤ) ^ (b + 2) * t - eB ℓ (b + 2)) := by
    push_cast [hn]; rw [eB, show (b + 2 + 1) / 2 = k + 1 by omega]; linear_combination -hls' + he'
  exact ⟨24 * t - s, (div24_cast h1).1, (div24_cast h1).2, (div24_cast h2).2⟩

/-- **Generic partition form of exactness.** -/
theorem partition_of_exact (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (hℓ24 : ℓ ≤ 24)
    (hexact : ∀ b, 1 ≤ b → ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) (b + 1) (Ll ℓ (b + 2) - c • Ll ℓ b))
    (b : ℕ) (hb : 1 ≤ b) (c : ℤ_[ℓ]) :
    ∃ n : ℕ, 24 ∣ ℓ ^ b * n + 1 ∧
      ¬ (ℓ : ℤ_[ℓ]) ^ (b + 1) ∣ (Fintype.card (Nat.Partition ((ℓ ^ (b + 2) * n + 1) / 24)) : ℤ_[ℓ]) -
        c * (Fintype.card (Nat.Partition ((ℓ ^ b * n + 1) / 24)) : ℤ_[ℓ]) := by
  by_contra hcon
  push Not at hcon
  refine hexact b hb c (Ll_dvd_of_pZ h24 b (b + 1) c fun t => ?_)
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hneg : ∀ j, 1 ≤ j → (ℓ : ℤ) ^ j * ((0 : ℕ) : ℤ) - eB ℓ j < 0 := fun j hj1 => by
      have : 0 < eB ℓ j := by
        have hk := ek_mul ℓ h24 ((j + 1) / 2)
        have hpos : 1 < (ℓ : ℤ) ^ (2 * ((j + 1) / 2)) := by
          have h2 : (1 : ℤ) < ℓ := by exact_mod_cast hℓp.out.one_lt
          exact one_lt_pow₀ h2 (by omega)
        rw [eB]; linarith
      simpa using this
    rw [pZ, if_pos (hneg _ (by omega)), pZ, if_pos (hneg _ hb)]
    simp
  · obtain ⟨n, hn, e1, e2⟩ := index_of_t h24 hℓ24 b t ht
    have h := hcon n hn
    rw [← e1, ← e2, pZ_natCast, pZ_natCast]
    exact_mod_cast h

end

/-- **ℓ = 13.** For every `b ≥ 1` and `c ∈ ℤ₁₃` the Atkin–O'Brien congruence fails mod `13^(b+1)`. -/
theorem partition_13 (b : ℕ) (hb : 1 ≤ b) (c : ℤ_[13]) :
    ∃ n : ℕ, 24 ∣ 13 ^ b * n + 1 ∧
      ¬ (13 : ℤ_[13]) ^ (b + 1) ∣ (Fintype.card (Nat.Partition ((13 ^ (b + 2) * n + 1) / 24)) : ℤ_[13]) -
        c * (Fintype.card (Nat.Partition ((13 ^ b * n + 1) / 24)) : ℤ_[13]) := by
  have := partition_of_exact (ℓ := 13) Cert13.h24 (by norm_num) ExactAtkin13.exact b hb c
  exact_mod_cast this

/-- **ℓ = 17.** -/
theorem partition_17 (b : ℕ) (hb : 1 ≤ b) (c : ℤ_[17]) :
    ∃ n : ℕ, 24 ∣ 17 ^ b * n + 1 ∧
      ¬ (17 : ℤ_[17]) ^ (b + 1) ∣ (Fintype.card (Nat.Partition ((17 ^ (b + 2) * n + 1) / 24)) : ℤ_[17]) -
        c * (Fintype.card (Nat.Partition ((17 ^ b * n + 1) / 24)) : ℤ_[17]) := by
  have := partition_of_exact (ℓ := 17) Cert17.h24 (by norm_num) ExactAtkin17.exact b hb c
  exact_mod_cast this

/-- **ℓ = 19.** -/
theorem partition_19 (b : ℕ) (hb : 1 ≤ b) (c : ℤ_[19]) :
    ∃ n : ℕ, 24 ∣ 19 ^ b * n + 1 ∧
      ¬ (19 : ℤ_[19]) ^ (b + 1) ∣ (Fintype.card (Nat.Partition ((19 ^ (b + 2) * n + 1) / 24)) : ℤ_[19]) -
        c * (Fintype.card (Nat.Partition ((19 ^ b * n + 1) / 24)) : ℤ_[19]) := by
  have := partition_of_exact (ℓ := 19) Cert19.h24 (by norm_num) ExactAtkin19.exact b hb c
  exact_mod_cast this

/-- **ℓ = 23.** -/
theorem partition_23 (b : ℕ) (hb : 1 ≤ b) (c : ℤ_[23]) :
    ∃ n : ℕ, 24 ∣ 23 ^ b * n + 1 ∧
      ¬ (23 : ℤ_[23]) ^ (b + 1) ∣ (Fintype.card (Nat.Partition ((23 ^ (b + 2) * n + 1) / 24)) : ℤ_[23]) -
        c * (Fintype.card (Nat.Partition ((23 ^ b * n + 1) / 24)) : ℤ_[23]) := by
  have := partition_of_exact (ℓ := 23) Cert23.h24 (by norm_num) ExactAtkin23.exact b hb c
  exact_mod_cast this

end RamanujanTau.FiniteArithmetic.AtkinExactPartition
