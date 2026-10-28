import RamanujanTau.BoylanWebb.Cert13
import RamanujanTau.BoylanWebb.Cert17
import RamanujanTau.BoylanWebb.Cert19
import RamanujanTau.BoylanWebb.Cert23

/-!
# Boylan–Webb inputs mod `ℓ` for `ℓ ∈ {13, 17, 19, 23}` (the `hbase`/`hnz` inputs of `AtkinOBrien.induction`)

`L ℓ b ∈ ℤ⟦q⟧` is Boylan–Webb's `L_ℓ(b)`: `L 0 = 1`, `L(2b+1) = U_ℓ(Φ·L(2b))`, `L(2b+2) = U_ℓ(L(2b+1))`,
with `Φ = q^δ(q^{ℓ²};q^{ℓ²})_∞/(q;q)_∞`. By `BoylanWebb.L_eq_partition`,
`L(b) = (q^{ℓ^{b mod 2}}; q^{ℓ^{b mod 2}})_∞ · Σ_m p(ℓ^b m − e_b) qᵐ` with `24 e_b = ℓ^{2⌈b/2⌉} − 1`.

For every `b ≥ 1`, with `κ₁₃ = 6`, `κ₁₇ = 6`, `κ₁₉ = 10`, `κ₂₃ = 5`:
* `L(b+2) ≡ κ L(b) (mod ℓ)` (`CertX.two_step`; for `b = 1` this is `hbase`, i.e. `b_ℓ(1) = 1`);
* `L(b) ≢ 0 (mod ℓ)` (`hnz`);
* `L(b) mod ℓ` lies on the line spanned by the reduction of the normalized cusp form
  `f_ℓ ∈ S_{ℓ−1}` (`Δ`, `ΔE₄`, `ΔE₆`, `ΔE₄E₆`) (`CertX.rank_one`);
* `p(ℓ^{b+2}m − e_{b+2}) ≡ κ p(ℓ^b m − e_b) (mod ℓ)` (`CertX.partition`), equivalently
  `p((ℓ^{b+2}n+1)/24) ≡ κ p((ℓ^b n+1)/24) (mod ℓ)` whenever `24 ∣ ℓ^b n + 1` (`partition_count_ℓ`).

Everything is unconditional and kernel-checked: Hecke `T_ℓ` on integral cusp forms, Sturm's bound mod
`ℓ` in level one, the Swinnerton-Dyer Hasse lift `A ≡ 1`, Frobenius `Φ ≡ Δ^δ`, Euler's pentagonal
theorem, and `decide +kernel` on literal truncated q-series.
-/

set_option autoImplicit false

namespace BoylanWebb
open PowerSeries

theorem hbase_13 : AtkinOBrien.Dvd (13 : ℤ) 1 (L 13 3 - (6 : ℤ) • L 13 1) := Cert13.two_step 1 le_rfl
theorem hbase_17 : AtkinOBrien.Dvd (17 : ℤ) 1 (L 17 3 - (6 : ℤ) • L 17 1) := Cert17.two_step 1 le_rfl
theorem hbase_19 : AtkinOBrien.Dvd (19 : ℤ) 1 (L 19 3 - (10 : ℤ) • L 19 1) := Cert19.two_step 1 le_rfl
theorem hbase_23 : AtkinOBrien.Dvd (23 : ℤ) 1 (L 23 3 - (5 : ℤ) • L 23 1) := Cert23.two_step 1 le_rfl

theorem hnz_13 (b : ℕ) (hb : 1 ≤ b) : ¬ ∃ y : PowerSeries ℤ, L 13 b = (13 : ℤ) • y :=
  fun ⟨y, hy⟩ => Cert13.not_dvd b hb ⟨y, by rw [pow_one]; exact hy⟩
theorem hnz_17 (b : ℕ) (hb : 1 ≤ b) : ¬ ∃ y : PowerSeries ℤ, L 17 b = (17 : ℤ) • y :=
  fun ⟨y, hy⟩ => Cert17.not_dvd b hb ⟨y, by rw [pow_one]; exact hy⟩
theorem hnz_19 (b : ℕ) (hb : 1 ≤ b) : ¬ ∃ y : PowerSeries ℤ, L 19 b = (19 : ℤ) • y :=
  fun ⟨y, hy⟩ => Cert19.not_dvd b hb ⟨y, by rw [pow_one]; exact hy⟩
theorem hnz_23 (b : ℕ) (hb : 1 ≤ b) : ¬ ∃ y : PowerSeries ℤ, L 23 b = (23 : ℤ) • y :=
  fun ⟨y, hy⟩ => Cert23.not_dvd b hb ⟨y, by rw [pow_one]; exact hy⟩

/-- **Mod-`ℓ` stability from `b = 1` on, all four primes at once.** -/
theorem two_step_mod_ell :
    (∀ b, 1 ≤ b → AtkinOBrien.Dvd (13 : ℤ) 1 (L 13 (b + 2) - (6 : ℤ) • L 13 b)) ∧
    (∀ b, 1 ≤ b → AtkinOBrien.Dvd (17 : ℤ) 1 (L 17 (b + 2) - (6 : ℤ) • L 17 b)) ∧
    (∀ b, 1 ≤ b → AtkinOBrien.Dvd (19 : ℤ) 1 (L 19 (b + 2) - (10 : ℤ) • L 19 b)) ∧
    (∀ b, 1 ≤ b → AtkinOBrien.Dvd (23 : ℤ) 1 (L 23 (b + 2) - (5 : ℤ) • L 23 b)) :=
  ⟨Cert13.two_step, Cert17.two_step, Cert19.two_step, Cert23.two_step⟩

/-- **`b_13(1) = 1`, partition form**: `p((13^(b+2) n + 1)/24) ≡ 6·p((13^b n + 1)/24) (mod 13)`
for every `b ≥ 1` and every `n` with `24 ∣ 13^b n + 1`. -/
theorem partition_count_13 (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ 13 ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((13 ^ (b + 2) * n + 1) / 24)) : ZMod 13) =
      6 * (Fintype.card (Nat.Partition ((13 ^ b * n + 1) / 24)) : ZMod 13) :=
  count_of 13 Cert13.h24 6 Cert13.partition b hb n hn

/-- **`b_17(1) = 1`, partition form**: `p((17^(b+2) n + 1)/24) ≡ 6·p((17^b n + 1)/24) (mod 17)`
for every `b ≥ 1` and every `n` with `24 ∣ 17^b n + 1`. -/
theorem partition_count_17 (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ 17 ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((17 ^ (b + 2) * n + 1) / 24)) : ZMod 17) =
      6 * (Fintype.card (Nat.Partition ((17 ^ b * n + 1) / 24)) : ZMod 17) :=
  count_of 17 Cert17.h24 6 Cert17.partition b hb n hn

/-- **`b_19(1) = 1`, partition form**: `p((19^(b+2) n + 1)/24) ≡ 10·p((19^b n + 1)/24) (mod 19)`
for every `b ≥ 1` and every `n` with `24 ∣ 19^b n + 1`. -/
theorem partition_count_19 (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ 19 ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((19 ^ (b + 2) * n + 1) / 24)) : ZMod 19) =
      10 * (Fintype.card (Nat.Partition ((19 ^ b * n + 1) / 24)) : ZMod 19) :=
  count_of 19 Cert19.h24 10 Cert19.partition b hb n hn

/-- **`b_23(1) = 1`, partition form**: `p((23^(b+2) n + 1)/24) ≡ 5·p((23^b n + 1)/24) (mod 23)`
for every `b ≥ 1` and every `n` with `24 ∣ 23^b n + 1`. -/
theorem partition_count_23 (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ 23 ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((23 ^ (b + 2) * n + 1) / 24)) : ZMod 23) =
      5 * (Fintype.card (Nat.Partition ((23 ^ b * n + 1) / 24)) : ZMod 23) :=
  count_of 23 Cert23.h24 5 Cert23.partition b hb n hn

/-- **`L(b)` is cuspidal**: `L(b) ∈ qℤ⟦q⟧` for `b ≥ 1` (any prime `ℓ ≥ 5`). -/
theorem L_cuspidal (ℓ : ℕ) [Fact ℓ.Prime] (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (hℓ : 5 ≤ ℓ) (b : ℕ) (hb : 1 ≤ b) :
    coeff 0 (L ℓ b) = 0 := by
  have hP : ∀ b, 1 ≤ b → constantCoeff (Pser ℓ b) = 0 := by
    intro b hb
    rw [Pser, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, Nat.cast_zero, mul_zero, zero_sub]
    apply pZ_neg
    have h := ek_mul ℓ h24 ((b + 1) / 2)
    have hk : 1 ≤ 2 * ((b + 1) / 2) := by omega
    have h1 : (ℓ : ℤ) ^ 2 ≤ (ℓ : ℤ) ^ (2 * ((b + 1) / 2)) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ℓ by omega)) (by omega)
    have h2 : (25 : ℤ) ≤ (ℓ : ℤ) ^ 2 := by
      have : (5 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
      nlinarith
    rw [eB]
    linarith
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' b
  · rw [(L_eq_partition ℓ h24 k).1, coeff_zero_eq_constantCoeff_apply, map_mul, hP _ hb, mul_zero]
  · rw [(L_eq_partition ℓ h24 k).2, coeff_zero_eq_constantCoeff_apply, map_mul, hP _ hb, mul_zero]

end BoylanWebb
