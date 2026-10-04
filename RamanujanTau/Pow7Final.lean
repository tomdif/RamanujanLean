/-
# Watson's congruences for powers of 7

`p(m) ≡ 0 (mod 7^⌊(k+2)/2⌋)` whenever `24m ≡ 1 (mod 7ᵏ)`, `k ≥ 1`.

Proof (Watson; Garvan 1984): the generating functions `L_k = Σ_n p(7ᵏn + δ_k) qⁿ⁺¹` alternate between
`(1/E)·b(τ)` and `(1/E(q⁷))·a(τ)` (`trans_even7`, `trans_odd7`), and Garvan's bound
`ν₇(m_{k,j}) ≥ ⌊(7j−2k−1)/4⌋` (`mc7_dvd`) propagates `ν₇(a_l) ≥ ⌈k/2⌉ + ⌊(7l−7)/4⌋`, `ν₇(b_s) ≥ k/2 + ⌊(7s−3)/4⌋`.
-/
import RamanujanTau.Pow7Stage

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey

noncomputable def stagePoly7 : ℕ → Polynomial ℤ
  | 0 => 1
  | k + 1 => if k % 2 = 0 then Aform7 (stagePoly7 k) else Bform7 (stagePoly7 k)

noncomputable def Par7 : ℕ → PowerSeries ℤ
  | 0 => partitionGF
  | k + 1 => if k % 2 = 0 then dis7 0 (X ^ 2 * Par7 k) else dis7 0 (Par7 k)

theorem Par7_eq (k : ℕ) :
    Par7 k = (if k % 2 = 0 then partitionGF else Ring.inverse eQ7) * Polynomial.aeval tau7 (stagePoly7 k) := by
  induction k with
  | zero => simp [Par7, stagePoly7]
  | succ k ih =>
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have h1 : (k + 1) % 2 ≠ 0 := by omega
      simp only [Par7, stagePoly7, hk, h1, if_true, if_false] at ih ⊢
      rw [ih, ← mul_assoc, trans_even7]
    · have h1 : (k + 1) % 2 = 0 := by omega
      have h2 : k % 2 ≠ 0 := by omega
      simp only [Par7, stagePoly7, h1, h2, if_true, if_false] at ih ⊢
      rw [ih, trans_odd7]

lemma stagePoly7_coeff_zero {k : ℕ} (hk : 1 ≤ k) : (stagePoly7 k).coeff 0 = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [stagePoly7]
    split_ifs with h
    · rw [coeff_Aform7]; split_ifs <;> simp
    · rw [coeff_Bform7, if_pos (by omega)]
      simp only [Nat.mul_zero, zero_add, sum_range_one]
      rw [ih (by omega), zero_mul]

/-- **the 7-adic invariant**. -/
theorem stagePoly7_dvd (k i d : ℕ) (h : 4 * d + 3 + 2 * (k % 2) ≤ 2 * k + 7 * i) :
    (7 : ℤ) ^ d ∣ (stagePoly7 k).coeff i := by
  induction k generalizing i d with
  | zero =>
    simp only [stagePoly7, Polynomial.coeff_one]
    rw [if_neg (by omega)]; exact dvd_zero _
  | succ k ih =>
    rw [stagePoly7]
    split_ifs with hk
    · rw [coeff_Aform7]
      split_ifs; swap; · exact dvd_zero _
      refine dvd_sum fun s hs => ?_
      simp only [mem_range] at hs
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp only [stagePoly7, Polynomial.coeff_one, if_true, one_mul, Nat.mul_zero, zero_add, add_zero]
          exact mc7_dvd 1 i d (by omega)
        · rw [stagePoly7_coeff_zero hk0, zero_mul]; exact dvd_zero _
      · refine dvd_mul_helper7 (e := min d ((2 * k + 7 * s - 3) / 4)) (ih s _ (by omega)) fun he => ?_
        rcases Nat.eq_zero_or_pos (d - min d ((2 * k + 7 * s - 3) / 4)) with h0 | h0
        · rw [h0, pow_zero]; exact one_dvd _
        · have hlt : (2 * k + 7 * s - 3) / 4 < d := by
            by_contra hc; rw [min_eq_left (by omega)] at h0; omega
          rw [min_eq_right hlt.le]
          refine mc7_dvd _ _ _ ?_
          obtain ⟨F, hF⟩ : ∃ F, F = (2 * k + 7 * s - 3) / 4 := ⟨_, rfl⟩
          have h1 : 4 * F + 3 ≤ 2 * k + 7 * s := by omega
          have h2 : 2 * k + 7 * s ≤ 4 * F + 6 := by omega
          rw [← hF] at hlt ⊢
          obtain ⟨G, hG⟩ : ∃ G, G = d - F := ⟨_, rfl⟩
          have h3 : d = G + F := by omega
          rw [← hG]
          subst h3
          omega
    · rw [coeff_Bform7]
      split_ifs; swap; · exact dvd_zero _
      refine dvd_sum fun l hl => ?_
      simp only [mem_range] at hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · rw [stagePoly7_coeff_zero (by omega), zero_mul]; exact dvd_zero _
      · refine dvd_mul_helper7 (e := min d ((2 * k + 7 * l - 5) / 4)) (ih l _ (by omega)) fun he => ?_
        rcases Nat.eq_zero_or_pos (d - min d ((2 * k + 7 * l - 5) / 4)) with h0 | h0
        · rw [h0, pow_zero]; exact one_dvd _
        · have hlt : (2 * k + 7 * l - 5) / 4 < d := by
            by_contra hc; rw [min_eq_left (by omega)] at h0; omega
          rw [min_eq_right hlt.le]
          refine mc7_dvd _ _ _ ?_
          obtain ⟨F, hF⟩ : ∃ F, F = (2 * k + 7 * l - 5) / 4 := ⟨_, rfl⟩
          have h1 : 4 * F + 5 ≤ 2 * k + 7 * l := by omega
          have h2 : 2 * k + 7 * l ≤ 4 * F + 8 := by omega
          rw [← hF] at hlt ⊢
          obtain ⟨G, hG⟩ : ∃ G, G = d - F := ⟨_, rfl⟩
          have h3 : d = G + F := by omega
          rw [← hG]
          subst h3
          rcases (by omega : l = 1 ∨ 2 ≤ l) with rfl | hl2
          · have hF2 : 4 * F = 2 * k + 2 := by omega
            omega
          · omega

lemma stagePoly7_pow_dvd {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : (7 : ℤ) ^ ((k + 2) / 2) ∣ (stagePoly7 k).coeff i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [stagePoly7_coeff_zero hk]; exact dvd_zero _
  · exact stagePoly7_dvd k i _ (by omega)

theorem Par7_dvd {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (7 : ℤ) ^ ((k + 2) / 2) ∣ coeff n (Par7 k) := by
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr (stagePoly7_pow_dvd hk)
  rw [Par7_eq, hQ, map_mul (Polynomial.aeval tau7), Polynomial.aeval_C,
    show algebraMap ℤ (PowerSeries ℤ) ((7 : ℤ) ^ ((k + 2) / 2)) = C ((7 : ℤ) ^ ((k + 2) / 2)) by simp,
    mul_left_comm, coeff_C_mul]
  exact dvd_mul_right _ _

def delta7 : ℕ → ℕ
  | 0 => 0
  | 1 => 5
  | k + 2 => delta7 (k + 1) + (if (k + 1) % 2 = 1 then 6 else 4) * 7 ^ (k + 1)

lemma coeff_dis7_zero (n : ℕ) (F : PowerSeries ℤ) : coeff n (dis7 0 F) = coeff (7 * n) F := by
  rw [dis7, coeff_mk, add_zero]

theorem Par7_coeff {k : ℕ} (hk : 1 ≤ k) :
    coeff 0 (Par7 k) = 0 ∧ ∀ n, coeff (n + 1) (Par7 k) = (Fintype.card (Nat.Partition (7 ^ k * n + delta7 k)) : ℤ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨?_, fun n => ?_⟩
      · simp [Par7, coeff_dis7_zero, coeff_X_pow_mul']
      · simp only [Par7, if_true, show (0 : ℕ) % 2 = 0 by rfl, coeff_dis7_zero]
        rw [show 7 * (n + 1) = (7 * n + 5) + 2 by ring, coeff_X_pow_mul', if_pos (by omega),
          show 7 * n + 5 + 2 - 2 = 7 * n + 5 by omega, coeff_partitionGF_eq_card]
        simp [delta7]
    · obtain ⟨h0, hn⟩ := ih hk0
      rcases Nat.mod_two_eq_zero_or_one k with hpar | hpar
      · have hd : delta7 (k + 1) = delta7 k + 4 * 7 ^ k := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [delta7, if_neg (by omega)]
        refine ⟨?_, fun n => ?_⟩
        · simp [Par7, hpar, coeff_dis7_zero, coeff_X_pow_mul']
        · simp only [Par7, hpar, if_true, coeff_dis7_zero]
          rw [show 7 * (n + 1) = (7 * n + 4 + 1) + 2 by ring, coeff_X_pow_mul', if_pos (by omega),
            show 7 * n + 4 + 1 + 2 - 2 = (7 * n + 4) + 1 by omega, hn, hd,
            show 7 ^ k * (7 * n + 4) + delta7 k = 7 ^ (k + 1) * n + (delta7 k + 4 * 7 ^ k) by rw [pow_succ]; ring]
      · have hd : delta7 (k + 1) = delta7 k + 6 * 7 ^ k := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [delta7, if_pos (by omega)]
        refine ⟨?_, fun n => ?_⟩
        · simp only [Par7, show k % 2 ≠ 0 by omega, if_false, coeff_dis7_zero, Nat.mul_zero, h0]
        · simp only [Par7, show k % 2 ≠ 0 by omega, if_false, coeff_dis7_zero]
          rw [show 7 * (n + 1) = (7 * n + 6) + 1 by ring, hn, hd,
            show 7 ^ k * (7 * n + 6) + delta7 k = 7 ^ (k + 1) * n + (delta7 k + 6 * 7 ^ k) by rw [pow_succ]; ring]

lemma delta7_spec {k : ℕ} (hk : 1 ≤ k) :
    24 * delta7 k = (if k % 2 = 1 then 17 else 23) * 7 ^ k + 1 ∧ delta7 k < 7 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [delta7]
    · obtain ⟨h1, h2⟩ := ih hk0
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [delta7]
      rcases Nat.mod_two_eq_zero_or_one (j + 1) with hp | hp
      · rw [if_neg (by omega)] at *
        rw [if_pos (by omega)]
        constructor
        · rw [pow_succ]; omega
        · rw [pow_succ]; omega
      · rw [if_pos hp] at *
        rw [if_neg (by omega)]
        constructor
        · rw [pow_succ]; omega
        · rw [pow_succ]; omega

/-- **Watson's theorem for powers of 7**: if `24m ≡ 1 (mod 7ᵏ)`, `k ≥ 1`, then `7^⌊(k+2)/2⌋ ∣ p(m)`. -/
theorem ramanujan_pow7 {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (hm : 24 * m ≡ 1 [MOD 7 ^ k]) :
    7 ^ ((k + 2) / 2) ∣ Fintype.card (Nat.Partition m) := by
  obtain ⟨hδ, hlt⟩ := delta7_spec hk
  have hd24 : 24 * delta7 k ≡ 1 [MOD 7 ^ k] := by
    rw [hδ]
    split_ifs <;> simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hcop : Nat.gcd (7 ^ k) 24 = 1 := Nat.Coprime.pow_left _ (by decide)
  have hcong : m ≡ delta7 k [MOD 7 ^ k] := Nat.ModEq.cancel_left_of_coprime hcop (hm.trans hd24.symm)
  have hge : delta7 k ≤ m := by
    by_contra h
    have := Nat.ModEq.eq_of_lt_of_lt hcong (by omega) hlt
    omega
  obtain ⟨n, hn⟩ : ∃ n, m = 7 ^ k * n + delta7 k := by
    obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hge).mp hcong.symm
    exact ⟨n, by omega⟩
  have h := Par7_dvd hk (n + 1)
  rw [(Par7_coeff hk).2 n, ← hn] at h
  exact_mod_cast h

end MockTheta5.JTP
