/-
# Ramanujan's conjecture for powers of 5 (Watson 1938)

`p(m) ≡ 0 (mod 5ᵏ)` whenever `24m ≡ 1 (mod 5ᵏ)`.

Proof (Hirschhorn–Hunt): the generating functions `L_k = Σ_n p(5ᵏn + δ_k) qⁿ⁺¹` alternate between
`(1/E)·b(τ)` and `(1/E(q⁵))·a(τ)` (`trans_even`, `trans_odd`), with coefficient polynomials obtained through the
`m_{k,j}`, and `ν₅(m_{k,j}) ≥ ⌊(5j−k−1)/2⌋` (`mc_dvd`) propagates `ν₅(coeff_i) ≥ k + ⌊(5i−5)/2⌋`.
-/
import RamanujanTau.Pow5Stage

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey

/-- the stage polynomials: `L_k = (1/E or 1/E(q⁵))·stagePoly k (τ)`. -/
noncomputable def stagePoly : ℕ → Polynomial ℤ
  | 0 => 1
  | k + 1 => if k % 2 = 0 then Aform (stagePoly k) else Bform (stagePoly k)

/-- the partition stages: `Par (k+1) = U₅(q^{[k even]}·Par k)`. -/
noncomputable def Par : ℕ → PowerSeries ℤ
  | 0 => partitionGF
  | k + 1 => if k % 2 = 0 then dis5 0 (X * Par k) else dis5 0 (Par k)

theorem Par_eq (k : ℕ) :
    Par k = (if k % 2 = 0 then partitionGF else Ring.inverse eQ) * Polynomial.aeval taus (stagePoly k) := by
  induction k with
  | zero => simp [Par, stagePoly]
  | succ k ih =>
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have h1 : (k + 1) % 2 ≠ 0 := by omega
      simp only [Par, stagePoly, hk, h1, if_true, if_false] at ih ⊢
      rw [ih, ← mul_assoc, trans_even]
    · have h1 : (k + 1) % 2 = 0 := by omega
      have h2 : k % 2 ≠ 0 := by omega
      simp only [Par, stagePoly, h1, h2, if_true, if_false] at ih ⊢
      rw [ih, trans_odd]

lemma stagePoly_coeff_zero {k : ℕ} (hk : 1 ≤ k) : (stagePoly k).coeff 0 = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [stagePoly]
    split_ifs with h
    · rw [coeff_Aform]; split_ifs <;> simp
    · rw [coeff_Bform, if_pos (by omega)]
      simp only [Nat.mul_zero, zero_add, sum_range_one]
      rw [ih (by omega), zero_mul]

/-- **the 5-adic invariant**: `5^d ∣ coeff_i (stagePoly k)` whenever `2d + 5 ≤ 2k + 5i`. -/
theorem stagePoly_dvd (k i d : ℕ) (h : 2 * d + 5 ≤ 2 * k + 5 * i) : (5 : ℤ) ^ d ∣ (stagePoly k).coeff i := by
  induction k generalizing i d with
  | zero =>
    simp only [stagePoly, Polynomial.coeff_one]
    rw [if_neg (by omega)]; exact dvd_zero _
  | succ k ih =>
    rw [stagePoly]
    split_ifs with hk
    · rw [coeff_Aform]
      split_ifs; swap; · exact dvd_zero _
      refine dvd_sum fun s hs => ?_
      simp only [mem_range] at hs
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp only [stagePoly, Polynomial.coeff_one, if_true, one_mul, Nat.mul_zero, zero_add]
          rw [add_zero, mc_small 1 i (by norm_num)]
          rcases (by omega : i = 1 ∨ 2 ≤ i) with rfl | hi
          · simp only [show (1 : ℕ) ≠ 0 by omega, if_false, if_true]
            exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 1)).trans (by norm_num)
          · simp only [show (1 : ℕ) ≠ 0 by omega, if_false, if_true, show i ≠ 1 by omega]
            exact dvd_zero _
        · rw [stagePoly_coeff_zero hk0, zero_mul]; exact dvd_zero _
      · refine dvd_mul_helper (e := min d ((2 * k + 5 * s - 5) / 2)) (ih s _ (by omega)) fun he => ?_
        rcases Nat.eq_zero_or_pos (d - min d ((2 * k + 5 * s - 5) / 2)) with h0 | h0
        · rw [h0, pow_zero]; exact one_dvd _
        · have hlt : (2 * k + 5 * s - 5) / 2 < d := by
            by_contra hc; rw [min_eq_left (by omega)] at h0; omega
          rw [min_eq_right hlt.le]
          refine mc_dvd _ _ _ ?_
          obtain ⟨F, hF⟩ : ∃ F, F = (2 * k + 5 * s - 5) / 2 := ⟨_, rfl⟩
          have h1 : 2 * F + 5 ≤ 2 * k + 5 * s := by omega
          have h2 : 2 * k + 5 * s ≤ 2 * F + 6 := by omega
          rw [← hF] at hlt ⊢
          obtain ⟨G, hG⟩ : ∃ G, G = d - F := ⟨_, rfl⟩
          have h3 : d = G + F := by omega
          rw [← hG]
          subst h3
          rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | hs2
          · have hFk : F = k := by omega
            subst hFk; omega
          · omega
    · rw [coeff_Bform]
      split_ifs; swap; · exact dvd_zero _
      refine dvd_sum fun l hl => ?_
      simp only [mem_range] at hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · rw [stagePoly_coeff_zero (by omega), zero_mul]; exact dvd_zero _
      · refine dvd_mul_helper (e := min d ((2 * k + 5 * l - 5) / 2)) (ih l _ (by omega)) fun he => ?_
        rcases Nat.eq_zero_or_pos (d - min d ((2 * k + 5 * l - 5) / 2)) with h0 | h0
        · rw [h0, pow_zero]; exact one_dvd _
        · have hlt : (2 * k + 5 * l - 5) / 2 < d := by
            by_contra hc; rw [min_eq_left (by omega)] at h0; omega
          rw [min_eq_right hlt.le]
          refine mc_dvd _ _ _ ?_
          obtain ⟨F, hF⟩ : ∃ F, F = (2 * k + 5 * l - 5) / 2 := ⟨_, rfl⟩
          have h1 : 2 * F + 5 ≤ 2 * k + 5 * l := by omega
          have h2 : 2 * k + 5 * l ≤ 2 * F + 6 := by omega
          rw [← hF] at hlt ⊢
          obtain ⟨G, hG⟩ : ∃ G, G = d - F := ⟨_, rfl⟩
          have h3 : d = G + F := by omega
          rw [← hG]
          subst h3
          omega

lemma stagePoly_pow_dvd {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : (5 : ℤ) ^ k ∣ (stagePoly k).coeff i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [stagePoly_coeff_zero hk]; exact dvd_zero _
  · exact stagePoly_dvd k i k (by omega)

/-- every coefficient of `L_k` is divisible by `5ᵏ`. -/
theorem Par_dvd (k n : ℕ) : (5 : ℤ) ^ k ∣ coeff n (Par k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr (stagePoly_pow_dvd hk)
  rw [Par_eq, hQ, map_mul (Polynomial.aeval taus), Polynomial.aeval_C,
    show algebraMap ℤ (PowerSeries ℤ) ((5 : ℤ) ^ k) = C ((5 : ℤ) ^ k) by simp, mul_left_comm, coeff_C_mul]
  exact dvd_mul_right _ _

/-- `δ_k`: `δ₁ = 4`, `δ_{k+1} = δ_k + (4 if k odd else 3)·5ᵏ`. -/
def delta : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | k + 2 => delta (k + 1) + (if (k + 1) % 2 = 1 then 4 else 3) * 5 ^ (k + 1)

lemma coeff_dis5_zero (n : ℕ) (F : PowerSeries ℤ) : coeff n (dis5 0 F) = coeff (5 * n) F := by
  rw [dis5, coeff_mk, add_zero]

/-- the coefficients of `L_k` are partition numbers. -/
theorem Par_coeff {k : ℕ} (hk : 1 ≤ k) :
    coeff 0 (Par k) = 0 ∧ ∀ n, coeff (n + 1) (Par k) = (Fintype.card (Nat.Partition (5 ^ k * n + delta k)) : ℤ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨?_, fun n => ?_⟩
      · simp [Par, coeff_dis5_zero]
      · simp only [Par, if_true, show (0 : ℕ) % 2 = 0 by rfl, coeff_dis5_zero]
        rw [show 5 * (n + 1) = (5 * n + 4) + 1 by ring, coeff_succ_X_mul, coeff_partitionGF_eq_card]
        simp [delta]
    · obtain ⟨h0, hn⟩ := ih hk0
      rcases Nat.mod_two_eq_zero_or_one k with hpar | hpar
      · -- `k` even: `L_{k+1} = U₅(q·L_k)`
        have hd : delta (k + 1) = delta k + 3 * 5 ^ k := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [delta, if_neg (by omega)]
        refine ⟨?_, fun n => ?_⟩
        · simp [Par, hpar, coeff_dis5_zero]
        · simp only [Par, hpar, if_true, coeff_dis5_zero]
          rw [show 5 * (n + 1) = (5 * n + 4) + 1 by ring, coeff_succ_X_mul, hn, hd,
            show 5 ^ k * (5 * n + 3) + delta k = 5 ^ (k + 1) * n + (delta k + 3 * 5 ^ k) by rw [pow_succ]; ring]
      · -- `k` odd: `L_{k+1} = U₅(L_k)`
        have hd : delta (k + 1) = delta k + 4 * 5 ^ k := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [delta, if_pos (by omega)]
        refine ⟨?_, fun n => ?_⟩
        · simp only [Par, show k % 2 ≠ 0 by omega, if_false, coeff_dis5_zero, Nat.mul_zero, h0]
        · simp only [Par, show k % 2 ≠ 0 by omega, if_false, coeff_dis5_zero]
          rw [show 5 * (n + 1) = (5 * n + 4) + 1 by ring, hn, hd,
            show 5 ^ k * (5 * n + 4) + delta k = 5 ^ (k + 1) * n + (delta k + 4 * 5 ^ k) by rw [pow_succ]; ring]

/-- `24·δ_k = c·5ᵏ + 1` (`c = 19` for odd `k`, `23` for even `k ≥ 2`), and `δ_k < 5ᵏ`. -/
lemma delta_spec {k : ℕ} (hk : 1 ≤ k) :
    24 * delta k = (if k % 2 = 1 then 19 else 23) * 5 ^ k + 1 ∧ delta k < 5 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [delta]
    · obtain ⟨h1, h2⟩ := ih hk0
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [delta]
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

/-- **Ramanujan's conjecture for powers of 5** (Watson 1938): if `24m ≡ 1 (mod 5ᵏ)` then `5ᵏ ∣ p(m)`. -/
theorem ramanujan_pow5 (k m : ℕ) (hm : 24 * m ≡ 1 [MOD 5 ^ k]) : 5 ^ k ∣ Fintype.card (Nat.Partition m) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨hδ, hlt⟩ := delta_spec hk
  have hd24 : 24 * delta k ≡ 1 [MOD 5 ^ k] := by
    rw [hδ]
    split_ifs <;> simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hcop : Nat.gcd (5 ^ k) 24 = 1 := Nat.Coprime.pow_left _ (by decide)
  have hcong : m ≡ delta k [MOD 5 ^ k] := Nat.ModEq.cancel_left_of_coprime hcop (hm.trans hd24.symm)
  have hge : delta k ≤ m := by
    by_contra h
    have := Nat.ModEq.eq_of_lt_of_lt hcong (by omega) hlt
    omega
  obtain ⟨n, hn⟩ : ∃ n, m = 5 ^ k * n + delta k := by
    have := (Nat.modEq_iff_dvd' hge).mp hcong.symm
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by omega⟩
  have h := Par_dvd k (n + 1)
  rw [(Par_coeff hk).2 n, ← hn] at h
  exact_mod_cast h

end MockTheta5.JTP
