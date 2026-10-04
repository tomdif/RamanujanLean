/-
# Watson's congruences for powers of 7: the polynomials `Pm7` and the 7-adic bound on their coefficients
-/
import Mathlib

set_option autoImplicit false

namespace MockTheta5.JTP
open Finset

/-- the polynomials with `U₇(yᵏ) = Pm7 k (τ)`. -/
noncomputable def Pm7 : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => 7 * Polynomial.X ^ 1 + 49 * Polynomial.X ^ 2
  | 2 => 10 * Polynomial.X ^ 1 + 441 * Polynomial.X ^ 2 + 4802 * Polynomial.X ^ 3 + 16807 * Polynomial.X ^ 4
  | 3 => 3 * Polynomial.X ^ 1 + 798 * Polynomial.X ^ 2 + 29155 * Polynomial.X ^ 3 + 403368 * Polynomial.X ^ 4 + 2470629 * Polynomial.X ^ 5 + 5764801 * Polynomial.X ^ 6
  | 4 => 574 * Polynomial.X ^ 2 + 60368 * Polynomial.X ^ 3 + 2028845 * Polynomial.X ^ 4 + 32000528 * Polynomial.X ^ 5 + 265180846 * Polynomial.X ^ 6 + 1129900996 * Polynomial.X ^ 7 + 1977326743 * Polynomial.X ^ 8
  | 5 => 190 * Polynomial.X ^ 2 + 61985 * Polynomial.X ^ 3 + 4549895 * Polynomial.X ^ 4 + 145061217 * Polynomial.X ^ 5 + 2491217575 * Polynomial.X ^ 6 + 25019236340 * Polynomial.X ^ 7 + 148299505725 * Polynomial.X ^ 8 + 484445052035 * Polynomial.X ^ 9 + 678223072849 * Polynomial.X ^ 10
  | 6 => 27 * Polynomial.X ^ 2 + 36064 * Polynomial.X ^ 3 + 5756226 * Polynomial.X ^ 4 + 343266168 * Polynomial.X ^ 5 + 10561938975 * Polynomial.X ^ 6 + 192486705390 * Polynomial.X ^ 7 + 2211781199670 * Polynomial.X ^ 8 + 16305036322778 * Polynomial.X ^ 9 + 75282761086239 * Polynomial.X ^ 10 + 199397583417606 * Polynomial.X ^ 11 + 232630513987207 * Polynomial.X ^ 12
  | k + 7 => Polynomial.X * (49 * Pm7 (k + 6) + 35 * Pm7 (k + 5) + 7 * Pm7 (k + 4))
      + Polynomial.X ^ 2 * (343 * Pm7 (k + 6) + 343 * Pm7 (k + 5) + 147 * Pm7 (k + 4) + 49 * Pm7 (k + 3)
        + 21 * Pm7 (k + 2) + 7 * Pm7 (k + 1) + Pm7 k)



/-- `m_{k,j}`. -/
noncomputable def mc7 (k j : ℕ) : ℤ := (Pm7 k).coeff j

lemma mc7_rec (k j : ℕ) : mc7 (k + 7) (j + 2) = 49 * mc7 (k + 6) (j + 1) + 35 * mc7 (k + 5) (j + 1)
    + 7 * mc7 (k + 4) (j + 1) + 343 * mc7 (k + 6) j + 343 * mc7 (k + 5) j + 147 * mc7 (k + 4) j
    + 49 * mc7 (k + 3) j + 21 * mc7 (k + 2) j + 7 * mc7 (k + 1) j + mc7 k j := by
  simp only [mc7, Pm7, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul,
    Polynomial.coeff_ofNat_mul]
  ring

lemma mc7_rec1 (k : ℕ) : mc7 (k + 7) 1 = 49 * mc7 (k + 6) 0 + 35 * mc7 (k + 5) 0 + 7 * mc7 (k + 4) 0 := by
  simp only [mc7, Pm7, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_ofNat_mul]
  rw [Polynomial.coeff_X_pow_mul']; simp

lemma mc7_rec0 (k : ℕ) : mc7 (k + 7) 0 = 0 := by
  simp [mc7, Pm7]

lemma dvd_mul_helper7 {c x : ℤ} {e d : ℕ} (hc : (7 : ℤ) ^ e ∣ c) (hx : e ≤ d → (7 : ℤ) ^ (d - e) ∣ x) :
    (7 : ℤ) ^ d ∣ c * x := by
  rcases Nat.lt_or_ge d e with h | h
  · exact (pow_dvd_pow 7 h.le).trans (hc.mul_right x)
  · rw [show d = e + (d - e) by omega, pow_add]; exact mul_dvd_mul hc (hx h)

set_option maxHeartbeats 4000000 in
lemma mc7_base_high (k j : ℕ) (hk : k ≤ 6) (h : 2 * k < j) : mc7 k j = 0 := by
  interval_cases k <;> simp [mc7, Pm7, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> omega

set_option maxHeartbeats 4000000 in
lemma mc7_base_low (k j : ℕ) (hk : k ≤ 6) (h : 7 * j < 2 * k) : mc7 k j = 0 := by
  have : j < 2 := by omega
  interval_cases k <;> interval_cases j <;> first | omega | simp [mc7, Pm7, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

set_option maxHeartbeats 0 in
lemma mc7_base_dvd (k j d : ℕ) (hk : k ≤ 6) (h : 4 * d + 2 * k + 1 ≤ 7 * j) : (7 : ℤ) ^ d ∣ mc7 k j := by
  rcases Nat.lt_or_ge (2 * k) j with hj | hj
  · rw [mc7_base_high k j hk hj]; exact dvd_zero _
  have hd : d ≤ 21 := by omega
  interval_cases k <;> interval_cases j <;> interval_cases d <;> first
    | omega
    | (simp [mc7, Pm7, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> norm_num)

lemma mc7_high (k j : ℕ) (h : 2 * k < j) : mc7 k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases Nat.lt_or_ge k 7 with hk | hk
    · exact mc7_base_high k j (by omega) h
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 7 := ⟨k - 7, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      rw [mc7_rec]
      simp only [ih (k + 6) (by omega) (j + 1) (by omega), ih (k + 5) (by omega) (j + 1) (by omega),
        ih (k + 4) (by omega) (j + 1) (by omega), ih (k + 6) (by omega) j (by omega), ih (k + 5) (by omega) j (by omega),
        ih (k + 4) (by omega) j (by omega), ih (k + 3) (by omega) j (by omega), ih (k + 2) (by omega) j (by omega),
        ih (k + 1) (by omega) j (by omega), ih k (by omega) j (by omega)]
      ring

lemma mc7_low (k j : ℕ) (h : 7 * j < 2 * k) : mc7 k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases Nat.lt_or_ge k 7 with hk | hk
    · exact mc7_base_low k j (by omega) h
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 7 := ⟨k - 7, by omega⟩
      rcases j with _ | _ | j
      · exact mc7_rec0 k
      · rw [mc7_rec1, ih (k + 6) (by omega) 0 (by omega), ih (k + 5) (by omega) 0 (by omega),
          ih (k + 4) (by omega) 0 (by omega)]; ring
      · rw [mc7_rec]
        simp only [ih (k + 6) (by omega) (j + 1) (by omega), ih (k + 5) (by omega) (j + 1) (by omega),
          ih (k + 4) (by omega) (j + 1) (by omega), ih (k + 6) (by omega) j (by omega),
          ih (k + 5) (by omega) j (by omega), ih (k + 4) (by omega) j (by omega), ih (k + 3) (by omega) j (by omega),
          ih (k + 2) (by omega) j (by omega), ih (k + 1) (by omega) j (by omega), ih k (by omega) j (by omega)]
        ring

/-- **Garvan's 7-adic bound** `ν₇(m_{k,j}) ≥ ⌊(7j − 2k − 1)/4⌋`. -/
lemma mc7_dvd (k j d : ℕ) (h : 4 * d + 2 * k + 1 ≤ 7 * j) : (7 : ℤ) ^ d ∣ mc7 k j := by
  induction k using Nat.strong_induction_on generalizing j d with
  | _ k ih =>
    rcases Nat.lt_or_ge k 7 with hk | hk
    · exact mc7_base_dvd k j d (by omega) h
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 7 := ⟨k - 7, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      rw [mc7_rec]
      refine dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_) ?_)
        ?_) ?_) ?_) ?_
      · exact dvd_mul_helper7 (e := 2) (by norm_num) fun _ => ih (k + 6) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 1) (by norm_num) fun _ => ih (k + 5) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 1) (by norm_num) fun _ => ih (k + 4) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 3) (by norm_num) fun _ => ih (k + 6) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 3) (by norm_num) fun _ => ih (k + 5) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 2) (by norm_num) fun _ => ih (k + 4) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 2) (by norm_num) fun _ => ih (k + 3) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 1) (by norm_num) fun _ => ih (k + 2) (by omega) _ _ (by omega)
      · exact dvd_mul_helper7 (e := 1) (by norm_num) fun _ => ih (k + 1) (by omega) _ _ (by omega)
      · exact ih k (by omega) j d (by omega)

end MockTheta5.JTP
