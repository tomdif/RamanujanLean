import RamanujanTau.RamanujanODE.Main
import RamanujanTau.ModP.Formal

/-! # Series identities used by the prime-607 computation

These identities let a kernel program obtain `E₂` and `E₄` from the discriminant
alone, without computing any divisor sums:

* `theta_Dq`: `θΔ = E₂Δ`, from Ramanujan's differential equations.
* `E2_mul_W`: with `Δ = qW`, `E₂W = W + θW`.
* `E4_eq`: `E₄ = E₂² - 12 θE₂`.
* `sigma_pred_eq`: for `0 < n < p²` and `m` the prime-to-`p` part of `n`,
  `σ_(p-2)(n) ≡ σ₁(n) m^(p-2) (mod p)`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank607Identities

open PowerSeries Igusa ModP

section Discriminant

lemma E4_cube_sub_E6_sq :
    ModP.E4 ℤ ^ 3 - ModP.E6 ℤ ^ 2 = 1728 * ModP.Dq ℤ := by
  have h := ModP.ev_disc (R := ℤ)
  simpa only [map_sub, map_pow, ModP.ev_X0, ModP.ev_X1] using h

lemma theta_pow_two {R : Type*} [CommRing R] (f : PowerSeries R) :
    theta (f ^ 2) = 2 * f * theta f := by
  rw [pow_two, theta_mul]; ring

lemma theta_pow_three {R : Type*} [CommRing R] (f : PowerSeries R) :
    theta (f ^ 3) = 3 * f ^ 2 * theta f := by
  rw [pow_succ, theta_mul, theta_pow_two]; ring

lemma theta_sub {R : Type*} [CommRing R] (f g : PowerSeries R) :
    theta (f - g) = theta f - theta g := by
  ext n; simp [coeff_theta, mul_sub]

/-- `θΔ = E₂Δ` over `ℤ`. -/
theorem theta_Dq_int : theta (ModP.Dq ℤ) = E2 ℤ * ModP.Dq ℤ := by
  obtain ⟨h4, h6, -⟩ := RamanujanODEProof.ramanujanODE
  have hd := E4_cube_sub_E6_sq
  have hth : (1728 : PowerSeries ℤ) * theta (ModP.Dq ℤ) = 1728 * (E2 ℤ * ModP.Dq ℤ) := by
    have h1 : (1728 : PowerSeries ℤ) * theta (ModP.Dq ℤ) = theta (1728 * ModP.Dq ℤ) := by
      have := theta_natCast_mul (R := ℤ) 1728 (ModP.Dq ℤ)
      simpa using this.symm
    rw [h1, ← hd, theta_sub, theta_pow_three, theta_pow_two]
    linear_combination (ModP.E4 ℤ ^ 2) * h4 - (ModP.E6 ℤ) * h6 + E2 ℤ * hd
  have h0 : (1728 : PowerSeries ℤ) ≠ 0 := fun h => by
    have h1 := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at h1
    norm_num at h1
  exact mul_left_cancel₀ h0 hth

variable (R : Type*) [CommRing R]

lemma map_Dq : PowerSeries.map (Int.castRingHom R) (ModP.Dq ℤ) = ModP.Dq R := by
  simp [ModP.Dq]

lemma map_E2 : PowerSeries.map (Int.castRingHom R) (E2 ℤ) = E2 R := by
  simp [E2]

lemma map_E4 : PowerSeries.map (Int.castRingHom R) (ModP.E4 ℤ) = ModP.E4 R := by
  simp [ModP.E4]

/-- `θΔ = E₂Δ` over every commutative ring. -/
theorem theta_Dq : theta (ModP.Dq R) = E2 R * ModP.Dq R := by
  have h := congrArg (PowerSeries.map (Int.castRingHom R)) theta_Dq_int
  rwa [map_theta, map_mul, map_Dq, map_E2] at h

/-- `12 θE₂ = E₂² - E₄` over every commutative ring. -/
theorem twelve_theta_E2 : 12 * theta (E2 R) = E2 R ^ 2 - ModP.E4 R := by
  obtain ⟨-, -, h⟩ := RamanujanODEProof.ramanujanODE
  have h' := congrArg (PowerSeries.map (Int.castRingHom R)) h
  simpa only [map_mul, map_sub, map_pow, map_theta, map_E2, map_E4, map_ofNat] using h'

/-- `E₄ = E₂² - 12 θE₂`. -/
theorem E4_eq : ModP.E4 R = E2 R ^ 2 - 12 * theta (E2 R) := by
  rw [twelve_theta_E2]; ring

/-- `W = (q;q)²⁴`, so that `Δ = qW`. -/
noncomputable def W : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) (MockTheta5.JTP.qfacInf ^ 24)

lemma Dq_eq : ModP.Dq R = X * W R := by
  simp [ModP.Dq, W]

lemma theta_X : theta (X : PowerSeries R) = X := by
  ext n
  rw [coeff_theta, PowerSeries.coeff_X]
  split_ifs with h
  · simp [h]
  · simp

lemma X_mul_left_cancel {f g : PowerSeries R} (h : (X : PowerSeries R) * f = X * g) : f = g := by
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  simpa [PowerSeries.coeff_succ_X_mul] using this

/-- `E₂W = W + θW`. -/
theorem E2_mul_W : E2 R * W R = W R + theta (W R) := by
  apply X_mul_left_cancel R
  have h := theta_Dq R
  rw [Dq_eq, theta_mul, theta_X] at h
  linear_combination -h

/-- `E₂ = 1 + θW · W⁻¹`, for any inverse of `W`. -/
theorem E2_eq_of_inv {Wi : PowerSeries R} (h : W R * Wi = 1) :
    E2 R = theta (W R) * Wi + 1 := by
  have h1 := E2_mul_W R
  linear_combination (Wi) * h1 + (-E2 R + 1) * h

end Discriminant

section Sigma

open ArithmeticFunction

variable {p : ℕ} [hp : Fact p.Prime]

/-- Prime-to-`p` case: the divisor-pair involution and Fermat's little theorem. -/
theorem sigma_pred_coprime {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) :
    (sigma (p - 2) n : ZMod p) = (sigma 1 n : ZMod p) * (n : ZMod p) ^ (p - 2) := by
  have h2 : 2 ≤ p := hp.out.two_le
  rw [sigma_apply, sigma_apply]
  have hflip : (∑ d ∈ n.divisors, d ^ 1) = ∑ d ∈ n.divisors, (n / d) ^ 1 :=
    (Nat.sum_div_divisors n (fun d => d ^ 1)).symm
  rw [hflip]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hn
    · exact h
  have hquot : d * e / d = e := Nat.mul_div_cancel_left _ hd0
  rw [hquot, pow_one]
  have heu : (e : ZMod p) ≠ 0 := by
    intro h
    exact hpn (Dvd.dvd.mul_left ((ZMod.natCast_eq_zero_iff _ _).mp h) _)
  have hfermat : (e : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one heu
  have hmul : (e : ZMod p) * (e : ZMod p) ^ (p - 2) = 1 := by
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hfermat]
  push_cast
  rw [mul_pow]
  calc (d : ZMod p) ^ (p - 2)
      = (d : ZMod p) ^ (p - 2) * ((e : ZMod p) * (e : ZMod p) ^ (p - 2)) := by rw [hmul, mul_one]
    _ = _ := by ring

/-- `σ_k(p m) ≡ σ_k(m) (mod p)` when `p ∤ m` and `k > 0`. -/
theorem sigma_prime_mul {k m : ℕ} (hk : 0 < k) (hpm : ¬ p ∣ m) :
    (sigma k (p * m) : ZMod p) = (sigma k m : ZMod p) := by
  have hco : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm
  rw [(isMultiplicative_sigma (k := k)).map_mul_of_coprime hco]
  have hsp : (sigma k p : ZMod p) = 1 := by
    rw [sigma_apply, Nat.Prime.divisors hp.out, Finset.sum_pair hp.out.one_lt.ne]
    simp [hk.ne']
  push_cast
  rw [hsp, one_mul]

/-- The lane formula for the denominator. -/
theorem sigma_pred_eq (hp3 : 3 ≤ p) {n : ℕ} (hn : 0 < n) (hlt : n < p ^ 2) :
    (sigma (p - 2) n : ZMod p) =
      (sigma 1 n : ZMod p) * ((if n % p = 0 then n / p else n : ℕ) : ZMod p) ^ (p - 2) := by
  have h2 : 2 ≤ p := hp.out.two_le
  by_cases hd : n % p = 0
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hd
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmlt : m < p := by
      rw [pow_two] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    have hpm : ¬ p ∣ m := fun h => absurd (Nat.le_of_dvd hm0 h) (by omega)
    rw [if_pos hd, Nat.mul_div_cancel_left _ hp.out.pos, sigma_prime_mul (by omega) hpm,
      sigma_prime_mul one_pos hpm]
    exact sigma_pred_coprime hm0 hpm
  · rw [if_neg hd]
    exact sigma_pred_coprime hn (fun h => hd (Nat.mod_eq_zero_of_dvd h))

end Sigma

end RamanujanTau.FiniteArithmetic.Rank607Identities
