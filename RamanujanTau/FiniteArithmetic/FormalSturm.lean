import RamanujanTau.ModP.Formal

/-! A finite q-expansion bound over arbitrary coefficient rings, including
prime-power rings. This uses the integral discriminant decomposition. -/
set_option autoImplicit false

namespace ModP
open PowerSeries

variable {R : Type*} [CommRing R]

lemma X_pow_dvd_of_disc_mul (h1728 : IsUnit (1728 : R)) {g : PowerSeries R} (n : ℕ)
    (h : X ^ (n + 1) ∣ 1728 * Dq R * g) : X ^ n ∣ g := by
  obtain ⟨W, hW⟩ := exists_inv_U
  obtain ⟨u, hu⟩ := h1728.exists_left_inv
  have hW' : PowerSeries.map (Int.castRingHom R) W * PowerSeries.map (Int.castRingHom R)
      (MockTheta5.JTP.qfacInf ^ 24) = 1 := by
    rw [← map_mul, mul_comm, hW, map_one]
  have h1 : (PowerSeries.C u : PowerSeries R) * 1728 = 1 := by
    rw [show (1728 : PowerSeries R) = PowerSeries.C 1728 from (map_ofNat _ _).symm,
      ← map_mul, hu, map_one]
  have he : PowerSeries.C u * PowerSeries.map (Int.castRingHom R) W * (1728 * Dq R * g) = X * g := by
    rw [Dq, map_mul, PowerSeries.map_X]
    linear_combination (X * g) * h1 * (PowerSeries.map (Int.castRingHom R) W *
      PowerSeries.map (Int.castRingHom R) (MockTheta5.JTP.qfacInf ^ 24)) + (X * g) * hW'
  have hd : X ^ (n + 1) ∣ X * g := he ▸ Dvd.dvd.mul_left h _
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, PowerSeries.X_mul_cancel ?_⟩
  simpa only [pow_succ', mul_assoc] using ht

/-- Weight `k` is determined by coefficients through `floor(k/12)` over any
commutative ring in which 1728 is invertible. -/
theorem iso_eq_zero_of_coeff_prefix (h1728 : IsUnit (1728 : R)) :
    ∀ (k : ℕ) (P : MvPolynomial (Fin 2) R), Iso P k →
      (∀ n ≤ k / 12, PowerSeries.coeff n (ev R P) = 0) → P = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hP hc
    obtain ⟨Q, hQ, hQ0, hPQ⟩ := exists_div hP
    have hs : MvPolynomial.eval one2 P = 0 := by
      rw [← constantCoeff_ev, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hc 0 (by omega)
    rw [hs, map_zero, zero_mul, zero_add] at hPQ
    by_cases hk : k < 12
    · rw [hPQ, hQ0 hk, mul_zero]
    · have hd : PowerSeries.X ^ (k / 12 + 1) ∣ ev R P :=
        PowerSeries.X_pow_dvd_iff.mpr fun n hn => hc n (by omega)
      have he : ev R P = 1728 * Dq R * ev R Q := by rw [hPQ, map_mul, ev_disc]
      rw [he] at hd
      have hq := X_pow_dvd_of_disc_mul h1728 (k / 12) hd
      have hqcoeff : ∀ n ≤ (k - 12) / 12, PowerSeries.coeff n (ev R Q) = 0 := by
        intro n hn
        exact PowerSeries.X_pow_dvd_iff.mp hq n (by omega)
      rw [hPQ, ih (k - 12) (by omega) Q hQ hqcoeff, mul_zero]

theorem ev_eq_of_coeff_prefix (h1728 : IsUnit (1728 : R)) {k : ℕ}
    {P Q : MvPolynomial (Fin 2) R} (hP : Iso P k) (hQ : Iso Q k)
    (hc : ∀ n ≤ k / 12, PowerSeries.coeff n (ev R P) = PowerSeries.coeff n (ev R Q)) :
    ev R P = ev R Q := by
  have h := iso_eq_zero_of_coeff_prefix h1728 k (P - Q) (iso_sub hP hQ) (by
    intro n hn
    rw [map_sub, map_sub, hc n hn, sub_self])
  exact congrArg (ev R) (sub_eq_zero.mp h)

end ModP
