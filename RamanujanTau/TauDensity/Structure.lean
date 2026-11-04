import RamanujanTau.LehmerSmall.FinalDeep

/-! # Structure of the zero set of `τ`

* `tau_prime_pow_eq_zero_iff`: `τ(pᵏ) = 0 ↔ τ(p) = 0 ∧ k odd` (Lehmer's lemma + the Hecke recurrence:
  if `τ(p) = 0` then `τ(p^{2j}) = (−p¹¹)ʲ`, `τ(p^{2j+1}) = 0`).
* `tau_eq_zero_iff`: for `n ≥ 1`, `τ(n) = 0 ↔ ∃ p prime, v_p(n) odd ∧ τ(p) = 0`.
* `tau_sq_ne_zero`: `τ(m²) ≠ 0` for every `m ≥ 1`.
* `prime_zero_candidate`: a prime zero `p` satisfies `p ≥ 21 492 863 999`,
  `p ≡ −1 (mod 10 746 432 000 = 2⁹·3⁵·5³·691)` and `p ≡ 3, 5, 6 (mod 7)`.
* `tau_ne_zero_of_mod691`: `τ(n) ≠ 0` whenever no prime `p ≡ −1 (mod 691)` divides `n` to an odd power.
* `card_tau_ne_zero_ge_sqrt`: `⌊√N⌋ ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset

/-- If `τ(p) = 0`, then `τ(p^{2j}) = (−p¹¹)ʲ` and `τ(p^{2j+1}) = 0`. -/
lemma tau_prime_pow_of_zero {p : ℕ} (hp : p.Prime) (h : τ p = 0) (j : ℕ) :
    τ (p ^ (2 * j)) = (-(p : ℤ) ^ 11) ^ j ∧ τ (p ^ (2 * j + 1)) = 0 := by
  induction j with
  | zero => simp [tau_one, h]
  | succ j ih =>
    have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
    have e2 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
    refine ⟨?_, ?_⟩
    · rw [e1, LehmerSmall.rec2 hp, h, ih.1]; ring
    · rw [e2, LehmerSmall.rec2 hp, h, ih.2]; ring

/-- **`τ(pᵏ) = 0` iff `τ(p) = 0` and `k` is odd.** -/
theorem tau_prime_pow_eq_zero_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    τ (p ^ k) = 0 ↔ τ p = 0 ∧ Odd k := by
  constructor
  · intro hk
    by_cases h : τ p = 0
    · refine ⟨h, ?_⟩
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ho
      · exfalso
        rw [show j + j = 2 * j by ring, (tau_prime_pow_of_zero hp h j).1] at hk
        exact pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))) hk
      · exact ho
    · exact absurd hk (LehmerSmall.tau_prime_pow_ne_zero hp h k)
  · rintro ⟨h, j, rfl⟩
    exact (tau_prime_pow_of_zero hp h j).2

/-- **The zero set of `τ`.** For `n ≥ 1`: `τ(n) = 0` iff some prime `p` with `τ(p) = 0` divides `n`
to an odd power. -/
theorem tau_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) :
    τ n = 0 ↔ ∃ p, p.Prime ∧ Odd (n.factorization p) ∧ τ p = 0 := by
  constructor
  · revert hn
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      intro _ h
      obtain ⟨h0, hodd⟩ := (tau_prime_pow_eq_zero_iff hp k).mp h
      exact ⟨p, hp, by simpa [hp.factorization_self] using hodd, h0⟩
    | zero => intro h; omega
    | one => intro _ h; rw [tau_one] at h; exact absurd h one_ne_zero
    | coprime a b ha hb hab IHa IHb =>
      intro _ h
      rw [tau_mul_coprime hab] at h
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      rcases mul_eq_zero.mp h with h' | h'
      · obtain ⟨p, hp, hodd, h0⟩ := IHa (by omega) h'
        have hpa : p ∣ a := by
          by_contra hc; rw [Nat.factorization_eq_zero_of_not_dvd hc] at hodd; simp at hodd
        have hpb : ¬ p ∣ b := fun hpb => hp.not_dvd_one (by
          have := Nat.dvd_gcd hpa hpb; rwa [Nat.Coprime.gcd_eq_one hab] at this)
        refine ⟨p, hp, ?_, h0⟩
        rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
        exact hodd
      · obtain ⟨p, hp, hodd, h0⟩ := IHb (by omega) h'
        have hpb : p ∣ b := by
          by_contra hc; rw [Nat.factorization_eq_zero_of_not_dvd hc] at hodd; simp at hodd
        have hpa : ¬ p ∣ a := fun hpa => hp.not_dvd_one (by
          have := Nat.dvd_gcd hpa hpb; rwa [Nat.Coprime.gcd_eq_one hab] at this)
        refine ⟨p, hp, ?_, h0⟩
        rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
        exact hodd
  · rintro ⟨p, hp, hodd, h0⟩
    have hn0 : n ≠ 0 := by omega
    have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
      (Nat.coprime_ordCompl hp hn0).pow_left _
    rw [← Nat.ordProj_mul_ordCompl_eq_self n p, tau_mul_coprime hcop,
      (tau_prime_pow_eq_zero_iff hp _).mpr ⟨h0, hodd⟩, zero_mul]

/-- **`τ(n) ≠ 0` as soon as every prime dividing `n` to an odd power has `τ(p) ≠ 0`.** -/
theorem tau_ne_zero_of_odd_primes {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ p, p.Prime → Odd (n.factorization p) → τ p ≠ 0) : τ n ≠ 0 := by
  intro h
  obtain ⟨p, hp, hodd, h0⟩ := (tau_eq_zero_iff hn).mp h
  exact H p hp hodd h0

/-- **`τ` never vanishes on perfect squares.** -/
theorem tau_sq_ne_zero {m : ℕ} (hm : 1 ≤ m) : τ (m ^ 2) ≠ 0 := by
  refine tau_ne_zero_of_odd_primes (Nat.one_le_pow _ _ hm) fun p _ hodd => ?_
  exfalso
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hodd
  exact Nat.not_even_iff_odd.mpr hodd (even_two_mul _)

/-- **Arithmetic constraints on a prime zero of `τ`** (Lehmer's congruences, all proved in
`LehmerSmall`): `p ≥ 21 492 863 999`, `p ≡ −1 (mod 2⁹·3⁵·5³·691)`, `p ≡ 3, 5, 6 (mod 7)`. -/
theorem prime_zero_candidate {p : ℕ} (hp : p.Prime) (h : τ p = 0) :
    21492863999 ≤ p ∧ p % 10746432000 = 10746431999 ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := by
  obtain ⟨c691, -, -, -, c7⟩ := LehmerSmall.prime_zero_conditions hp h
  obtain ⟨c512, c243, c125⟩ := LehmerSmall.prime_zero_deep hp h
  refine ⟨?_, ?_, c7⟩
  · rcases Nat.lt_or_ge p 21492863999 with hlt | hge
    · exact absurd h (LehmerSmall.lehmer_below_21492863999 p hp.one_lt.le hlt)
    · exact hge
  · have d1 : 691 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c691])
    have d2 : 512 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c512])
    have d3 : 243 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c243])
    have d4 : 125 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, c125])
    have e12 : 691 * 512 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
    have e123 : 691 * 512 * 243 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e12 d3
    have hM : 691 * 512 * 243 * 125 ∣ p + 1 :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e123 d4
    rw [show 691 * 512 * 243 * 125 = 10746432000 by norm_num] at hM
    obtain ⟨k, hk⟩ := hM
    clear c691 c512 c243 c125 d1 d2 d3 d4 e12 e123 c7 h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp at hk
      · exact hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hp' : p = 10746432000 * j + 10746431999 := by rw [mul_add, mul_one] at hk; omega
    rw [hp', Nat.mul_add_mod]

/-- **Structural non-vanishing.** `τ(n) ≠ 0` unless some prime `p` dividing `n` to an odd power is a
"Lehmer candidate": `p ≥ 21 492 863 999`, `p ≡ −1 (mod 10 746 432 000)`, `p ≡ 3, 5, 6 (mod 7)`. -/
theorem tau_ne_zero_of_no_candidate {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ p, p.Prime → Odd (n.factorization p) →
      ¬ (21492863999 ≤ p ∧ p % 10746432000 = 10746431999 ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6))) :
    τ n ≠ 0 :=
  tau_ne_zero_of_odd_primes hn fun p hp hodd h0 => H p hp hodd (prime_zero_candidate hp h0)

/-- **The mod-691 form.** `τ(n) ≠ 0` whenever no prime `p ≡ −1 (mod 691)` divides `n` to an odd power
(in particular whenever no prime factor of `n` is `≡ −1 (mod 691)`). -/
theorem tau_ne_zero_of_mod691 {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ p, p.Prime → Odd (n.factorization p) → p % 691 ≠ 690) : τ n ≠ 0 :=
  tau_ne_zero_of_odd_primes hn fun p hp hodd h0 =>
    H p hp hodd (LehmerSmall.prime_zero_conditions hp h0).1

/-- `τ(n) ≠ 0` whenever every prime factor of `n` is `≢ −1 (mod 691)`. -/
theorem tau_ne_zero_of_prime_factors_mod691 {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ p, p.Prime → p ∣ n → p % 691 ≠ 690) : τ n ≠ 0 :=
  tau_ne_zero_of_mod691 hn fun p hp hodd => H p hp <| by
    by_contra hc; rw [Nat.factorization_eq_zero_of_not_dvd hc] at hodd; simp at hodd

/-- `τ(s·m²) ≠ 0` whenever `1 ≤ s < 21 492 863 999` and `m ≥ 1`. -/
theorem tau_small_mul_sq_ne_zero {s m : ℕ} (hs1 : 1 ≤ s) (hs : s < 21492863999) (hm : 1 ≤ m) :
    τ (s * m ^ 2) ≠ 0 := by
  have hm2 : m ^ 2 ≠ 0 := by positivity
  refine tau_ne_zero_of_no_candidate (Nat.one_le_iff_ne_zero.mpr (by positivity)) fun p hp hodd hc => ?_
  rw [Nat.factorization_mul (by omega) hm2, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul] at hodd
  have hps : p ∣ s := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, zero_add] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (even_two_mul _)
  have := Nat.le_of_dvd (by omega) hps
  omega

/-- **Elementary counting bound.** `⌊√N⌋ ≤ #{n ∈ [1,N] : τ(n) ≠ 0}` for every `N`. -/
theorem card_tau_ne_zero_ge_sqrt (N : ℕ) :
    Nat.sqrt N ≤ ((Icc 1 N).filter (fun n => τ n ≠ 0)).card := by
  have : (Icc 1 (Nat.sqrt N)).card ≤ ((Icc 1 N).filter (fun n => τ n ≠ 0)).card := by
    refine card_le_card_of_injOn (fun m => m ^ 2) (fun m hm => ?_) ?_
    · obtain ⟨h1, h2⟩ := mem_Icc.mp (by simpa using hm)
      simp only [coe_filter, Set.mem_setOf_eq, mem_Icc]
      refine ⟨⟨Nat.one_le_pow _ _ h1, ?_⟩, tau_sq_ne_zero h1⟩
      rw [sq]; exact Nat.le_sqrt.mp h2
    · intro a _ b _ hab
      exact Nat.pow_left_injective (by norm_num) hab
  simpa using this

/-- Combined with Lehmer's range: `max(⌊√N⌋, min(N, 21 492 863 998)) ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge (N : ℕ) :
    max (Nat.sqrt N) (min N 21492863998) ≤ ((Icc 1 N).filter (fun n => τ n ≠ 0)).card := by
  refine max_le (card_tau_ne_zero_ge_sqrt N) ?_
  have hsub : Icc 1 (min N 21492863998) ⊆ (Icc 1 N).filter (fun n => τ n ≠ 0) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨h1, h2.trans (min_le_left _ _)⟩,
      LehmerSmall.lehmer_below_21492863999 n h1 (by have := min_le_right N 21492863998; omega)⟩
  simpa using card_le_card hsub

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.tau_prime_pow_eq_zero_iff
#print axioms RamanujanTau.TauDensity.tau_eq_zero_iff
#print axioms RamanujanTau.TauDensity.tau_sq_ne_zero
#print axioms RamanujanTau.TauDensity.prime_zero_candidate
#print axioms RamanujanTau.TauDensity.tau_ne_zero_of_no_candidate
#print axioms RamanujanTau.TauDensity.tau_ne_zero_of_mod691
#print axioms RamanujanTau.TauDensity.tau_ne_zero_of_prime_factors_mod691
#print axioms RamanujanTau.TauDensity.tau_small_mul_sq_ne_zero
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_sqrt
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge
