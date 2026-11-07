import RamanujanTau.HeckeQExp
import RamanujanTau.SmallValues
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-! # Lehmer's lemma: the least `n` with `τ(n) = 0` is prime

If `τ(p) ≠ 0` then `τ(pᵏ) ≠ 0` for every `k` (`tau_prime_pow_ne_zero`). Proof (Lehmer 1947): write
`X² − τ(p)X + p¹¹ = (X − x)(X − y)` over `ℂ`. The Hecke recurrence gives `(x − y)τ(pᵏ) = x^{k+1} − y^{k+1}`.
If `τ(pᵏ) = 0` with `x ≠ y`, `ζ = x/y` is a root of unity, so `ζ + ζ⁻¹ = τ(p)²/p¹¹ − 2` is a rational
algebraic integer of absolute value `≤ 2`, i.e. `τ(p)² = m·p¹¹` with `m ∈ {0,…,4}`. A `p`-adic valuation
count leaves only `τ(2)² = 2¹²` or `τ(3)² = 3¹²`, false (`τ(2) = −24`, `τ(3) = 252`); and `m = 0` is `τ(p) = 0`.
If `x = y`, `τ(pᵏ) = (k+1)xᵏ ≠ 0`.

With multiplicativity this gives: if `τ(n) = 0` then `τ(p) = 0` for some prime `p ∣ n`
(`exists_prime_dvd_tau_eq_zero`). In particular the least zero of `τ`, if any, is a prime.
-/

namespace RamanujanTau.LehmerSmall
open RamanujanTau

/-- `t² = m·p¹¹` with `1 ≤ m ≤ 4` forces `(p, m) = (2, 2)` or `(3, 3)`. -/
lemma sq_eq_mul_prime_pow11 {p : ℕ} (hp : p.Prime) {t : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h : t ^ 2 = (m : ℤ) * (p : ℤ) ^ 11) : (p = 2 ∧ m = 2) ∨ (p = 3 ∧ m = 3) := by
  haveI := Fact.mk hp
  have hN : t.natAbs ^ 2 = m * p ^ 11 := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  have ht0 : t.natAbs ≠ 0 := by
    intro h0; rw [h0] at hN
    have : 0 < m * p ^ 11 := Nat.mul_pos (by omega) (pow_pos hp.pos _)
    rw [← hN] at this; simp at this
  have hv := congrArg (padicValNat p) hN
  rw [padicValNat.pow 2 ht0, padicValNat.mul (by omega) (pow_ne_zero _ hp.ne_zero),
    padicValNat.prime_pow] at hv
  -- so `padicValNat p m` is odd
  have hodd : padicValNat p m % 2 = 1 := by omega
  have h2 := hp.two_le
  interval_cases m
  · simp at hodd
  · by_cases hp2 : p = 2
    · left; exact ⟨hp2, rfl⟩
    · rw [padicValNat.eq_zero_of_not_dvd (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))] at hodd
      simp at hodd
  · by_cases hp3 : p = 3
    · right; exact ⟨hp3, rfl⟩
    · rw [padicValNat.eq_zero_of_not_dvd (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))] at hodd
      simp at hodd
  · by_cases hp2 : p = 2
    · subst hp2
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow] at hodd; simp at hodd
    · have : ¬ p ∣ 4 := by
        intro hd
        have := (Nat.Prime.dvd_of_dvd_pow hp (show p ∣ 2 ^ 2 by simpa using hd))
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      rw [padicValNat.eq_zero_of_not_dvd this] at hodd; simp at hodd

/-- The Hecke recurrence in the form used below: `τ(p^{k+2}) = τ(p)τ(p^{k+1}) − p¹¹τ(pᵏ)`. -/
lemma rec2 {p : ℕ} (hp : p.Prime) (k : ℕ) :
    τ (p ^ (k + 2)) = τ p * τ (p ^ (k + 1)) - (p : ℤ) ^ 11 * τ (p ^ k) := by
  have := tau_hecke_recurrence hp (r := k + 1) (by omega)
  simpa using this

/-- **Lehmer's lemma.** If `τ(p) ≠ 0` for a prime `p`, then `τ(pᵏ) ≠ 0` for all `k`. -/
theorem tau_prime_pow_ne_zero {p : ℕ} (hp : p.Prime) (hτ : τ p ≠ 0) (k : ℕ) : τ (p ^ k) ≠ 0 := by
  set t : ℂ := (τ p : ℂ) with ht
  set P : ℂ := (p : ℂ) ^ 11 with hP
  have hP0 : P ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  let a : ℕ → ℂ := fun j => (τ (p ^ j) : ℂ)
  have a0 : a 0 = 1 := by simp [a, tau_one]
  have a1 : a 1 = t := by simp [a, t]
  have arec : ∀ j, a (j + 2) = t * a (j + 1) - P * a j := by
    intro j; simp only [a, t, P]; rw [rec2 hp j]; push_cast; ring
  -- roots of `X² − tX + P`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (t ^ 2 - 4 * P)
  set x : ℂ := (t + s) / 2
  set y : ℂ := (t - s) / 2
  have hsum : x + y = t := by simp only [x, y]; ring
  have hprod : x * y = P := by simp only [x, y]; linear_combination (1/4 : ℂ) * hs
  intro hk
  have hak : a k = 0 := by simp [a, hk]
  by_cases hxy : x = y
  · -- double root: `a j = (j+1) xʲ`
    have hform : ∀ j, a j = ((j : ℂ) + 1) * x ^ j := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        match j, ih with
        | 0, _ => simp [a0]
        | 1, _ => rw [a1, ← hsum, ← hxy]; push_cast; ring
        | j + 2, ih =>
          rw [arec, ih (j + 1) (by omega), ih j (by omega), ← hsum, ← hprod, ← hxy]; push_cast; ring
    have hx0 : x ≠ 0 := by
      intro h0; apply hP0; rw [← hprod, h0, zero_mul]
    rw [hform] at hak
    rcases mul_eq_zero.mp hak with h | h
    · have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      exact this h
    · exact hx0 (pow_eq_zero_iff (n := k) (by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp at h
        · omega) |>.mp h)
  · have hform : ∀ j, (x - y) * a j = x ^ (j + 1) - y ^ (j + 1) := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        match j, ih with
        | 0, _ => simp [a0]
        | 1, _ => rw [a1, ← hsum]; ring
        | j + 2, ih =>
          have e1 := ih (j + 1) (by omega)
          have e2 := ih j (by omega)
          rw [arec, ← hsum, ← hprod]
          linear_combination (x + y) * e1 - (x * y) * e2
    have hy0 : y ≠ 0 := by intro h0; apply hP0; rw [← hprod, h0, mul_zero]
    have hpow : x ^ (k + 1) = y ^ (k + 1) := by
      have := hform k; rw [hak, mul_zero] at this; exact (sub_eq_zero.mp this.symm)
    set ζ : ℂ := x / y
    have hζ : ζ ^ (k + 1) = 1 := by
      simp only [ζ]; rw [div_pow, hpow, div_self (pow_ne_zero _ hy0)]
    have hζ0 : ζ ≠ 0 := div_ne_zero (fun h0 => by apply hP0; rw [← hprod, h0, zero_mul]) hy0
    -- `c = ζ + ζ⁻¹` is rational
    set qr : ℚ := ((τ p : ℚ) ^ 2 - 2 * (p : ℚ) ^ 11) / (p : ℚ) ^ 11
    have hc : ζ + ζ⁻¹ = (qr : ℂ) := by
      have hx0 : x ≠ 0 := fun h0 => by apply hP0; rw [← hprod, h0, zero_mul]
      have hq : (qr : ℂ) = (t ^ 2 - 2 * P) / P := by simp only [qr, t, P]; push_cast; ring
      rw [hq, ← hsum, ← hprod]
      simp only [ζ]; rw [inv_div]; field_simp; ring
    -- integrality
    have hint : IsIntegral ℤ (ζ + ζ⁻¹) := by
      have hI : IsIntegral ℤ ζ :=
        ⟨Polynomial.X ^ (k + 1) - 1, Polynomial.monic_X_pow_sub_C 1 (Nat.succ_ne_zero k),
          by simp [hζ]⟩
      have hinv : ζ⁻¹ = ζ ^ k := by
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hζ)
      rw [hinv]; exact hI.add (hI.pow k)
    rw [hc] at hint
    have hintQ : IsIntegral ℤ qr :=
      (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective).mp hint
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
    -- `|z| ≤ 2`
    have hn1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (Nat.succ_ne_zero k)
    have hzb : |(z : ℝ)| ≤ 2 := by
      have : ‖ζ + ζ⁻¹‖ ≤ 2 := by
        calc ‖ζ + ζ⁻¹‖ ≤ ‖ζ‖ + ‖ζ⁻¹‖ := norm_add_le _ _
          _ = 2 := by rw [norm_inv, hn1]; norm_num
      rw [hc, ← hz] at this
      simpa [Complex.norm_intCast] using this
    have hzb' : -2 ≤ z ∧ z ≤ 2 := by
      have := abs_le.mp hzb
      constructor <;> [exact_mod_cast this.1; exact_mod_cast this.2]
    -- `τ(p)² = (z + 2) p¹¹`
    have hpq : ((p : ℚ) ^ 11) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hzq : (z : ℚ) = qr := by simpa using hz
    have heq : (τ p) ^ 2 = (z + 2) * (p : ℤ) ^ 11 := by
      have : ((τ p : ℚ)) ^ 2 = ((z : ℚ) + 2) * (p : ℚ) ^ 11 := by
        rw [hzq]; simp only [qr]; rw [div_add' _ _ _ hpq, div_mul_cancel₀ _ hpq]; ring
      exact_mod_cast this
    have hz2 : z + 2 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at heq; exact hτ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp heq)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = z + 2 := ⟨(z + 2).toNat, by omega⟩
    rw [← hm] at heq
    rcases sq_eq_mul_prime_pow11 hp (m := m) (by omega) (by omega) heq with ⟨h2, -⟩ | ⟨h3, -⟩
    · subst h2; rw [tau_two] at heq; norm_num at heq; omega
    · subst h3; rw [tau_three] at heq; norm_num at heq; omega

/-- **Least zero is prime.** If `τ(n) = 0` (`n ≥ 1`), then `τ(p) = 0` for some prime `p ∣ n`. -/
theorem exists_prime_dvd_tau_eq_zero {n : ℕ} (hn : 1 ≤ n) (h : τ n = 0) :
    ∃ p, p.Prime ∧ p ∣ n ∧ τ p = 0 := by
  by_contra hcon
  push Not at hcon
  revert hcon h hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ h H
    exact tau_prime_pow_ne_zero hp (H p hp (dvd_pow_self p (by omega))) k h
  | zero => intro h; omega
  | one => intro _ h _; rw [tau_one] at h; exact one_ne_zero h
  | coprime a b ha hb hab IHa IHb =>
    intro _ h H
    rw [tau_mul_coprime hab] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact IHa (by omega) h' (fun p hp hpa => H p hp (dvd_mul_of_dvd_left hpa b))
    · exact IHb (by omega) h' (fun p hp hpb => H p hp (dvd_mul_of_dvd_right hpb a))

/-- If `τ` has no zero at primes below `N`, it has no zero at all `1 ≤ n < N`. -/
theorem tau_ne_zero_of_primes_below {N : ℕ} (H : ∀ p, p.Prime → p < N → τ p ≠ 0) :
    ∀ n, 1 ≤ n → n < N → τ n ≠ 0 := by
  intro n hn hN h
  obtain ⟨p, hp, hpn, hp0⟩ := exists_prime_dvd_tau_eq_zero hn h
  exact H p hp (lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpn) hN) hp0

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.tau_prime_pow_ne_zero
#print axioms RamanujanTau.LehmerSmall.exists_prime_dvd_tau_eq_zero
