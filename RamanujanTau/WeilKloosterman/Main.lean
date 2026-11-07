/-
# Salié / Weil exponents for `τ(n)`, conditional only on the prime-modulus Kloosterman bound

* `PrimeKlBound α`: `|S(1,b;p)| ≤ C p^α` for all primes `p` and `b ≢ 0 (mod p)`.
* `SaliePrimeBound := PrimeKlBound (2/3)` (Salié 1931/32, Davenport 1933).
* `WeilPrimeBound`: `|S(1,b;p)| ≤ 2√p` for `p ∤ b` (Weil 1948).

Everything except these prime-modulus inputs is proved here:
* `b ≡ 0`: `S(1,0;p) = -1` (`norm_kl_prime_zero_le`);
* prime powers `k ≥ 2`: `≤ 4 p^{⌈k/2⌉}` (`TauBound.norm_kl_primePow_le`, enough for `2/3`) and the
  sharp `≤ 4 p^{k/2}` for odd `p`, odd `k ≥ 3` (`norm_kl_primePow_odd_le`, stationary phase);
* composite moduli by twisted multiplicativity (`Assembly.lean`).
-/
import RamanujanTau.WeilKloosterman.Assembly
import RamanujanTau.WeilKloosterman.OddPrimePow

set_option autoImplicit false

namespace RamanujanTau.WeilKloosterman

open Complex Filter Asymptotics RamanujanTau.TauBound
open scoped Real

/-- Prime-modulus Kloosterman bound with exponent `α`. -/
def PrimeKlBound (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (p : ℕ) (hp : p.Prime), haveI : NeZero p := ⟨hp.ne_zero⟩
    ∀ b : ZMod p, b ≠ 0 → ‖kl p 1 b‖ ≤ C * (p : ℝ) ^ α

/-- **Salié's bound** (named hypothesis): `|S(1,b;p)| ≪ p^{2/3}`. -/
def SaliePrimeBound : Prop := PrimeKlBound (2 / 3)

/-- **Weil's bound** (named hypothesis): `|S(1,b;p)| ≤ 2√p` for `p ∤ b`. -/
def WeilPrimeBound : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), haveI : NeZero p := ⟨hp.ne_zero⟩
    ∀ b : ZMod p, b ≠ 0 → ‖kl p 1 b‖ ≤ 2 * Real.sqrt p

theorem primeKlBound_half_of_weil (hW : WeilPrimeBound) : PrimeKlBound (1 / 2) :=
  ⟨2, fun p hp b hb => by
    have := hW p hp b hb
    rwa [Real.sqrt_eq_rpow] at this⟩

/-- `S(1,0;p) = -1`, so `|S(1,0;p)| ≤ 1`. -/
theorem norm_kl_prime_zero_le {p : ℕ} [hp : Fact p.Prime] : ‖kl p 1 0‖ ≤ 1 := by
  classical
  have hsum : ∑ x : ZMod p, ZMod.stdAddChar x = 0 := by
    refine AddChar.sum_eq_zero_of_ne_one (fun h => ?_)
    have h1 : ZMod.stdAddChar (N := p) 1 = ZMod.stdAddChar (N := p) 0 := by
      rw [h, AddChar.map_zero_eq_one]; rfl
    exact one_ne_zero (ZMod.injective_stdAddChar h1)
  have hunits : kl p 1 0 = ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0),
      ZMod.stdAddChar x := by
    unfold kl
    simp only [one_mul, zero_mul, add_zero]
    refine Finset.sum_bij' (fun u _ => (u : ZMod p)) (fun x hx => Units.mk0 x
      (Finset.mem_filter.mp hx).2) (fun u _ => by simp) (fun _ _ => Finset.mem_univ _)
      (fun u _ => by ext; simp) (fun x _ => by simp) (fun _ _ => rfl)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : ZMod p => x ≠ 0)
    (fun x => ZMod.stdAddChar x)
  rw [hsum] at hsplit
  have hzero : ∑ x ∈ Finset.univ.filter (fun x : ZMod p => ¬ x ≠ 0), ZMod.stdAddChar x = 1 := by
    have : Finset.univ.filter (fun x : ZMod p => ¬ x ≠ 0) = {0} := by ext; simp
    rw [this, Finset.sum_singleton, AddChar.map_zero_eq_one]
  rw [hzero] at hsplit
  have : kl p 1 0 = -1 := by rw [hunits]; linear_combination hsplit
  rw [this]; simp

/-- Prime moduli, all `n`. -/
lemma prime_case {α : ℝ} (hα : 0 ≤ α) (hP : PrimeKlBound α) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ), p.Prime → ∀ n : ℤ,
      ‖kloosterman 1 n p‖ ≤ C * (p : ℝ) ^ α := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨max C 1, le_max_right _ _, fun p hp n => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) hα
  rw [kloosterman_eq_kl]
  simp only [Int.cast_one]
  by_cases hb : ((n : ℤ) : ZMod p) = 0
  · rw [hb]
    refine norm_kl_prime_zero_le.trans ?_
    nlinarith [le_max_right C 1]
  · refine (hC p hp _ hb).trans ?_
    gcongr
    exact le_max_left _ _

/-- `4/3 ≤ √2`. -/
lemma four_thirds_le_sqrt_two : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
  Real.le_sqrt_of_sq_le (by norm_num)

/-- Prime powers `k ≥ 2`: `|S(1,n;p^k)| ≤ 6 √(p^k)` for every prime `p`. -/
theorem norm_kloosterman_primePow_le_sqrt {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (n : ℤ) :
    ‖kloosterman 1 n (p ^ k)‖ ≤ 6 * Real.sqrt ((p : ℝ) ^ k) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [kloosterman_eq_kl]
  simp only [Int.cast_one]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · -- k = 2m: `4 p^m`
    refine (norm_kl_primePow_le hp hk _).trans ?_
    have e : (k + 1) / 2 = m := by omega
    rw [e, hm, pow_mul', Real.sqrt_sq (by positivity)]
    have : (0 : ℝ) ≤ (p : ℝ) ^ m := by positivity
    linarith
  · by_cases h2 : p = 2
    · -- p = 2, k = 2m+1: `4·2^{m+1} = 8·2^m ≤ 6√2·2^m`
      refine (norm_kl_primePow_le hp hk _).trans ?_
      have e : (k + 1) / 2 = m + 1 := by omega
      rw [e, hm, h2]
      have hs : Real.sqrt ((2 : ℕ) ^ (2 * m + 1) : ℝ) = (2 : ℝ) ^ m * Real.sqrt 2 := by
        rw [show ((2 : ℕ) : ℝ) ^ (2 * m + 1) = ((2 : ℝ) ^ m) ^ 2 * 2 by push_cast; ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [hs]
      have := four_thirds_le_sqrt_two
      have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      push_cast
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left this h2m.le]
    · have hm1 : 1 ≤ m := by omega
      refine (norm_kl_primePow_odd_le hp h2 hm1 hm _).trans ?_
      have : (0 : ℝ) ≤ Real.sqrt ((p : ℝ) ^ k) := Real.sqrt_nonneg _
      linarith

/-- `LocalKlBound (1/2)` from a prime bound with exponent `1/2`. -/
theorem localKlBound_half (hP : PrimeKlBound (1 / 2)) : ∃ C : ℝ, 1 ≤ C ∧ LocalKlBound (1 / 2) C := by
  obtain ⟨C, hC1, hC⟩ := prime_case (by norm_num) hP
  refine ⟨max C 6, le_trans hC1 (le_max_left _ _), fun p k hp hk n => ?_⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    simp only [pow_one]
    refine (hC p hp n).trans ?_
    gcongr; exact le_max_left _ _
  · refine (norm_kloosterman_primePow_le_sqrt hp hk2 n).trans ?_
    rw [Real.sqrt_eq_rpow]
    gcongr; exact le_max_right _ _

/-- `LocalKlBound (2/3)` from a prime bound with exponent `2/3` (prime powers via `⌈k/2⌉`). -/
theorem localKlBound_twoThirds (hP : PrimeKlBound (2 / 3)) :
    ∃ C : ℝ, 1 ≤ C ∧ LocalKlBound (2 / 3) C := by
  obtain ⟨C, hC1, hC⟩ := prime_case (by norm_num) hP
  refine ⟨max C 4, le_trans hC1 (le_max_left _ _), fun p k hp hk n => ?_⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    simp only [pow_one]
    refine (hC p hp n).trans ?_
    gcongr; exact le_max_left _ _
  · haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) ≤ p := by linarith
    rw [kloosterman_eq_kl]
    simp only [Int.cast_one]
    refine (norm_kl_primePow_le hp hk2 _).trans ?_
    have hexp : ((((k + 1) / 2 : ℕ)) : ℝ) ≤ (k : ℝ) * (2 / 3) := by
      have : 3 * ((k + 1) / 2) ≤ 2 * k := by omega
      have : ((3 * ((k + 1) / 2) : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hpow : (p : ℝ) ^ ((k + 1) / 2) ≤ ((p : ℝ) ^ k) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp0]
      exact Real.rpow_le_rpow_of_exponent_le hp1 hexp
    have : (0 : ℝ) ≤ (p : ℝ) ^ ((k + 1) / 2) := by positivity
    calc 4 * (p : ℝ) ^ ((k + 1) / 2) ≤ max C 4 * (p : ℝ) ^ ((k + 1) / 2) := by
          gcongr; exact le_max_right _ _
      _ ≤ max C 4 * ((p : ℝ) ^ k) ^ (2 / 3 : ℝ) := by
          gcongr

/-- **G1 (conditional)**: Salié's prime bound gives `KloostermanBound (2/3 + δ)` for all `δ > 0`. -/
theorem kloostermanBound_twoThirds_of_salie (hS : SaliePrimeBound) (δ : ℝ) (hδ : 0 < δ) :
    KloostermanBound (2 / 3 + δ) := by
  obtain ⟨C, hC, hL⟩ := localKlBound_twoThirds hS
  exact kloostermanBound_of_local hC hL δ hδ

/-- **G2 (conditional)**: Weil's prime bound gives `KloostermanBound (1/2 + δ)` for all `δ > 0`. -/
theorem kloostermanBound_half_of_weil (hW : WeilPrimeBound) (δ : ℝ) (hδ : 0 < δ) :
    KloostermanBound (1 / 2 + δ) := by
  obtain ⟨C, hC, hL⟩ := localKlBound_half (primeKlBound_half_of_weil hW)
  exact kloostermanBound_of_local hC hL δ hδ

/-- **Salié's exponent for `τ`**: `SaliePrimeBound → τ(n) = O(n^{35/6+ε})`. -/
theorem tau_isBigO_35_6_of_salie (hS : SaliePrimeBound) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((35 / 6 : ℝ) + ε) := by
  have := tau_isBigO_of_kloostermanFamily (α := 2 / 3) (by norm_num)
    (kloostermanBound_twoThirds_of_salie hS) ε hε
  have e : ((11 : ℝ) + 2 / 3) / 2 = 35 / 6 := by norm_num
  rwa [e] at this

/-- **Weil's exponent for `τ` (1948)**: `WeilPrimeBound → τ(n) = O(n^{23/4+ε})`. -/
theorem tau_isBigO_23_4_of_weil (hW : WeilPrimeBound) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((23 / 4 : ℝ) + ε) := by
  have := tau_isBigO_of_kloostermanFamily (α := 1 / 2) (by norm_num)
    (kloostermanBound_half_of_weil hW) ε hε
  have e : ((11 : ℝ) + 1 / 2) / 2 = 23 / 4 := by norm_num
  rwa [e] at this

/-- Same, from any prime bound `|S(1,b;p)| ≤ C √p` (any constant). -/
theorem tau_isBigO_23_4_of_primeKlBound (hP : PrimeKlBound (1 / 2)) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((23 / 4 : ℝ) + ε) := by
  obtain ⟨C, hC, hL⟩ := localKlBound_half hP
  have := tau_isBigO_of_kloostermanFamily (α := 1 / 2) (by norm_num)
    (kloostermanBound_of_local hC hL) ε hε
  have e : ((11 : ℝ) + 1 / 2) / 2 = 23 / 4 := by norm_num
  rwa [e] at this

end RamanujanTau.WeilKloosterman

#print axioms RamanujanTau.WeilKloosterman.norm_kl_primePow_odd_le
#print axioms RamanujanTau.WeilKloosterman.kloostermanBound_of_local
#print axioms RamanujanTau.WeilKloosterman.tau_isBigO_of_kloostermanFamily
#print axioms RamanujanTau.WeilKloosterman.norm_kloosterman_primePow_le_sqrt
#print axioms RamanujanTau.WeilKloosterman.tau_isBigO_35_6_of_salie
#print axioms RamanujanTau.WeilKloosterman.tau_isBigO_23_4_of_weil
#print axioms RamanujanTau.WeilKloosterman.tau_isBigO_23_4_of_primeKlBound
