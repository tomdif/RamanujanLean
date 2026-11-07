/-
# Kloosterman's bound for all moduli: `|S(1,n;c)| ≤ 4^{ω(c)} c^{3/4} ≪_δ c^{3/4+δ}`

Assembly of the prime bound (`KlPrime`), the prime-power bound (`KlPrimePow`) and twisted
multiplicativity (`KlBasic`), followed by the elementary divisor-type bound `4^{ω(c)} ≪_δ c^δ`.
Discharges `KloostermanBound (3/4 + δ)` for every `δ > 0`.
-/
import RamanujanTau.TauBound.KlPrime
import RamanujanTau.TauBound.KlPrimePow
import RamanujanTau.TauBound.Endgame
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex
open scoped Real

/-- Prime moduli: `|S(1,b;p)| ≤ 4 p^{3/4}`. -/
lemma norm_kl_prime_le {p : ℕ} [hp : Fact p.Prime] (b : ZMod p) :
    ‖kl p 1 b‖ ≤ 4 * (p : ℝ) ^ (3 / 4 : ℝ) := by
  have h4 := norm_kl_prime_pow_four_le b
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hR : 0 ≤ 4 * (p : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hR4 : (4 * (p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 256 * (p : ℝ) ^ 3 := by
    rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (3 / 4 : ℝ)), ← Real.rpow_mul hp0.le]
    norm_num
  have : ‖kl p 1 b‖ ^ 4 ≤ (4 * (p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 := by
    rw [hR4]; nlinarith [pow_pos hp0 3]
  exact le_of_pow_le_pow_left₀ (by norm_num) hR this

/-- The multiplicative bound `4^{ω(c)} c^{3/4}`. -/
noncomputable def klMajor (c : ℕ) : ℝ := (4 : ℝ) ^ c.primeFactors.card * (c : ℝ) ^ (3 / 4 : ℝ)

lemma klMajor_primePow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    klMajor (p ^ k) = 4 * ((p : ℝ) ^ k) ^ (3 / 4 : ℝ) := by
  rw [klMajor, Nat.primeFactors_prime_pow hk.ne' hp]; push_cast; simp

lemma kloosterman_prime_le {p : ℕ} (hp : p.Prime) (n : ℤ) :
    ‖kloosterman 1 n p‖ ≤ klMajor p := by
  haveI := Fact.mk hp
  rw [kloosterman_eq_kl, klMajor, Nat.Prime.primeFactors hp]
  simpa using norm_kl_prime_le (p := p) (n : ZMod p)

theorem norm_kloosterman_le_klMajor : ∀ c : ℕ, ∀ n : ℤ, ‖kloosterman 1 n c‖ ≤ klMajor c := by
  intro c
  induction c using Nat.recOnPosPrimePosCoprime with
  | zero => intro n; simp [kloosterman, klMajor]
  | one =>
    intro n
    refine (norm_kloosterman_le 1 n 1).trans ?_
    simp [klMajor]
  | prime_pow p k hp hk =>
    intro n
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      rw [pow_one]
      exact kloosterman_prime_le hp n
    · rw [kloosterman_eq_kl, klMajor_primePow hp hk]
      push_cast
      refine (norm_kl_primePow_le hp hk2 _).trans ?_
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast]
      gcongr
      · exact_mod_cast hp.one_lt.le
      · have : (((k + 1) / 2 : ℕ) : ℝ) ≤ ((k : ℝ) + 1) / 2 := by
          rw [le_div_iff₀ (by norm_num)]
          have : ((k + 1) / 2) * 2 ≤ k + 1 := Nat.div_mul_le_self _ _
          exact_mod_cast this
        have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
  | coprime a b ha hb hab iha ihb =>
    intro n
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    haveI : NeZero (a * b) := ⟨by positivity⟩
    -- Bézout: u b + v a = 1
    have hg : Int.gcd (a : ℤ) (b : ℤ) = 1 := by simpa [Int.gcd_natCast_natCast] using hab
    set v := Int.gcdA (a : ℤ) (b : ℤ)
    set u := Int.gcdB (a : ℤ) (b : ℤ)
    have huv : u * (b : ℤ) + v * (a : ℤ) = 1 := by
      have := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
      rw [hg] at this; push_cast at this; linarith
    rw [kloosterman_eq_kl, kl_mul_coprime hab u v huv 1 n]
    -- u is a unit mod a, v is a unit mod b
    have hua : (u : ZMod a) * (b : ZMod a) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod a)) huv
      simpa using this
    have hvb : (v : ZMod b) * (a : ZMod b) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod b)) huv
      simpa using this
    have hu : IsUnit (u : ZMod a) := IsUnit.of_mul_eq_one _ hua
    have hv : IsUnit (v : ZMod b) := IsUnit.of_mul_eq_one _ hvb
    have e1 : kl a ((u * 1 : ℤ) : ZMod a) ((u * n : ℤ) : ZMod a) =
        kloosterman 1 (u * (u * n)) a := by
      rw [kloosterman_eq_kl]
      have := kl_unit_eq a hu.unit ((u * n : ℤ) : ZMod a)
      simp only [IsUnit.unit_spec] at this
      push_cast at this ⊢
      rw [mul_one, this]
    have e2 : kl b ((v * 1 : ℤ) : ZMod b) ((v * n : ℤ) : ZMod b) =
        kloosterman 1 (v * (v * n)) b := by
      rw [kloosterman_eq_kl]
      have := kl_unit_eq b hv.unit ((v * n : ℤ) : ZMod b)
      simp only [IsUnit.unit_spec] at this
      push_cast at this ⊢
      rw [mul_one, this]
    have e1' := e1; have e2' := e2
    push_cast at e1' e2'
    push_cast
    rw [e1', e2', norm_mul]
    have h1 := iha (u * (u * n))
    have h2 := ihb (v * (v * n))
    have hmaj : klMajor (a * b) = klMajor a * klMajor b := by
      simp only [klMajor]
      rw [Nat.Coprime.primeFactors_mul hab,
        Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab), pow_add]
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    rw [hmaj]
    exact mul_le_mul h1 h2 (norm_nonneg _) (by unfold klMajor; positivity)

/-- `4^{ω(c)} ≤ K_δ c^δ`. -/
theorem four_pow_omega_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ c : ℕ, 1 ≤ c → (4 : ℝ) ^ c.primeFactors.card ≤ K * (c : ℝ) ^ δ := by
  classical
  set P0 : ℕ := ⌈(4 : ℝ) ^ (1 / δ)⌉₊
  refine ⟨(4 : ℝ) ^ P0, fun c hc => ?_⟩
  have hpt : ∀ p ∈ c.primeFactors,
      (4 : ℝ) ≤ (if p < P0 then (4 : ℝ) else 1) * (p : ℝ) ^ δ := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    split_ifs with h
    · have : (1 : ℝ) ≤ (p : ℝ) ^ δ := Real.one_le_rpow hp1 hδ.le
      nlinarith
    · push Not at h
      have hP : (4 : ℝ) ^ (1 / δ) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast h)
      have : ((4 : ℝ) ^ (1 / δ)) ^ δ ≤ (p : ℝ) ^ δ :=
        Real.rpow_le_rpow (by positivity) hP hδ.le
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at this
      linarith
  have h1 : (4 : ℝ) ^ c.primeFactors.card ≤
      ∏ p ∈ c.primeFactors, ((if p < P0 then (4 : ℝ) else 1) * (p : ℝ) ^ δ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by norm_num) hpt
  rw [Finset.prod_mul_distrib] at h1
  have h2 : ∏ p ∈ c.primeFactors, (if p < P0 then (4 : ℝ) else 1) ≤ (4 : ℝ) ^ P0 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ (by norm_num) ?_
    calc (c.primeFactors.filter (fun p => p < P0)).card
        ≤ (Finset.range P0).card := Finset.card_le_card (fun p hp => by
          simp only [Finset.mem_filter] at hp; simpa using hp.2)
      _ = P0 := Finset.card_range _
  have h3 : ∏ p ∈ c.primeFactors, (p : ℝ) ^ δ ≤ (c : ℝ) ^ δ := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
    have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd c)
    rw [← Nat.cast_prod]; exact_mod_cast this
  calc (4 : ℝ) ^ c.primeFactors.card
      ≤ (∏ p ∈ c.primeFactors, (if p < P0 then (4 : ℝ) else 1)) *
          ∏ p ∈ c.primeFactors, (p : ℝ) ^ δ := h1
    _ ≤ (4 : ℝ) ^ P0 * (c : ℝ) ^ δ := by
        apply mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)

/-- **Kloosterman's bound (1927), elementary**: `|S(1,n;c)| ≪_δ c^{3/4+δ}` uniformly in `n`. -/
theorem kloostermanBound_three_quarters (δ : ℝ) (hδ : 0 < δ) : KloostermanBound (3 / 4 + δ) := by
  obtain ⟨K, hK⟩ := four_pow_omega_le δ hδ
  refine ⟨K, fun n c hc => ?_⟩
  refine (norm_kloosterman_le_klMajor c n).trans ?_
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  rw [klMajor, Real.rpow_add hc0]
  have := hK c hc
  calc (4 : ℝ) ^ c.primeFactors.card * (c : ℝ) ^ (3 / 4 : ℝ)
      ≤ K * (c : ℝ) ^ δ * (c : ℝ) ^ (3 / 4 : ℝ) := by gcongr
    _ = K * ((c : ℝ) ^ (3 / 4 : ℝ) * (c : ℝ) ^ δ) := by ring

end RamanujanTau.TauBound
