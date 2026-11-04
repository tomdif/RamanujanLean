/-
# Generic assembly: local Kloosterman bounds ⇒ `KloostermanBound (α + δ)` ⇒ `τ(n) = O(n^{(11+α)/2+ε})`

* `LocalKlBound α C`: `|S(1,b;p^k)| ≤ C (p^k)^α` for every prime power `p^k` (`k ≥ 1`) and every `b`.
* `norm_kloosterman_le_major`: under `LocalKlBound α C`, `|S(1,n;c)| ≤ C^{ω(c)} c^α` for all `c ≥ 1`
  (twisted multiplicativity `kl_mul_coprime`).
* `const_pow_omega_le`: `C^{ω(c)} ≪_δ c^δ`.
* `kloostermanBound_of_local`: `LocalKlBound α C → ∀ δ > 0, KloostermanBound (α + δ)`.
* `tau_isBigO_of_kloostermanFamily`: `(∀ δ > 0, KloostermanBound (α + δ)) → ∀ ε > 0,
  τ(n) = O(n^{(11+α)/2+ε})` (unconditional Poincaré input from `TauBound`).
-/
import RamanujanTau.TauBound.KlAssembly
import RamanujanTau.TauBound.Unconditional

set_option autoImplicit false

namespace RamanujanTau.WeilKloosterman

open Complex Filter Asymptotics RamanujanTau.TauBound
open scoped Real

/-- Local (prime-power) Kloosterman bound with exponent `α` and constant `C`. -/
def LocalKlBound (α C : ℝ) : Prop :=
  ∀ (p k : ℕ), p.Prime → 1 ≤ k →
    ∀ n : ℤ, ‖kloosterman 1 n (p ^ k)‖ ≤ C * ((p : ℝ) ^ k) ^ α

/-- The multiplicative majorant `C^{ω(c)} c^α`. -/
noncomputable def major (α C : ℝ) (c : ℕ) : ℝ := C ^ c.primeFactors.card * (c : ℝ) ^ α

lemma major_nonneg {α C : ℝ} (hC : 0 ≤ C) (c : ℕ) : 0 ≤ major α C c := by
  unfold major; positivity

theorem norm_kloosterman_le_major {α C : ℝ} (hC : 0 ≤ C) (hL : LocalKlBound α C) :
    ∀ c : ℕ, 1 ≤ c → ∀ n : ℤ, ‖kloosterman 1 n c‖ ≤ major α C c := by
  intro c
  induction c using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro _ n
    refine (norm_kloosterman_le 1 n 1).trans ?_
    simp [major]
  | prime_pow p k hp hk =>
    intro _ n
    rw [major, Nat.primeFactors_prime_pow hk.ne' hp]
    have := hL p k hp hk n
    simpa using this
  | coprime a b ha hb hab iha ihb =>
    intro _ n
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    haveI : NeZero (a * b) := ⟨by positivity⟩
    have hg : Int.gcd (a : ℤ) (b : ℤ) = 1 := by simpa [Int.gcd_natCast_natCast] using hab
    set v := Int.gcdA (a : ℤ) (b : ℤ)
    set u := Int.gcdB (a : ℤ) (b : ℤ)
    have huv : u * (b : ℤ) + v * (a : ℤ) = 1 := by
      have := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
      rw [hg] at this; push_cast at this; linarith
    rw [kloosterman_eq_kl, kl_mul_coprime hab u v huv 1 n]
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
    have h1 := iha (by omega) (u * (u * n))
    have h2 := ihb (by omega) (v * (v * n))
    have hmaj : major α C (a * b) = major α C a * major α C b := by
      simp only [major]
      rw [Nat.Coprime.primeFactors_mul hab,
        Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab), pow_add]
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    rw [hmaj]
    exact mul_le_mul h1 h2 (norm_nonneg _) (major_nonneg hC _)

/-- `C^{ω(c)} ≤ K_δ c^δ` for `C ≥ 1`. -/
theorem const_pow_omega_le (C : ℝ) (hC : 1 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ c : ℕ, 1 ≤ c → C ^ c.primeFactors.card ≤ K * (c : ℝ) ^ δ := by
  classical
  set P0 : ℕ := ⌈C ^ (1 / δ)⌉₊
  have hC0 : 0 ≤ C := by linarith
  refine ⟨C ^ P0, fun c hc => ?_⟩
  have hpt : ∀ p ∈ c.primeFactors,
      C ≤ (if p < P0 then C else 1) * (p : ℝ) ^ δ := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    split_ifs with h
    · have : (1 : ℝ) ≤ (p : ℝ) ^ δ := Real.one_le_rpow hp1 hδ.le
      nlinarith
    · push Not at h
      have hP : C ^ (1 / δ) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast h)
      have : (C ^ (1 / δ)) ^ δ ≤ (p : ℝ) ^ δ :=
        Real.rpow_le_rpow (by positivity) hP hδ.le
      rw [← Real.rpow_mul hC0, one_div_mul_cancel hδ.ne', Real.rpow_one] at this
      linarith
  have h1 : C ^ c.primeFactors.card ≤
      ∏ p ∈ c.primeFactors, ((if p < P0 then C else 1) * (p : ℝ) ^ δ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hC0) hpt
  rw [Finset.prod_mul_distrib] at h1
  have h2 : ∏ p ∈ c.primeFactors, (if p < P0 then C else 1) ≤ C ^ P0 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hC ?_
    calc (c.primeFactors.filter (fun p => p < P0)).card
        ≤ (Finset.range P0).card := Finset.card_le_card (fun p hp => by
          simp only [Finset.mem_filter] at hp; simpa using hp.2)
      _ = P0 := Finset.card_range _
  have h3 : ∏ p ∈ c.primeFactors, (p : ℝ) ^ δ ≤ (c : ℝ) ^ δ := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
    have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd c)
    rw [← Nat.cast_prod]; exact_mod_cast this
  calc C ^ c.primeFactors.card
      ≤ (∏ p ∈ c.primeFactors, (if p < P0 then C else 1)) *
          ∏ p ∈ c.primeFactors, (p : ℝ) ^ δ := h1
    _ ≤ C ^ P0 * (c : ℝ) ^ δ := by
        apply mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)

/-- **Assembly.** A local bound with exponent `α` gives `KloostermanBound (α + δ)` for all `δ > 0`. -/
theorem kloostermanBound_of_local {α C : ℝ} (hC : 1 ≤ C) (hL : LocalKlBound α C)
    (δ : ℝ) (hδ : 0 < δ) : KloostermanBound (α + δ) := by
  obtain ⟨K, hK⟩ := const_pow_omega_le C hC δ hδ
  refine ⟨K, fun n c hc => ?_⟩
  refine (norm_kloosterman_le_major (by linarith) hL c hc n).trans ?_
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  rw [major, Real.rpow_add hc0]
  have := hK c hc
  calc C ^ c.primeFactors.card * (c : ℝ) ^ α
      ≤ K * (c : ℝ) ^ δ * (c : ℝ) ^ α := by gcongr
    _ = K * ((c : ℝ) ^ α * (c : ℝ) ^ δ) := by ring

/-- The Poincaré formula, unconditionally (from `TauBound`). -/
theorem poincareFormula : PoincareFormula :=
  poincareFormula_of_hyps poincareIsCuspForm poincareUnfolding poincareFirstCoeffNeZero

/-- **Generic sub-Hecke bound.** If `KloostermanBound (α + δ)` for every `δ > 0`, with `0 ≤ α`,
then `τ(n) = O(n^{(11+α)/2 + ε})` for every `ε > 0`. -/
theorem tau_isBigO_of_kloostermanFamily {α : ℝ} (hα0 : 0 ≤ α)
    (hK : ∀ δ : ℝ, 0 < δ → KloostermanBound (α + δ)) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((11 + α) / 2 + ε) := by
  rcases lt_or_ge ε ((11 - α) / 2) with h | h
  · have := tau_isBigO_of_kloosterman (α := α + ε) (r := (11 - α) / 2 - ε) (by linarith)
      (by linarith) (by linarith) (hK ε hε) poincareFormula
    refine this.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · have := tau_isBigO_of_kloosterman (α := 1) (r := 0) (by norm_num) le_rfl (by norm_num)
      kloostermanBound_one poincareFormula
    refine this.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Sanity check: the proved `3/4` route recovers `47/8`. -/
example (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((11 + 3 / 4) / 2 + ε) :=
  tau_isBigO_of_kloostermanFamily (by norm_num) kloostermanBound_three_quarters ε hε

end RamanujanTau.WeilKloosterman
