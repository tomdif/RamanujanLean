/-
# Logarithmic means of non-negative multiplicative functions (two-sided, elementary)

Standalone, reusable.  `P(M) = {p ≤ M prime}`.

* `logmean_upper`: `f ≥ 0` multiplicative, `f(p^k) ≤ B` (`k ≥ 1`),
  `Σ_{p≤M} f(p)/p ≤ κ log log M + C` for `M ≥ 2`  ⟹
  `Σ_{n≤N} f(n)/n ≤ e^{C+2B} (log N)^κ` for `N ≥ 2`.
  (Euler product over `(N+1)`-smooth numbers, only *local* summability needed.)
* `logmean_lower`: `f ≥ 0` multiplicative, `κ ≥ 0`, `f(p) ≤ 2`,
  `Σ_{p≤M} f(p) log p/p ≤ A log M` and `Σ_{p≤M} f(p)/p ≥ κ log log M − C` for `M ≥ 2`  ⟹
  `∃ c > 0, Σ_{n≤N} f(n)/n ≥ c (log N)^κ` for `N ≥ 2`.
  (Squarefree `P(M)`-numbers `≤ N`, `M = N^{1/K}`; the tail `ΠS > N` is removed by Rankin's
  trick with `δ = 1/log M`; `1 + u ≥ e^{u − u²}` on `[0,1]`.)

For *signed* `f` only `|Σ f(n)/n| ≤ Σ |f(n)|/n` follows (apply `logmean_upper` to `|f|`); a saving
from cancellation (negative mean value) is **not** of this elementary type — see the doc §7.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs3

open Finset Filter Topology ArithmeticFunction

noncomputable section

/-- Primes up to `M`. -/
def PrimesTo (M : ℕ) : Finset ℕ := (Ioc 0 M).filter Nat.Prime

lemma primesBelow_succ_eq (N : ℕ) : (N + 1).primesBelow = PrimesTo N := by
  ext p
  simp only [Nat.mem_primesBelow, PrimesTo, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩

lemma sum_inv_sq_PrimesTo_le (N : ℕ) : ∑ p ∈ PrimesTo N, 1 / (p : ℝ) ^ 2 ≤ 1 := by
  have hsub : PrimesTo N ⊆ Ioo 1 (N + 1) := fun p hp => by
    simp only [PrimesTo, mem_filter, mem_Ioc] at hp
    exact mem_Ioo.mpr ⟨hp.2.one_lt, by omega⟩
  calc ∑ p ∈ PrimesTo N, 1 / (p : ℝ) ^ 2 ≤ ∑ i ∈ Ioo 1 (N + 1), ((i : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 / ((1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 1 (N + 1)
    _ = 1 := by norm_num

lemma exp_loglog {M : ℕ} (hM : 2 ≤ M) (κ : ℝ) :
    Real.exp (κ * Real.log (Real.log M)) = Real.log M ^ κ := by
  have hL : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  rw [Real.rpow_def_of_pos hL, mul_comm]

/-! ## Upper bound -/

theorem logmean_upper (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (h0 : ∀ n, 0 ≤ f n)
    {B κ C : ℝ} (hB : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ B)
    (hS : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, f p / p ≤ κ * Real.log (Real.log M) + C) :
    ∀ N : ℕ, 2 ≤ N → ∑ n ∈ Ioc 0 N, f n / n ≤ Real.exp (C + 2 * B) * Real.log N ^ κ := by
  intro N hN
  have hB0 : 0 ≤ B := (h0 _).trans (by simpa using hB 2 1 Nat.prime_two le_rfl)
  set g : ℕ → ℝ := fun n => f n / n
  have hg0 : ∀ n, 0 ≤ g n := fun n => div_nonneg (h0 n) (Nat.cast_nonneg _)
  have hg1 : g 1 = 1 := by simp [g, hf.map_one]
  have hgm : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := fun {m n} h => by
    simp only [g, hf.map_mul_of_coprime h, Nat.cast_mul]; ring
  -- local bounds
  have hloc : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, g (p ^ (k + 1)) ≤ B * (1 / (p : ℝ)) ^ (k + 1) := by
    intro p hp k
    simp only [g, Nat.cast_pow]
    rw [div_eq_mul_inv, one_div, inv_pow]
    exact mul_le_mul_of_nonneg_right (hB p (k + 1) hp (by omega)) (by positivity)
  have hgeo : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => (1 / (p : ℝ)) ^ k := fun hp =>
    summable_geometric_of_lt_one (by positivity)
      ((div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt))
  have hsumloc : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ => ‖g (p ^ k)‖ := by
    intro p hp
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (((summable_nat_add_iff 1).mpr (hgeo hp)).mul_left B)
    rw [Real.norm_of_nonneg (hg0 _)]; exact hloc hp k
  obtain ⟨hsm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg1 hgm hsumloc (N + 1)
  rw [primesBelow_succ_eq] at hhas
  have hsm' : Summable fun m : (N + 1).smoothNumbers => g m :=
    hsm.of_norm
  -- finite sum ≤ smooth sum
  have hmem : ∀ n ∈ Ioc 0 N, n ∈ (N + 1).smoothNumbers := fun n hn => by
    rw [mem_Ioc] at hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  have h1 : ∑ n ∈ Ioc 0 N, g n ≤ ∏ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) := by
    rw [← hhas.tsum_eq, ← Finset.sum_subtype_of_mem g hmem]
    exact hsm'.sum_le_tsum _ (fun _ _ => hg0 _)
  -- local factor ≤ exp(f(p)/p + 2B/p²)
  have h2 : ∀ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) ≤ Real.exp (f p / p + 2 * B * (1 / (p : ℝ) ^ 2)) := by
    intro p hpP
    have hp : p.Prime := (mem_filter.mp hpP).2
    have hs : Summable fun k : ℕ => g (p ^ k) := (hsumloc hp).of_norm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hq1 : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    rw [← hs.sum_add_tsum_nat_add 2]
    have e : ∑ k ∈ range 2, g (p ^ k) = 1 + f p / p := by
      simp [sum_range_succ, g, hf.map_one]
    have htail : ∑' k : ℕ, g (p ^ (k + 2)) ≤ ∑' k : ℕ, B * (1 / (p : ℝ)) ^ (k + 2) :=
      ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum (fun k => hloc hp (k + 1))
        (((summable_nat_add_iff 2).mpr (hgeo hp)).mul_left B)
    have hgv : ∑' k : ℕ, B * (1 / (p : ℝ)) ^ (k + 2) = B * ((1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹) := by
      rw [tsum_mul_left]
      simp_rw [pow_add, mul_comm _ ((1 / (p : ℝ)) ^ 2)]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    have h12 : (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
      have hh : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hb : B * ((1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹) ≤ 2 * B * (1 / (p : ℝ) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h12 (show 0 ≤ (1 / (p : ℝ)) ^ 2 by positivity)
      rw [one_div_pow] at this ⊢
      nlinarith
    rw [e]
    have := Real.add_one_le_exp (f p / p + 2 * B * (1 / (p : ℝ) ^ 2))
    linarith
  have h3 : ∏ p ∈ PrimesTo N, ∑' k : ℕ, g (p ^ k) ≤
      Real.exp (∑ p ∈ PrimesTo N, (f p / p + 2 * B * (1 / (p : ℝ) ^ 2))) := by
    rw [Real.exp_sum]
    exact prod_le_prod (fun p _ => tsum_nonneg fun _ => hg0 _) h2
  have h4 : ∑ p ∈ PrimesTo N, (f p / p + 2 * B * (1 / (p : ℝ) ^ 2)) ≤
      κ * Real.log (Real.log N) + C + 2 * B := by
    rw [sum_add_distrib, ← mul_sum]
    have := sum_inv_sq_PrimesTo_le N
    have := hS N hN
    nlinarith
  calc ∑ n ∈ Ioc 0 N, f n / n = ∑ n ∈ Ioc 0 N, g n := rfl
    _ ≤ _ := h1.trans h3
    _ ≤ Real.exp (κ * Real.log (Real.log N) + C + 2 * B) := Real.exp_le_exp.mpr h4
    _ = Real.exp (C + 2 * B) * Real.log N ^ κ := by
        rw [← exp_loglog hN κ, ← Real.exp_add]; ring_nf

/-- `|f|` as an arithmetic function (multiplicative if `f` is). -/
def absF (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun n => |f n|, by simp⟩

lemma absF_mult {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) : (absF f).IsMultiplicative :=
  ⟨by simp [absF, hf.map_one], fun {m n} h => by simp [absF, hf.map_mul_of_coprime h, abs_mul]⟩

/-- **Signed version (no cancellation)**: for real multiplicative `f` with `|f(p^k)| ≤ B` and
`Σ_{p≤M} |f(p)|/p ≤ κ log log M + C`, `|Σ_{n≤N} f(n)/n| ≤ e^{C+2B}(log N)^κ`. -/
theorem logmean_upper_abs (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    {B κ C : ℝ} (hB : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ B)
    (hS : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, |f p| / p ≤ κ * Real.log (Real.log M) + C) :
    ∀ N : ℕ, 2 ≤ N → |∑ n ∈ Ioc 0 N, f n / n| ≤ Real.exp (C + 2 * B) * Real.log N ^ κ := by
  intro N hN
  have h := logmean_upper (absF f) (absF_mult hf) (fun n => abs_nonneg (f n)) hB hS N hN
  refine (abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) h)
  exact sum_congr rfl fun n _ => by simp [absF, abs_div]

/-! ## Lower bound -/

lemma one_add_ge_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Real.exp (u - u ^ 2) ≤ 1 + u := by
  have hx0 : 0 ≤ u - u ^ 2 := by nlinarith
  have hx1 : u - u ^ 2 ≤ 1 := by nlinarith
  have h := Real.exp_bound' hx0 hx1 (n := 2) (by norm_num)
  simp [sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg (u - u ^ 2), mul_nonneg h0 (sub_nonneg.mpr h1)]

lemma exp_sub_one_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x - 1 ≤ x * Real.exp 1 := by
  have h := Real.add_one_le_exp (-x)
  have hx : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hm : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
  have : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith [Real.exp_pos x]
  nlinarith

/-- The squarefree `P`-numbers `≤ N` inject into `[1, N]`. -/
lemma sum_powerset_le (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (h0 : ∀ n, 0 ≤ f n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    ∑ S ∈ P.powerset.filter (fun S => ∏ p ∈ S, p ≤ N), ∏ p ∈ S, f p / p ≤
      ∑ n ∈ Ioc 0 N, f n / n := by
  set T := P.powerset.filter (fun S => ∏ p ∈ S, p ≤ N)
  have hval : ∀ S ∈ T, ∏ p ∈ S, f p / p = f (∏ p ∈ S, p) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
    intro S hS
    have hSP : S ⊆ P := mem_powerset.mp (mem_filter.mp hS).1
    rw [prod_div_distrib, hf.map_prod_of_prime S (fun p hp => hP p (hSP hp)), Nat.cast_prod]
  rw [sum_congr rfl hval]
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) T := by
    intro S hS S' hS' h
    have h1 := Nat.primeFactors_prod (s := S) (fun p hp =>
      hP p (mem_powerset.mp (mem_filter.mp hS).1 hp))
    have h2 := Nat.primeFactors_prod (s := S') (fun p hp =>
      hP p (mem_powerset.mp (mem_filter.mp hS').1 hp))
    simp only at h
    rw [← h1, ← h2, h]
  rw [← sum_image (f := fun n => f n / (n : ℝ)) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => div_nonneg (h0 n) (Nat.cast_nonneg _)
  intro n hn
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hn
  have hSP : S ⊆ P := mem_powerset.mp (mem_filter.mp hS).1
  refine mem_Ioc.mpr ⟨?_, (mem_filter.mp hS).2⟩
  exact prod_pos fun p hp => (hP p (hSP hp)).pos

/-- Rankin tail: `Σ_{S ⊆ P, ΠS > N} Π_S u ≤ N^{−δ} Π_P (1 + u_p p^δ)`. -/
lemma sum_powerset_tail_le (u : ℕ → ℝ) (hu : ∀ p, 0 ≤ u p) (P : Finset ℕ) (_hP : ∀ p ∈ P, 0 < p)
    (N : ℕ) (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ S ∈ P.powerset.filter (fun S => ¬ ∏ p ∈ S, p ≤ N), ∏ p ∈ S, u p ≤
      (N : ℝ) ^ (-δ) * ∏ p ∈ P, (1 + u p * (p : ℝ) ^ δ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prod_one_add, mul_sum]
  have hnn : ∀ S ∈ P.powerset, 0 ≤ (N : ℝ) ^ (-δ) * ∏ p ∈ S, u p * (p : ℝ) ^ δ := fun S _ =>
    mul_nonneg (by positivity) (prod_nonneg fun p _ => mul_nonneg (hu p) (by positivity))
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg
    (filter_subset (fun S : Finset ℕ => ¬ ∏ p ∈ S, p ≤ N) P.powerset) fun S hS _ => hnn S hS)
  refine sum_le_sum fun S hS => ?_
  have hgt : (N : ℝ) < ∏ p ∈ S, (p : ℝ) := by
    have := (mem_filter.mp hS).2; push Not at this
    rw [← Nat.cast_prod]; exact_mod_cast this
  have hpow : 1 ≤ (N : ℝ) ^ (-δ) * (∏ p ∈ S, (p : ℝ)) ^ δ := by
    rw [Real.rpow_neg hN0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    exact Real.rpow_le_rpow hN0.le hgt.le hδ
  have hu0 : 0 ≤ ∏ p ∈ S, u p := prod_nonneg fun p _ => hu p
  rw [prod_mul_distrib, Real.finsetProd_rpow S _ (fun p _ => Nat.cast_nonneg _)]
  calc ∏ p ∈ S, u p ≤ (∏ p ∈ S, u p) * ((N : ℝ) ^ (-δ) * (∏ p ∈ S, (p : ℝ)) ^ δ) :=
        le_mul_of_one_le_right hu0 hpow
    _ = (N : ℝ) ^ (-δ) * ((∏ p ∈ S, u p) * (∏ p ∈ S, (p : ℝ)) ^ δ) := by ring

theorem logmean_lower (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) (h0 : ∀ n, 0 ≤ f n)
    {A κ C : ℝ} (hκ : 0 ≤ κ) (hf2 : ∀ p : ℕ, p.Prime → f p ≤ 2)
    (hA : ∀ M : ℕ, 2 ≤ M → ∑ p ∈ PrimesTo M, f p * Real.log p / p ≤ A * Real.log M)
    (hS : ∀ M : ℕ, 2 ≤ M → κ * Real.log (Real.log M) - C ≤ ∑ p ∈ PrimesTo M, f p / p) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * Real.log N ^ κ ≤ ∑ n ∈ Ioc 0 N, f n / n := by
  set u : ℕ → ℝ := fun p => f p / p
  have hu0 : ∀ p, 0 ≤ u p := fun p => div_nonneg (h0 p) (Nat.cast_nonneg _)
  have hA0 : 0 ≤ A := by
    have h := hA 2 le_rfl
    have hs : 0 ≤ ∑ p ∈ PrimesTo 2, f p * Real.log p / p :=
      sum_nonneg fun p _ => div_nonneg (mul_nonneg (h0 p) (Real.log_natCast_nonneg p))
        (Nat.cast_nonneg _)
    have hl : 0 < Real.log (2 : ℕ) := Real.log_pos (by norm_num)
    push_cast at h hl hs
    by_contra hneg; push Not at hneg; nlinarith [mul_neg_of_neg_of_pos hneg hl]
  set K : ℕ := ⌈Real.exp 1 * A⌉₊ + 1
  have hK1 : 1 ≤ K := by simp [K]
  have hKA : Real.exp 1 * A + 1 ≤ K := by
    have := Nat.le_ceil (Real.exp 1 * A); simp only [K]; push_cast; linarith
  set c₀ : ℝ := Real.exp (-C - 4) / 4
  -- core estimate for `N ≥ M^K`
  have core : ∀ M N : ℕ, 2 ≤ M → M ^ K ≤ N →
      c₀ * Real.log M ^ κ ≤ ∑ n ∈ Ioc 0 N, f n / n := by
    intro M N hM hMN
    have hN : 0 < N := lt_of_lt_of_le (pow_pos (by omega) _) hMN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hLM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    set P := PrimesTo M
    have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
    have hPle : ∀ p ∈ P, p ≤ M := fun p hp => (mem_Ioc.mp (mem_filter.mp hp).1).2
    set δ : ℝ := 1 / Real.log M
    have hδ : 0 ≤ δ := by positivity
    -- (i) Π(1+u) splits
    have hsplit := sum_filter_add_sum_filter_not P.powerset (fun S => ∏ p ∈ S, p ≤ N)
      (fun S => ∏ p ∈ S, u p)
    rw [← prod_one_add] at hsplit
    have hlow := sum_powerset_le f hf h0 P hPp N
    have htail := sum_powerset_tail_le u hu0 P (fun p hp => (hPp p hp).pos) N hN hδ
    -- (ii) Π(1 + u p^δ) ≤ Π(1+u) · exp(Σ u (p^δ − 1)) ≤ Π(1+u) · e^{eA}
    have hloc : ∀ p ∈ P, 1 + u p * (p : ℝ) ^ δ ≤ (1 + u p) * Real.exp (u p * ((p : ℝ) ^ δ - 1)) := by
      intro p hp
      have hq : 1 ≤ (p : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (hPp p hp).one_lt.le) hδ
      have := Real.add_one_le_exp (u p * ((p : ℝ) ^ δ - 1))
      have h1 : 0 ≤ u p * ((p : ℝ) ^ δ - 1) := mul_nonneg (hu0 p) (by linarith)
      nlinarith [hu0 p, mul_nonneg (hu0 p) h1]
    have hexpo : ∑ p ∈ P, u p * ((p : ℝ) ^ δ - 1) ≤ Real.exp 1 * A := by
      have hb : ∀ p ∈ P, u p * ((p : ℝ) ^ δ - 1) ≤ Real.exp 1 * δ * (f p * Real.log p / p) := by
        intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPp p hp).pos
        have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hx1 : δ * Real.log p ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hLM]
          exact Real.log_le_log hp0 (by exact_mod_cast hPle p hp)
        have hpd : (p : ℝ) ^ δ = Real.exp (δ * Real.log p) := by
          rw [Real.rpow_def_of_pos hp0, mul_comm]
        have := exp_sub_one_le (mul_nonneg hδ hlp) hx1
        rw [hpd]
        calc u p * (Real.exp (δ * Real.log p) - 1) ≤ u p * (δ * Real.log p * Real.exp 1) :=
              mul_le_mul_of_nonneg_left this (hu0 p)
          _ = Real.exp 1 * δ * (f p * Real.log p / p) := by simp only [u]; ring
      calc ∑ p ∈ P, u p * ((p : ℝ) ^ δ - 1) ≤ ∑ p ∈ P, Real.exp 1 * δ * (f p * Real.log p / p) :=
            sum_le_sum hb
        _ = Real.exp 1 * δ * ∑ p ∈ P, f p * Real.log p / p := by rw [mul_sum]
        _ ≤ Real.exp 1 * δ * (A * Real.log M) :=
            mul_le_mul_of_nonneg_left (hA M hM) (by positivity)
        _ = Real.exp 1 * A := by simp only [δ]; field_simp
    have hPi0 : 0 ≤ ∏ p ∈ P, (1 + u p) := prod_nonneg fun p _ => by linarith [hu0 p]
    have hprod : ∏ p ∈ P, (1 + u p * (p : ℝ) ^ δ) ≤ (∏ p ∈ P, (1 + u p)) * Real.exp (Real.exp 1 * A) := by
      calc ∏ p ∈ P, (1 + u p * (p : ℝ) ^ δ) ≤ ∏ p ∈ P, ((1 + u p) * Real.exp (u p * ((p : ℝ) ^ δ - 1))) :=
            prod_le_prod (fun p _ => by
              have := Real.rpow_nonneg (Nat.cast_nonneg p) δ; nlinarith [hu0 p]) hloc
        _ = (∏ p ∈ P, (1 + u p)) * Real.exp (∑ p ∈ P, u p * ((p : ℝ) ^ δ - 1)) := by
            rw [prod_mul_distrib, Real.exp_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) hPi0
    -- (iii) `N^{−δ} ≤ e^{−K}`
    have hNd : (N : ℝ) ^ (-δ) ≤ Real.exp (-(K : ℝ)) := by
      have hlogN : (K : ℝ) * Real.log M ≤ Real.log N := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hMN)
      rw [Real.rpow_def_of_pos hN0]
      apply Real.exp_le_exp.mpr
      have : Real.log N * -δ = -(Real.log N / Real.log M) := by simp only [δ]; ring
      rw [this, neg_le_neg_iff, le_div_iff₀ hLM]; exact hlogN
    have hsmall : Real.exp (-(K : ℝ)) * Real.exp (Real.exp 1 * A) ≤ 1 / 2 := by
      rw [← Real.exp_add]
      have : -(K : ℝ) + Real.exp 1 * A ≤ -1 := by linarith
      calc Real.exp (-(K : ℝ) + Real.exp 1 * A) ≤ Real.exp (-1) := Real.exp_le_exp.mpr this
        _ ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith [Real.add_one_le_exp (1 : ℝ), Real.exp_one_gt_d9]
    have hT : ∑ S ∈ P.powerset.filter (fun S => ¬ ∏ p ∈ S, p ≤ N), ∏ p ∈ S, u p ≤
        1 / 2 * ∏ p ∈ P, (1 + u p) := by
      calc _ ≤ (N : ℝ) ^ (-δ) * ∏ p ∈ P, (1 + u p * (p : ℝ) ^ δ) := htail
        _ ≤ Real.exp (-(K : ℝ)) * ((∏ p ∈ P, (1 + u p)) * Real.exp (Real.exp 1 * A)) :=
            mul_le_mul hNd hprod (prod_nonneg fun p _ => by
              have := Real.rpow_nonneg (Nat.cast_nonneg p) δ; nlinarith [hu0 p]) (by positivity)
        _ = (Real.exp (-(K : ℝ)) * Real.exp (Real.exp 1 * A)) * ∏ p ∈ P, (1 + u p) := by ring
        _ ≤ 1 / 2 * ∏ p ∈ P, (1 + u p) := mul_le_mul_of_nonneg_right hsmall hPi0
    -- (iv) Π(1+u) ≥ exp(Σu − Σu²) ≥ e^{−C−4} (log M)^κ
    have hu1 : ∀ p ∈ P, u p ≤ 2 / p := fun p hp =>
      div_le_div_of_nonneg_right (hf2 p (hPp p hp)) (Nat.cast_nonneg _)
    have hPi : Real.exp (∑ p ∈ P, (u p - u p ^ 2)) ≤ ∏ p ∈ P, (1 + u p) := by
      rw [Real.exp_sum]
      refine prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => one_add_ge_exp (hu0 p) ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
      exact (hu1 p hp).trans ((div_le_one (by linarith)).mpr hp2)
    have hsq : ∑ p ∈ P, u p ^ 2 ≤ 4 := by
      have := sum_inv_sq_PrimesTo_le M
      calc ∑ p ∈ P, u p ^ 2 ≤ ∑ p ∈ P, 4 * (1 / (p : ℝ) ^ 2) := by
            refine sum_le_sum fun p hp => ?_
            have := pow_le_pow_left₀ (hu0 p) (hu1 p hp) 2
            calc u p ^ 2 ≤ (2 / (p : ℝ)) ^ 2 := this
              _ = 4 * (1 / (p : ℝ) ^ 2) := by ring
        _ = 4 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ 4 := by linarith
    have hSM := hS M hM
    have hPi2 : Real.exp (-C - 4) * Real.log M ^ κ ≤ ∏ p ∈ P, (1 + u p) := by
      rw [← exp_loglog hM κ, ← Real.exp_add]
      refine le_trans (Real.exp_le_exp.mpr ?_) hPi
      rw [sum_sub_distrib]
      have : ∑ p ∈ P, u p = ∑ p ∈ PrimesTo M, f p / p := rfl
      linarith
    -- assemble
    have hlow' : ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∏ p ∈ S, p ≤ N), ∏ p ∈ S, u p ≤
        ∑ n ∈ Ioc 0 N, f n / n := hlow
    have : ∏ p ∈ P, (1 + u p) ≤ ∑ n ∈ Ioc 0 N, f n / n + 1 / 2 * ∏ p ∈ P, (1 + u p) := by
      linarith [hsplit, hlow', hT]
    simp only [c₀]
    nlinarith
  -- choose `M` with `M^K ≤ N < (M+1)^K`
  have hc₀ : 0 < c₀ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (c₀ * (1 / (2 * K)) ^ κ) (1 / (K * Real.log 2) ^ κ), lt_min (by positivity)
    (by positivity), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rcases lt_or_ge N (2 ^ K) with hsm | hbig
  · -- small `N`: the term `n = 1`
    have h1 : 1 ≤ ∑ n ∈ Ioc 0 N, f n / n := by
      have := single_le_sum (f := fun n => f n / (n : ℝ))
        (fun n _ => div_nonneg (h0 n) (Nat.cast_nonneg _)) (show 1 ∈ Ioc 0 N by simp; omega)
      simpa [hf.map_one] using this
    have hlogle : Real.log N ≤ K * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_le_log hN0 (by exact_mod_cast hsm.le)
    have hpow : Real.log N ^ κ ≤ (K * Real.log 2) ^ κ := Real.rpow_le_rpow hLN.le hlogle hκ
    have hKl : 0 < (K * Real.log 2) ^ κ := Real.rpow_pos_of_pos (by positivity) _
    calc min (c₀ * (1 / (2 * K)) ^ κ) (1 / (K * Real.log 2) ^ κ) * Real.log N ^ κ
        ≤ 1 / (K * Real.log 2) ^ κ * (K * Real.log 2) ^ κ :=
          mul_le_mul (min_le_right _ _) hpow (by positivity) (by positivity)
      _ = 1 := by field_simp
      _ ≤ _ := h1
  · set M := Nat.findGreatest (fun m => m ^ K ≤ N) N
    have h2N : 2 ≤ N := hN
    have hMspec : M ^ K ≤ N := Nat.findGreatest_spec (P := fun m => m ^ K ≤ N)
      (m := 2) (by omega) hbig
    have hM2 : 2 ≤ M := Nat.le_findGreatest (P := fun m => m ^ K ≤ N) (by omega) hbig
    have hMlt : N < (M + 1) ^ K := by
      by_contra hc
      push Not at hc
      have hle : M + 1 ≤ N := by
        have : M + 1 ≤ (M + 1) ^ K := Nat.le_self_pow (by omega) _
        omega
      exact Nat.findGreatest_is_greatest (P := fun m => m ^ K ≤ N) (Nat.lt_succ_self M) hle hc
    have hLM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    have hlog : Real.log N ≤ 2 * K * Real.log M := by
      have h1 : Real.log N ≤ K * Real.log (M + 1 : ℕ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log hN0 (by exact_mod_cast hMlt.le)
      have h2 : Real.log (M + 1 : ℕ) ≤ 2 * Real.log M := by
        rw [show (2 : ℝ) * Real.log M = Real.log ((M : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
        exact Real.log_le_log (by positivity) (by push_cast; nlinarith [(show (2:ℝ) ≤ M by exact_mod_cast hM2)])
      nlinarith
    have hpow : (1 / (2 * K)) ^ κ * Real.log N ^ κ ≤ Real.log M ^ κ := by
      rw [← Real.mul_rpow (by positivity) hLN.le]
      refine Real.rpow_le_rpow (by positivity) ?_ hκ
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    calc min (c₀ * (1 / (2 * K)) ^ κ) (1 / (K * Real.log 2) ^ κ) * Real.log N ^ κ
        ≤ c₀ * (1 / (2 * K)) ^ κ * Real.log N ^ κ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = c₀ * ((1 / (2 * K)) ^ κ * Real.log N ^ κ) := by ring
      _ ≤ c₀ * Real.log M ^ κ := mul_le_mul_of_nonneg_left hpow hc₀.le
      _ ≤ _ := core M N hM2 hMspec

end

end RamanujanTau.SelbergCoeffs3
