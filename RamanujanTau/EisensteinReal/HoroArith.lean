/-
# Arithmetic input for horocycle equidistribution (Route B)

* `coprimeCount_bound`: the number of integers `a ∈ [u, v)` coprime to `c ≥ 1` is
  `(v − u)·ν(c) + O(d(c))`, `ν(c) = ∑_{e ∣ c} μ(e)/e` (Möbius inversion; no totient needed).
* `sum_Ioc_antidiag`: `∑_{n ≤ N} ∑_{em = n} F(e,m) = ∑_{e ≤ N} ∑_{m ≤ N/e} F(e,m)`.
* `abs_riemannS_sub_le`: the Riemann sum `S(h) = ∑_{1 ≤ m ≤ 1/h} h·√(1 − (mh)²)` is within `h`
  of `W = ∫₀¹ √(1 − t²) dt`.
* `tendsto_mainT`: `T(s) = ∑ₑ μ(e)/e² · S(s e) → κ W` as `s → 0⁺`, `κ = ∑ μ(e)/e²`
  (dominated convergence; the value of `κ` is never needed).
* `tendsto_errorE`: `s · (∑_{e ≤ 1/s} 1/e)² → 0`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ### Möbius count of coprime integers in an interval -/

lemma sum_moebius_divisors (n : ℕ) :
    ∑ e ∈ n.divisors, (μ e : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only at h
  rw [coe_mul_zeta_apply] at h
  rw [h, one_apply]

/-- Integers in `[u, v)` coprime to `c`. -/
noncomputable def coprimeSet (c : ℕ) (u v : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈u⌉ ⌈v⌉).filter (fun a : ℤ => Int.gcd a c = 1)

lemma mem_coprimeSet {c : ℕ} {u v : ℝ} {a : ℤ} :
    a ∈ coprimeSet c u v ↔ (u ≤ a ∧ (a : ℝ) < v) ∧ Int.gcd a c = 1 := by
  simp [coprimeSet, Int.ceil_le, Int.lt_ceil]

lemma card_coprimeSet_eq {c : ℕ} (hc : c ≠ 0) (u v : ℝ) :
    ((coprimeSet c u v).card : ℤ) = ∑ e ∈ c.divisors,
      (μ e : ℤ) * ((Finset.Ico ⌈u⌉ ⌈v⌉).filter (fun a : ℤ => (e : ℤ) ∣ a)).card := by
  rw [coprimeSet, Finset.card_filter]
  push_cast
  have key : ∀ a : ℤ, (if Int.gcd a c = 1 then (1 : ℤ) else 0) =
      ∑ e ∈ c.divisors, if (e : ℤ) ∣ a then (μ e : ℤ) else 0 := by
    intro a
    have hg : Int.gcd a c ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact hc (by exact_mod_cast h.2)
    rw [← Finset.sum_filter]
    have hset : c.divisors.filter (fun e : ℕ => (e : ℤ) ∣ a) = (Int.gcd a c).divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hec, -⟩, hea⟩
        refine ⟨?_, hg⟩
        exact Nat.dvd_gcd (Int.natCast_dvd.mp hea) hec
      · rintro ⟨he, -⟩
        refine ⟨⟨he.trans (Int.gcd_dvd_natAbs_right _ _), hc⟩, ?_⟩
        exact Int.natCast_dvd.mpr (he.trans (Int.gcd_dvd_natAbs_left _ _))
    rw [hset, sum_moebius_divisors]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma card_Ico_ceil_bound {u v : ℝ} (huv : u ≤ v) :
    |((Finset.Ico ⌈u⌉ ⌈v⌉).card : ℝ) - (v - u)| ≤ 1 := by
  have hle : ⌈u⌉ ≤ ⌈v⌉ := Int.ceil_mono huv
  have hc : ((Finset.Ico ⌈u⌉ ⌈v⌉).card : ℤ) = ⌈v⌉ - ⌈u⌉ := Int.card_Ico_of_le _ _ hle
  have hc' : ((Finset.Ico ⌈u⌉ ⌈v⌉).card : ℝ) = (⌈v⌉ : ℝ) - ⌈u⌉ := by exact_mod_cast hc
  rw [hc', abs_le]
  have h1 := Int.le_ceil u
  have h2 := Int.ceil_lt_add_one u
  have h3 := Int.le_ceil v
  have h4 := Int.ceil_lt_add_one v
  constructor <;> linarith

lemma card_multiples_eq {e : ℕ} (he : 0 < e) (u v : ℝ) :
    ((Finset.Ico ⌈u⌉ ⌈v⌉).filter (fun a : ℤ => (e : ℤ) ∣ a)).card =
      (Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  symm
  refine Finset.card_bij (fun b _ => (e : ℤ) * b) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil] at hb
    simp only [Finset.mem_filter, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · push_cast; rw [div_le_iff₀ he'] at hb; linarith [hb.1]
    · push_cast; rw [lt_div_iff₀ he'] at hb; linarith [hb.2]
  · intro b₁ _ b₂ _ h
    exact mul_left_cancel₀ (by exact_mod_cast he.ne') h
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil] at ha
    obtain ⟨⟨h1, h2⟩, b, rfl⟩ := ha
    refine ⟨b, ?_, rfl⟩
    simp only [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
    push_cast at h1 h2
    constructor
    · rw [div_le_iff₀ he']; linarith
    · rw [lt_div_iff₀ he']; linarith

/-- `ν(c) = ∑_{e ∣ c} μ(e)/e` (this is `φ(c)/c`, but we never need that). -/
noncomputable def nu (c : ℕ) : ℝ := ∑ e ∈ c.divisors, (μ e : ℝ) / e

/-- **Coprime count in an interval:** `|#{a ∈ [u,v) : (a,c)=1} − (v−u)ν(c)| ≤ d(c)`. -/
theorem coprimeCount_bound {c : ℕ} (hc : c ≠ 0) {u v : ℝ} (huv : u ≤ v) :
    |((coprimeSet c u v).card : ℝ) - (v - u) * nu c| ≤ (c.divisors.card : ℝ) := by
  have h := card_coprimeSet_eq hc u v
  have h' : ((coprimeSet c u v).card : ℝ) = ∑ e ∈ c.divisors,
      (μ e : ℝ) * ((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) := by
    have : ((coprimeSet c u v).card : ℝ) = (((coprimeSet c u v).card : ℤ) : ℝ) := by norm_cast
    rw [this, h]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    rw [card_multiples_eq (Nat.pos_of_mem_divisors he)]
  rw [h', nu, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ e ∈ c.divisors, ((μ e : ℝ) * ((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) -
          (v - u) * ((μ e : ℝ) / e))|
      ≤ ∑ e ∈ c.divisors, |(μ e : ℝ) * ((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) -
          (v - u) * ((μ e : ℝ) / e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ c.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he' : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
        have hb := card_Ico_ceil_bound (u := u / e) (v := v / e)
          (div_le_div_of_nonneg_right huv he'.le)
        have e1 : (μ e : ℝ) * ((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) -
            (v - u) * ((μ e : ℝ) / e) =
            (μ e : ℝ) * (((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) - (v / e - u / e)) := by
          field_simp
        rw [e1, abs_mul]
        have hμ : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        calc |(μ e : ℝ)| * |((Finset.Ico ⌈u / e⌉ ⌈v / e⌉).card : ℝ) - (v / e - u / e)|
            ≤ 1 * 1 := mul_le_mul hμ hb (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (c.divisors.card : ℝ) := by simp

/-! ### Divisor rearrangement -/

lemma sum_Ioc_antidiag {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / n), F n m := by
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, F x.1 x.2
  · refine sum_congr rfl fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  rw [Finset.sum_comm' (t' := Ioc 0 N ×ˢ Ioc 0 N |>.filter (fun x => x.1 * x.2 ≤ N))
    (s' := fun x => {x.1 * x.2})]
  · simp only [Finset.sum_singleton]
    rw [Finset.sum_filter, Finset.sum_product]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [mem_filter, mem_Ioc] at hn ⊢
    constructor
    · rintro ⟨⟨hm0, -⟩, h⟩
      exact ⟨hm0, (Nat.le_div_iff_mul_le hn.1).2 (by rw [mul_comm]; exact h)⟩
    · rintro ⟨hm0, hm⟩
      have h := (Nat.le_div_iff_mul_le hn.1).1 hm
      refine ⟨⟨hm0, ?_⟩, by rw [mul_comm]; exact h⟩
      exact le_trans (Nat.div_le_self _ _ |> le_trans hm) le_rfl
  · intro n x
    simp only [mem_filter, mem_product, mem_Ioc, mem_singleton]
    constructor
    · rintro ⟨hn, hx, he⟩
      exact ⟨he.symm, hx, he ▸ hn.2⟩
    · rintro ⟨rfl, hx, hle⟩
      exact ⟨⟨Nat.mul_pos hx.1.1 hx.2.1, hle⟩, hx, rfl⟩

/-! ### Harmonic error -/

lemma sum_inv_le_log (N : ℕ) : ∑ e ∈ Ioc 0 N, (1 : ℝ) / e ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Ioc 0 N = Icc 1 N := by ext; simp; omega
  rw [this]
  simpa [one_div] using h

lemma sum_antidiag_inv_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / n), (1 : ℝ) / ((n : ℝ) * m) ≤ (1 + Real.log N) ^ 2 := by
  calc ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / n), (1 : ℝ) / ((n : ℝ) * m)
      ≤ ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 N, (1 : ℝ) / ((n : ℝ) * m) := by
        refine Finset.sum_le_sum fun n _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro m; simp only [mem_Ioc]; intro h; exact ⟨h.1, h.2.trans (Nat.div_le_self _ _)⟩
    _ = (∑ e ∈ Ioc 0 N, (1 : ℝ) / e) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (1 + Real.log N) ^ 2 := by
        have h0 : 0 ≤ ∑ e ∈ Ioc 0 N, (1 : ℝ) / e := Finset.sum_nonneg fun _ _ => by positivity
        exact pow_le_pow_left₀ h0 (sum_inv_le_log N) 2

/-- `s (1 + log(1/s))² → 0` as `s → 0⁺`. -/
lemma tendsto_errorE :
    Tendsto (fun s : ℝ => s * (1 + Real.log (1 / s)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hsum : Tendsto (fun t : ℝ => (1 + Real.log t) ^ 2 / t) atTop (𝓝 0) := by
    have := (h0.add (h1.const_mul 2)).add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [one_mul, pow_zero, pow_one]
    field_simp
    ring
  have hinv : Tendsto (fun s : ℝ => 1 / s) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  refine (hsum.comp hinv).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) < s := hs
  simp only [Function.comp]
  field_simp

/-! ### The Riemann sum for `w(t) = √(1 − t²)` -/

/-- `w(t) = √(1 − t²)` (which is `0` for `t ≥ 1`). -/
noncomputable def wfun (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

lemma wfun_nonneg (t : ℝ) : 0 ≤ wfun t := Real.sqrt_nonneg _

lemma wfun_le_one {t : ℝ} : wfun t ≤ 1 := by
  unfold wfun
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg t]

lemma wfun_anti {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') : wfun t' ≤ wfun t := by
  unfold wfun
  apply Real.sqrt_le_sqrt
  nlinarith

lemma continuous_wfun : Continuous wfun := by unfold wfun; fun_prop

/-- `W = ∫₀¹ √(1 − t²) dt` (`= π/4`, never needed). -/
noncomputable def Wc : ℝ := ∫ t in (0 : ℝ)..1, wfun t

/-- `S(h) = ∑_{1 ≤ m ≤ ⌊1/h⌋} h·w(mh)`. -/
noncomputable def riemannS (h : ℝ) : ℝ := ∑ m ∈ Ioc 0 ⌊1 / h⌋₊, h * wfun (m * h)

lemma riemannS_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ riemannS h :=
  Finset.sum_nonneg fun _ _ => mul_nonneg hh (wfun_nonneg _)

lemma riemannS_le_one {h : ℝ} (hh : 0 ≤ h) : riemannS h ≤ 1 := by
  unfold riemannS
  calc ∑ m ∈ Ioc 0 ⌊1 / h⌋₊, h * wfun (m * h) ≤ ∑ _m ∈ Ioc 0 ⌊1 / h⌋₊, h := by
        refine Finset.sum_le_sum fun m _ => ?_
        calc h * wfun (m * h) ≤ h * 1 := mul_le_mul_of_nonneg_left wfun_le_one hh
          _ = h := mul_one h
    _ = ⌊1 / h⌋₊ * h := by simp
    _ ≤ 1 := by
        rcases hh.eq_or_lt with rfl | hpos
        · simp
        have := Nat.floor_le (show 0 ≤ 1 / h by positivity)
        calc (⌊1 / h⌋₊ : ℝ) * h ≤ 1 / h * h := mul_le_mul_of_nonneg_right this hpos.le
          _ = 1 := by field_simp

lemma riemannS_of_gt_one {h : ℝ} (hh : 1 < h) : riemannS h = 0 := by
  unfold riemannS
  have : ⌊1 / h⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]
    rw [div_lt_one (by linarith)]; exact hh
  rw [this]; simp

lemma wfun_ii (a b : ℝ) : IntervalIntegrable wfun MeasureTheory.volume a b :=
  continuous_wfun.intervalIntegrable a b

lemma const_ii (k a b : ℝ) : IntervalIntegrable (fun _ : ℝ => k) MeasureTheory.volume a b :=
  intervalIntegrable_const

lemma step_upper {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    ∫ t in u..u + h, wfun t ≤ h * wfun u := by
  have := intervalIntegral.integral_mono_on (a := u) (b := u + h) (f := wfun)
    (g := fun _ => wfun u) (by linarith) (wfun_ii _ _)
    (const_ii _ _ _) (fun t ht => wfun_anti hu ht.1)
  simpa using this

lemma step_lower {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    h * wfun (u + h) ≤ ∫ t in u..u + h, wfun t := by
  have := intervalIntegral.integral_mono_on (a := u) (b := u + h) (g := wfun)
    (f := fun _ => wfun (u + h)) (by linarith) (const_ii _ _ _)
    (wfun_ii _ _) (fun t ht => wfun_anti (hu.trans ht.1) ht.2)
  simpa using this

lemma sum_adjacent (h : ℝ) (k M : ℕ) :
    ∑ m ∈ range M, ∫ t in ((m + k : ℕ) : ℝ) * h..((m + k + 1 : ℕ) : ℝ) * h, wfun t =
      ∫ t in (k : ℝ) * h..((M + k : ℕ) : ℝ) * h, wfun t := by
  have := intervalIntegral.sum_integral_adjacent_intervals (a := fun m : ℕ => ((m + k : ℕ) : ℝ) * h)
    (n := M) (f := wfun) (fun m _ => wfun_ii _ _)
  simpa [add_assoc, add_comm 1 k] using this

lemma sum_Ioc_eq_range (f : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Ioc 0 M, f m = ∑ m ∈ range M, f (m + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, Finset.sum_range_succ]

lemma riemannS_eq_range {h : ℝ} :
    riemannS h = ∑ m ∈ range ⌊1 / h⌋₊, h * wfun (((m + 1 : ℕ) : ℝ) * h) := by
  unfold riemannS
  exact sum_Ioc_eq_range (fun m => h * wfun ((m : ℝ) * h)) _

lemma integral_wfun_nonneg {a b : ℝ} (hab : a ≤ b) : 0 ≤ ∫ t in a..b, wfun t :=
  intervalIntegral.integral_nonneg hab fun t _ => wfun_nonneg t

/-- **Riemann sum:** `|S(h) − W| ≤ h` for `0 < h ≤ 1`. -/
theorem abs_riemannS_sub_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) : |riemannS h - Wc| ≤ h := by
  set M := ⌊1 / h⌋₊ with hM
  have hMle : (M : ℝ) * h ≤ 1 := by
    have := Nat.floor_le (show 0 ≤ 1 / h by positivity)
    calc (M : ℝ) * h ≤ 1 / h * h := mul_le_mul_of_nonneg_right this hh.le
      _ = 1 := by field_simp
  have hMgt : 1 < ((M : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (1 / h)
    calc (1 : ℝ) = 1 / h * h := by field_simp
      _ < ((M : ℝ) + 1) * h := mul_lt_mul_of_pos_right this hh
  have hI := wfun_ii
  -- upper bound: S ≤ ∫₀^{Mh} w ≤ W
  have hup : riemannS h ≤ Wc := by
    rw [riemannS_eq_range]
    calc ∑ m ∈ range M, h * wfun (((m + 1 : ℕ) : ℝ) * h)
        ≤ ∑ m ∈ range M, ∫ t in ((m + 0 : ℕ) : ℝ) * h..((m + 0 + 1 : ℕ) : ℝ) * h, wfun t := by
          refine Finset.sum_le_sum fun m _ => ?_
          have := step_lower (u := (m : ℝ) * h) (h := h) (by positivity) hh.le
          convert this using 2 <;> push_cast <;> ring
      _ = ∫ t in ((0 : ℕ) : ℝ) * h..((M + 0 : ℕ) : ℝ) * h, wfun t := sum_adjacent h 0 M
      _ ≤ Wc := by
          simp only [Nat.cast_zero, zero_mul, add_zero]
          rw [Wc, ← intervalIntegral.integral_add_adjacent_intervals (hI 0 (M * h)) (hI _ 1)]
          linarith [integral_wfun_nonneg hMle]
  -- lower bound: S ≥ ∫_h^{(M+1)h} w ≥ W − h
  have hlow : Wc - h ≤ riemannS h := by
    rw [riemannS_eq_range]
    have h1 : ∫ t in ((1 : ℕ) : ℝ) * h..((M + 1 : ℕ) : ℝ) * h, wfun t ≤
        ∑ m ∈ range M, h * wfun (((m + 1 : ℕ) : ℝ) * h) := by
      rw [← sum_adjacent h 1 M]
      refine Finset.sum_le_sum fun m _ => ?_
      have := step_upper (u := ((m + 1 : ℕ) : ℝ) * h) (h := h) (by positivity) hh.le
      convert this using 2 <;> push_cast <;> ring
    have h2 : Wc - h ≤ ∫ t in ((1 : ℕ) : ℝ) * h..((M + 1 : ℕ) : ℝ) * h, wfun t := by
      simp only [Nat.cast_one, one_mul, Nat.cast_add]
      have e1 : Wc = (∫ t in (0 : ℝ)..h, wfun t) + ∫ t in h..1, wfun t :=
        (intervalIntegral.integral_add_adjacent_intervals (hI 0 h) (hI h 1)).symm
      have e2 : (∫ t in h..((M : ℝ) + 1) * h, wfun t) =
          (∫ t in h..1, wfun t) + ∫ t in (1 : ℝ)..((M : ℝ) + 1) * h, wfun t :=
        (intervalIntegral.integral_add_adjacent_intervals (hI h 1) (hI 1 _)).symm
      have e3 : (∫ t in (0 : ℝ)..h, wfun t) ≤ h := by
        have := step_upper (u := 0) (h := h) le_rfl hh.le
        simp only [zero_add] at this
        calc (∫ t in (0 : ℝ)..h, wfun t) ≤ h * wfun 0 := this
          _ ≤ h * 1 := mul_le_mul_of_nonneg_left wfun_le_one hh.le
          _ = h := mul_one h
      rw [e2, e1]
      linarith [integral_wfun_nonneg hMgt.le]
    linarith
  rw [abs_le]; constructor <;> linarith

/-! ### The main-term limit by dominated convergence -/

/-- `κ = ∑ μ(e)/e²` (`= 6/π²`, never needed). -/
noncomputable def kappa : ℝ := ∑' e : ℕ, (μ e : ℝ) / (e : ℝ) ^ 2

/-- `T(s) = ∑ₑ μ(e)/e² · S(se)`. -/
noncomputable def mainT (s : ℝ) : ℝ := ∑' e : ℕ, (μ e : ℝ) / (e : ℝ) ^ 2 * riemannS (s * e)

theorem tendsto_mainT : Tendsto mainT (𝓝[>] 0) (𝓝 (kappa * Wc)) := by
  unfold mainT kappa
  rw [← tsum_mul_right]
  refine tendsto_tsum_of_dominated_convergence (bound := fun e : ℕ => 1 / (e : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) (fun e => ?_) ?_
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    refine Tendsto.const_mul _ ?_
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨min (ε / e) (1 / e), by positivity, fun s hs hds => ?_⟩
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hds
    have hse : s * e < ε := by
      have := (lt_min_iff.1 hds).1; rw [lt_div_iff₀ he'] at this; exact this
    have hse1 : s * e ≤ 1 := by
      have := (lt_min_iff.1 hds).2; rw [lt_div_iff₀ he'] at this; linarith
    rw [Real.dist_eq]
    exact (abs_riemannS_sub_le (by positivity) hse1).trans_lt hse
  · filter_upwards [self_mem_nhdsWithin] with s hs e
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    rw [norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (riemannS_nonneg (by positivity)), abs_of_nonneg (by positivity : (0:ℝ) ≤ (e:ℝ)^2)]
    have hμ : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hS := riemannS_le_one (h := s * e) (by positivity)
    calc |(μ e : ℝ)| / (e : ℝ) ^ 2 * riemannS (s * e) ≤ 1 / (e : ℝ) ^ 2 * 1 := by
          apply mul_le_mul _ hS (riemannS_nonneg (by positivity)) (by positivity)
          exact div_le_div_of_nonneg_right hμ (by positivity)
      _ = 1 / (e : ℝ) ^ 2 := mul_one _

end RamanujanTau.EisensteinReal.Horo

#print axioms RamanujanTau.EisensteinReal.Horo.coprimeCount_bound
#print axioms RamanujanTau.EisensteinReal.Horo.sum_Ioc_antidiag
#print axioms RamanujanTau.EisensteinReal.Horo.abs_riemannS_sub_le
#print axioms RamanujanTau.EisensteinReal.Horo.tendsto_mainT
#print axioms RamanujanTau.EisensteinReal.Horo.tendsto_errorE
