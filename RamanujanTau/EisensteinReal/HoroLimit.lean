/-
# The horocycle limit of a rectangle count

`tendsto_horoR`: for `α ≤ β`, `A > 0`,

    ∫₀¹ #{γ ∈ SL₂(ℤ) : γ(x+iy) ∈ [α,β) × [A,∞)} dx  →  K₀ (β − α)/A      (y → 0⁺),

with `K₀ = 4κW` (`κ = ∑ μ(e)/e² = 6/π²`, `W = ∫₀¹ √(1−t²) dt = π/4`, so `K₀ = 6/π`; the values
are never needed). Error term `O(√y log²(1/y))`.
-/
import RamanujanTau.EisensteinReal.HoroCount
import Mathlib.Algebra.Order.Floor.Semifield

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology MeasureTheory ArithmeticFunction
open RamanujanTau.RankinSelberg
open scoped ENNReal ArithmeticFunction.Moebius

/-- `λ_c(y) = 2√(y/(Ac²) − y²)`. -/
noncomputable def lam (A y : ℝ) (c : ℕ) : ℝ := 2 * Real.sqrt (y / (A * (c : ℝ) ^ 2) - y ^ 2)

lemma lam_nonneg (A y : ℝ) (c : ℕ) : 0 ≤ lam A y c := by unfold lam; positivity

lemma sum_Ioc_eq_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Ioc 0 N, f m = ∑ m ∈ range N, f (m + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, Finset.sum_range_succ]

section
variable {A y s : ℝ} (hA : 0 < A) (hy : 0 < y) (hs : s = Real.sqrt (A * y))
include hA hy hs

lemma s_pos : 0 < s := by rw [hs]; positivity

lemma s_sq : s ^ 2 = A * y := by rw [hs, Real.sq_sqrt (by positivity)]

lemma lam_eq_zero_of_gt {c : ℕ} (hc : ⌊1 / s⌋₊ < c) : lam A y c = 0 := by
  have hs0 := s_pos hA hy hs
  have h1 : 1 / s < c := (Nat.floor_lt (by positivity)).1 hc
  have h2 : 1 < c * s := by rw [div_lt_iff₀ hs0] at h1; linarith
  have h3 : 1 < (c : ℝ) ^ 2 * (A * y) := by
    rw [← s_sq hA hy hs]; nlinarith
  unfold lam
  rw [Real.sqrt_eq_zero'.mpr, mul_zero]
  have hc0 : (0 : ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; norm_num at h3
    · exact_mod_cast h
  rw [sub_nonpos, div_le_iff₀ (by positivity)]
  nlinarith

lemma lam_le {c : ℕ} (hc : 0 < c) : lam A y c ≤ 2 * s / (A * c) := by
  have hs0 := s_pos hA hy hs
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  unfold lam
  have e : y / (A * (c : ℝ) ^ 2) = (s / (A * c)) ^ 2 := by
    rw [div_pow, s_sq hA hy hs]; field_simp
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc Real.sqrt (y / (A * (c : ℝ) ^ 2) - y ^ 2) ≤ Real.sqrt (y / (A * (c : ℝ) ^ 2)) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = s / (A * c) := by rw [e, Real.sqrt_sq (by positivity)]

lemma m_lam_eq {e m : ℕ} (he : 0 < e) (hm : 0 < m) :
    (m : ℝ) * lam A y (e * m) = 2 / (A * (e : ℝ) ^ 2) * ((s * e) * wfun (m * (s * e))) := by
  have hs0 := s_pos hA hy hs
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy' : y = s ^ 2 / A := by rw [s_sq hA hy hs]; field_simp
  have key : y / (A * ((e * m : ℕ) : ℝ) ^ 2) - y ^ 2 =
      (s / (A * e * m)) ^ 2 * (1 - ((m : ℝ) * (s * e)) ^ 2) := by
    rw [hy']; push_cast; field_simp
  unfold lam wfun
  rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

end

/-- `c ν(c) = ∑_{em = c} μ(e) m`. -/
lemma mul_nu_eq (c : ℕ) :
    (c : ℝ) * nu c = ∑ x ∈ c.divisorsAntidiagonal, (μ x.1 : ℝ) * x.2 := by
  rw [Nat.sum_divisorsAntidiagonal (fun e m => (μ e : ℝ) * m), nu, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdvd := Nat.dvd_of_mem_divisors he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
  rw [Nat.cast_div hdvd he0]
  ring

/-- `d(c)/c = ∑_{em = c} 1/(em)`. -/
lemma card_div_eq {c : ℕ} (hc : 0 < c) :
    (c.divisors.card : ℝ) / c = ∑ x ∈ c.divisorsAntidiagonal, (1 : ℝ) / ((x.1 : ℝ) * x.2) := by
  rw [Nat.sum_divisorsAntidiagonal (fun e m => (1 : ℝ) / ((e : ℝ) * m))]
  have : ∀ e ∈ c.divisors, (1 : ℝ) / ((e : ℝ) * ((c / e : ℕ) : ℝ)) = 1 / c := by
    intro e he
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  ring

section
variable {A y s : ℝ} (hA : 0 < A) (hy : 0 < y) (hs : s = Real.sqrt (A * y))
include hA hy hs

/-- **Main term:** `∑_{c ≤ C} cν(c)λ_c = (2/A) T(s)`. -/
theorem sum_main_eq :
    ∑ c ∈ Ioc 0 ⌊1 / s⌋₊, (c : ℝ) * nu c * lam A y c = 2 / A * mainT s := by
  have hs0 := s_pos hA hy hs
  set C := ⌊1 / s⌋₊ with hC
  have h1 : ∀ c ∈ Ioc 0 C, (c : ℝ) * nu c * lam A y c =
      ∑ x ∈ c.divisorsAntidiagonal, (μ x.1 : ℝ) * x.2 * lam A y (x.1 * x.2) := by
    intro c hc
    rw [mul_nu_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.1 hx).1]
  rw [Finset.sum_congr rfl h1,
    sum_Ioc_antidiag (fun e m => (μ e : ℝ) * m * lam A y (e * m)) C]
  have h2 : ∀ e ∈ Ioc 0 C, ∑ m ∈ Ioc 0 (C / e), (μ e : ℝ) * m * lam A y (e * m) =
      2 / A * ((μ e : ℝ) / (e : ℝ) ^ 2 * riemannS (s * e)) := by
    intro e he
    have he0 : 0 < e := (Finset.mem_Ioc.1 he).1
    have he' : (0 : ℝ) < e := by exact_mod_cast he0
    have hCe : C / e = ⌊1 / (s * e)⌋₊ := by
      rw [hC, ← Nat.floor_div_natCast, div_div]
    rw [hCe, riemannS, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
    rw [mul_assoc, m_lam_eq hA hy hs he0 hm0]
    field_simp
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, mainT]
  congr 1
  symm
  refine tsum_eq_sum fun e he => ?_
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · simp
  · have hgt : C < e := by
      by_contra h
      exact he (Finset.mem_Ioc.2 ⟨he0, not_lt.1 h⟩)
    have h1s : 1 / s < e := (Nat.floor_lt (by positivity)).1 hgt
    have : 1 < s * e := by rw [div_lt_iff₀ hs0] at h1s; linarith
    rw [riemannS_of_gt_one this, mul_zero]

/-- **Error term:** `∑_{c ≤ C} d(c)λ_c ≤ (2s/A)(1 + log(1/s))²` for `s ≤ 1`. -/
theorem sum_error_le (hs1 : s ≤ 1) :
    ∑ c ∈ Ioc 0 ⌊1 / s⌋₊, (c.divisors.card : ℝ) * lam A y c ≤
      2 * s / A * (1 + Real.log (1 / s)) ^ 2 := by
  have hs0 := s_pos hA hy hs
  set C := ⌊1 / s⌋₊ with hC
  calc ∑ c ∈ Ioc 0 C, (c.divisors.card : ℝ) * lam A y c
      ≤ ∑ c ∈ Ioc 0 C, 2 * s / A * ((c.divisors.card : ℝ) / c) := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hc0 : 0 < c := (Finset.mem_Ioc.1 hc).1
        have hc' : (0 : ℝ) < c := by exact_mod_cast hc0
        calc (c.divisors.card : ℝ) * lam A y c ≤ (c.divisors.card : ℝ) * (2 * s / (A * c)) :=
              mul_le_mul_of_nonneg_left (lam_le hA hy hs hc0) (by positivity)
          _ = 2 * s / A * ((c.divisors.card : ℝ) / c) := by field_simp
    _ = 2 * s / A * ∑ c ∈ Ioc 0 C, ∑ x ∈ c.divisorsAntidiagonal, (1 : ℝ) / ((x.1 : ℝ) * x.2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [card_div_eq (Finset.mem_Ioc.1 hc).1]
    _ = 2 * s / A * ∑ n ∈ Ioc 0 C, ∑ m ∈ Ioc 0 (C / n), (1 : ℝ) / ((n : ℝ) * m) := by
        rw [sum_Ioc_antidiag (fun e m => (1 : ℝ) / ((e : ℝ) * m)) C]
    _ ≤ 2 * s / A * (1 + Real.log C) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_antidiag_inv_le C) (by positivity)
    _ ≤ 2 * s / A * (1 + Real.log (1 / s)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hC1 : 1 ≤ C := by
          rw [hC, Nat.one_le_floor_iff]; rw [le_div_iff₀ hs0]; linarith
        have hCpos : (0 : ℝ) < C := by exact_mod_cast hC1
        have hlogC : 0 ≤ Real.log C := Real.log_nonneg (by exact_mod_cast hC1)
        have hle : Real.log C ≤ Real.log (1 / s) :=
          Real.log_le_log hCpos (Nat.floor_le (by positivity))
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2

end

/-! ### Assembly -/

lemma Gc_ne_top {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) {c : ℕ} (hc : 0 < c) :
    Gc α β A y (c : ℤ) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (Gc_le hαβ hA hy hc)

lemma Gc_toReal_bound {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) {c : ℕ}
    (hc : 0 < c) :
    |(Gc α β A y (c : ℤ)).toReal - (c : ℝ) * (β - α) * nu c * lam A y c| ≤
      (c.divisors.card : ℝ) * lam A y c := by
  have hne := Gc_ne_top hαβ hA hy hc
  have hlam := lam_nonneg A y c
  -- `c(β−α)ν(c) + d(c) ≥ 0`
  have hLD : 0 ≤ (c : ℝ) * (β - α) * nu c + c.divisors.card := by
    have hb := coprimeCount_bound (c := c) hc.ne' (u := 0) (v := c * (β - α))
      (by have : (0 : ℝ) ≤ c := by positivity
          nlinarith)
    rw [sub_zero] at hb
    have h0 : (0 : ℝ) ≤ ((coprimeSet c 0 (c * (β - α))).card : ℝ) := by positivity
    linarith [(abs_le.1 hb).2]
  have hup := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (Gc_le hαβ hA hy hc)
  have hlo := ENNReal.toReal_mono hne (Gc_ge hαβ hA hy hc)
  rw [← ENNReal.ofReal_mul hLD, ENNReal.toReal_ofReal (mul_nonneg hLD (by positivity))] at hup
  rw [← ENNReal.ofReal_mul' (by positivity), ENNReal.toReal_ofReal'] at hlo
  have hlo' : ((c : ℝ) * (β - α) * nu c - c.divisors.card) * lam A y c ≤
      (Gc α β A y (c : ℤ)).toReal := le_trans (le_max_left _ _) hlo
  rw [abs_le]
  unfold lam at *
  constructor <;> nlinarith

/-- The horocycle mean, as a real function of `y` (junk value `0` for `y ≤ 0`). -/
noncomputable def horoR (α β A : ℝ) (y : ℝ) : ℝ :=
  if hy : 0 < y then (horo α β A hy).toReal else 0

theorem horo_ne_top {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) (hyA : y < A) :
    horo α β A hy ≠ ⊤ := by
  rw [horo_eq_two hy hyA]
  refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_
  set s := Real.sqrt (A * y) with hs
  rw [tsum_eq_sum (s := range ⌊1 / s⌋₊)]
  · refine (ENNReal.sum_lt_top.2 fun n _ => ?_).ne
    have := Gc_ne_top (c := n + 1) hαβ hA hy (Nat.succ_pos n)
    push_cast at this
    exact this.lt_top
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hc : ⌊1 / s⌋₊ < n + 1 := by omega
    refine le_antisymm ?_ (by simp)
    have h := Gc_le (c := n + 1) hαβ hA hy (Nat.succ_pos n) (α := α) (β := β)
    push_cast at h
    refine h.trans (le_of_eq ?_)
    have hz := lam_eq_zero_of_gt hA hy hs hc
    unfold lam at hz
    push_cast at hz
    rw [hz, ENNReal.ofReal_zero, mul_zero]

/-- **Explicit bound:** for `0 < y < A` with `Ay ≤ 1`, `s = √(Ay)`:
`|horo − 4(β−α)T(s)/A| ≤ (4s/A)(1 + log(1/s))²`. -/
theorem horo_bound {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) (hyA : y < A)
    (hAy : A * y ≤ 1) :
    |(horo α β A hy).toReal - 4 * (β - α) / A * mainT (Real.sqrt (A * y))| ≤
      4 * Real.sqrt (A * y) / A * (1 + Real.log (1 / Real.sqrt (A * y))) ^ 2 := by
  set s := Real.sqrt (A * y) with hs
  have hs1 : s ≤ 1 := by rw [hs, Real.sqrt_le_one]; exact hAy
  set C := ⌊1 / s⌋₊ with hC
  -- `horo = 2 ∑_{c ≤ C} G(c)`
  have hsum : ∑' n : ℕ, Gc α β A y ((n : ℤ) + 1) = ∑ c ∈ Ioc 0 C, Gc α β A y (c : ℤ) := by
    rw [sum_Ioc_eq_range' (fun c : ℕ => Gc α β A y (c : ℤ)) C]
    rw [tsum_eq_sum (s := range C)]
    · push_cast; rfl
    · intro n hn
      rw [Finset.mem_range, not_lt] at hn
      have hc : C < n + 1 := by omega
      refine le_antisymm ?_ (by simp)
      have h := Gc_le (c := n + 1) hαβ hA hy (Nat.succ_pos n) (α := α) (β := β)
      push_cast at h
      refine h.trans (le_of_eq ?_)
      have hz := lam_eq_zero_of_gt hA hy hs hc
      unfold lam at hz
      push_cast at hz
      rw [hz, ENNReal.ofReal_zero, mul_zero]
  have hreal : (horo α β A hy).toReal = 2 * ∑ c ∈ Ioc 0 C, (Gc α β A y (c : ℤ)).toReal := by
    rw [horo_eq_two hy hyA, hsum, ENNReal.toReal_mul, ENNReal.toReal_sum]
    · simp
    · intro c hc
      exact Gc_ne_top hαβ hA hy (Finset.mem_Ioc.1 hc).1
  have hmain := sum_main_eq hA hy hs
  have herr := sum_error_le hA hy hs hs1
  have hdiff : |∑ c ∈ Ioc 0 C, (Gc α β A y (c : ℤ)).toReal -
      ∑ c ∈ Ioc 0 C, (c : ℝ) * (β - α) * nu c * lam A y c| ≤
      ∑ c ∈ Ioc 0 C, (c.divisors.card : ℝ) * lam A y c := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c hc => ?_)
    exact Gc_toReal_bound hαβ hA hy (Finset.mem_Ioc.1 hc).1
  have hmain' : ∑ c ∈ Ioc 0 C, (c : ℝ) * (β - α) * nu c * lam A y c =
      (β - α) * (2 / A * mainT s) := by
    rw [← hmain, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hmain'] at hdiff
  rw [hreal]
  have e : 2 * ∑ c ∈ Ioc 0 C, (Gc α β A y (c : ℤ)).toReal - 4 * (β - α) / A * mainT s =
      2 * (∑ c ∈ Ioc 0 C, (Gc α β A y (c : ℤ)).toReal - (β - α) * (2 / A * mainT s)) := by ring
  rw [e, abs_mul, abs_two]
  calc 2 * |∑ c ∈ Ioc 0 C, (Gc α β A y (c : ℤ)).toReal - (β - α) * (2 / A * mainT s)|
      ≤ 2 * (2 * s / A * (1 + Real.log (1 / s)) ^ 2) := by
        linarith [hdiff.trans herr]
    _ = 4 * s / A * (1 + Real.log (1 / s)) ^ 2 := by ring

/-- `√(A y) → 0⁺` as `y → 0⁺`. -/
lemma tendsto_sqrt_mul {A : ℝ} (hA : 0 < A) :
    Tendsto (fun y : ℝ => Real.sqrt (A * y)) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Tendsto (fun y : ℝ => Real.sqrt (A * y)) (𝓝 0) (𝓝 (Real.sqrt (A * 0))) :=
      ((continuous_const.mul continuous_id).sqrt).tendsto 0
    rw [mul_zero, Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Real.sqrt_pos.2 (mul_pos hA hy)

/-- **Horocycle limit for a rectangle count (axiom-clean).** For `α ≤ β`, `A > 0`:
`∫₀¹ #{γ ∈ SL₂(ℤ) : γ(x+iy) ∈ [α,β)×[A,∞)} dx → 4κW(β−α)/A` as `y → 0⁺`. -/
theorem tendsto_horoR {α β A : ℝ} (hαβ : α ≤ β) (hA : 0 < A) :
    Tendsto (horoR α β A) (𝓝[>] 0) (𝓝 (4 * (β - α) / A * (kappa * Wc))) := by
  have hT : Tendsto (fun y => 4 * (β - α) / A * mainT (Real.sqrt (A * y))) (𝓝[>] 0)
      (𝓝 (4 * (β - α) / A * (kappa * Wc))) :=
    (tendsto_mainT.comp (tendsto_sqrt_mul hA)).const_mul _
  have hE : Tendsto (fun y => 4 / A * (Real.sqrt (A * y) *
      (1 + Real.log (1 / Real.sqrt (A * y))) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_errorE.comp (tendsto_sqrt_mul hA)).const_mul (4 / A)
    simpa using this
  have hdiff : Tendsto (fun y => horoR α β A y - 4 * (β - α) / A * mainT (Real.sqrt (A * y)))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hE
    have hpos : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < min A (1 / A) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hpos] with y hy hyA
    have hy0 : (0 : ℝ) < y := hy
    have hyA1 : y < A := lt_of_lt_of_le hyA (min_le_left _ _)
    have hAy : A * y ≤ 1 := by
      have := lt_of_lt_of_le hyA (min_le_right _ _)
      rw [lt_div_iff₀ hA] at this; nlinarith
    rw [Real.norm_eq_abs]
    unfold horoR
    rw [dif_pos hy0]
    have := horo_bound hαβ hA hy0 hyA1 hAy
    calc _ ≤ 4 * Real.sqrt (A * y) / A * (1 + Real.log (1 / Real.sqrt (A * y))) ^ 2 := this
      _ = 4 / A * (Real.sqrt (A * y) * (1 + Real.log (1 / Real.sqrt (A * y))) ^ 2) := by ring
  have := hdiff.add hT
  simpa using this

end RamanujanTau.EisensteinReal.Horo

#print axioms RamanujanTau.EisensteinReal.Horo.horo_bound
#print axioms RamanujanTau.EisensteinReal.Horo.tendsto_horoR
