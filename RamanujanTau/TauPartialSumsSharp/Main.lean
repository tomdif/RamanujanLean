/-
# `TauPartialSumsSharp/`: `∑_{n≤x} τ(n) ≪ x^{59/10+ε}` (unconditional)

Build: `nice -n 10 lake build RamanujanTau.TauPartialSumsSharp.Main`.
See `docs/TAU_PARTIAL_SUMS_SHARP.md`.

Headlines (unconditional, axiom-clean):

* `cuspForm_partial_sum_sharp`: for every level-one cusp form `f` of weight `k` and every
  `ε > 0`, `‖∑_{n≤x} a_f(n)‖ ≤ C x^{(k−1)/2 + 2/5 + ε}`;
* `tau_partial_sum_sharp`: `|∑_{n≤x} τ(n)| ≤ C x^{59/10 + ε}`  (`59/10 = 11/2 + 2/5`),

improving `TauPartialSums.tau_partial_sum_bound` (`181/30 = 11/2 + 8/15`).

Route (Landau 1915 / Chandrasekharan–Narasimhan, degree two): exact dual expansion of the Riesz
mean of order `r` (`Dual`), the sharp bottom kernel `J_0 ≪ y^{k/2−1/4}` by a bent contour
(`Contour`), the phase-free top kernel `J_r ≪ y^{(k+r)/2+eta}`, `r`-th differences of the dual
expansion down to `J_0` (`Core`), and short sums of `|a_f(n)|` by Cauchy–Schwarz and Rankin's
`O(N^{3/5})` (`RankinExact`). Parameters: `h = x^{1/5}`, `M = x^{3/5+ε}`, `r = ⌈1/ε⌉ + 2`.
-/
import RamanujanTau.TauPartialSumsSharp.Core
import RamanujanTau.TauPartialSumsSharp.Contour
import RamanujanTau.RankinExact.Main

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real Finset ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.RankinSelbergGeneral
open scoped MatrixGroups

/-! ### Short sums -/

/-- `∑_{x<n≤x+rh} ‖aₙ‖ ≤ √Q h^{1/2} x^{β/2+3/10}` for `1 ≤ h ≤ x^{3/5}`. -/
lemma short_bound (a : ℕ → ℂ) (β : ℕ) {c C : ℝ}
    (hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ β - c * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5))
    (r : ℕ) : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x : ℝ, 1 ≤ x → ∀ h : ℝ, 1 ≤ h → h ≤ x ^ ((3 : ℝ) / 5) →
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + r * h⌋₊, ‖a n‖ ≤
        Real.sqrt Q * (h ^ ((1 : ℝ) / 2) * x ^ ((β : ℝ) / 2 + 3 / 10)) := by
  have hC0 : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hT 1 le_rfl)
    simpa using h1
  set R : ℝ := (r : ℝ) + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  set Q : ℝ := R ^ (β + 2) * (|c| + 2 * C) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨Q, hQ0, fun x hx h hh1 hh => ?_⟩
  have hx0 : 0 < x := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hx35 : x ^ ((3 : ℝ) / 5) ≤ x := by
    calc x ^ ((3 : ℝ) / 5) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have hhx : h ≤ x := hh.trans hx35
  set N : ℕ := ⌊x⌋₊ with hN
  set M : ℕ := ⌊x + r * h⌋₊ with hM
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hNM : N ≤ M := Nat.floor_le_floor (by nlinarith)
  have hMle : (M : ℝ) ≤ x + r * h := Nat.floor_le (by nlinarith)
  have hNgt : x - 1 < (N : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have hMN : (M : ℝ) - N ≤ R * h := by rw [hR]; nlinarith
  have hMN0 : (0 : ℝ) ≤ (M : ℝ) - N := by
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    linarith
  have hMR : (M : ℝ) ≤ R * x := by rw [hR]; nlinarith
  set S : ℝ := ∑ n ∈ Finset.Ioc N M, ‖a n‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSq := TauPartialSums.short_sq a β hT hN1 hNM
  have hMb : (M : ℝ) ^ β ≤ R ^ β * x ^ β := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMR β
  have hM35 : (M : ℝ) ^ ((3 : ℝ) / 5) ≤ R * x ^ ((3 : ℝ) / 5) := by
    calc (M : ℝ) ^ ((3 : ℝ) / 5) ≤ (R * x) ^ ((3 : ℝ) / 5) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hMR (by norm_num)
      _ = R ^ ((3 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) := Real.mul_rpow (by linarith) hx0.le
      _ ≤ R * x ^ ((3 : ℝ) / 5) := by
          gcongr
          calc R ^ ((3 : ℝ) / 5) ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
            _ = R := Real.rpow_one R
  have hx35p : 0 ≤ x ^ ((3 : ℝ) / 5) := by positivity
  have hinner : |c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) ≤
      R * (|c| + 2 * C) * x ^ ((3 : ℝ) / 5) := by
    have h1 : |c| * ((M : ℝ) - N) ≤ |c| * (R * x ^ ((3 : ℝ) / 5)) :=
      mul_le_mul_of_nonneg_left (hMN.trans (by gcongr)) (abs_nonneg c)
    have h2 : 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 * C * (R * x ^ ((3 : ℝ) / 5)) :=
      mul_le_mul_of_nonneg_left hM35 (by positivity)
    nlinarith
  have hS2 : S ^ 2 ≤ Q * (h * (x ^ β * x ^ ((3 : ℝ) / 5))) := by
    calc S ^ 2 ≤ ((M : ℝ) - N) * ((M : ℝ) ^ β *
          (|c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5))) := hSq
      _ ≤ (R * h) * ((R ^ β * x ^ β) * (R * (|c| + 2 * C) * x ^ ((3 : ℝ) / 5))) := by
          have hin0 : 0 ≤ |c| * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) := by
            positivity
          gcongr
      _ = Q * (h * (x ^ β * x ^ ((3 : ℝ) / 5))) := by rw [hQ, pow_add]; ring
  have hr : Real.sqrt (h * (x ^ β * x ^ ((3 : ℝ) / 5))) =
      h ^ ((1 : ℝ) / 2) * x ^ ((β : ℝ) / 2 + 3 / 10) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (by linarith) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 2; ring
  calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS0).symm
    _ ≤ Real.sqrt (Q * (h * (x ^ β * x ^ ((3 : ℝ) / 5)))) := Real.sqrt_le_sqrt hS2
    _ = Real.sqrt Q * (h ^ ((1 : ℝ) / 2) * x ^ ((β : ℝ) / 2 + 3 / 10)) := by
        rw [Real.sqrt_mul hQ0, hr]

/-! ### The exponent bookkeeping -/

lemma exps_ok {k : ℝ} {ε r : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hr : 1 ≤ ε * (r - 1)) :
    (k / 2 - 1 / 4) + (3 / 5 + ε) * (1 / 4 + ε / 8) ≤ (k - 1) / 2 + 2 / 5 + ε ∧
    -(r / 5) + ((k - r) / 2 + ε / 8 + r) + (3 / 5 + ε) * ((1 - r) / 2 + ε / 8 + ε / 8) ≤
      (k - 1) / 2 + 2 / 5 + ε := by
  constructor
  · nlinarith
  · nlinarith

lemma alg (c a b q X : ℝ) : c * (a * X + b * X) + q * X = (c * (a + b) + q) * X := by ring

lemma exp3 {k : ℕ} (hk1 : 1 ≤ k) {ε : ℝ} (hε0 : 0 < ε) :
    (1 : ℝ) / 5 * (1 / 2) + (((k - 1 : ℕ) : ℝ) / 2 + 3 / 10) ≤ ((k : ℝ) - 1) / 2 + 2 / 5 + ε := by
  rw [Nat.cast_sub hk1, Nat.cast_one]; linarith

variable {k : ℕ}

/-- **Cancellation in the partial sums of a level-one cusp form**, `0 < ε ≤ 1/2`. -/
theorem cuspForm_partial_sum_sharp_aux (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖TauPartialSums.A (coef f) x‖ ≤ C * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε) := by
  have hk1 : 1 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set a := coef f with ha
  have ha0 : a 0 = 0 := coef_zero f
  -- parameters
  set r : ℕ := ⌈1 / ε⌉₊ + 2 with hrdef
  have hr2 : 2 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hrε : 1 ≤ ε * ((r : ℝ) - 1) := by
    have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((r : ℝ) - 1) = (⌈1 / ε⌉₊ : ℝ) + 1 := by rw [hrdef]; push_cast; ring
    rw [h2]
    have : ε * (1 / ε) = 1 := by field_simp
    nlinarith
  set b : ℝ := ((k : ℝ) + 1) / 2 with hb
  set σm : ℝ := (2 * (k : ℝ) - 3) / 4 with hσm
  set eta : ℝ := ε / 8 with heta
  set σt : ℝ := ((k : ℝ) - r) / 2 + eta with hσt
  set γ : ℝ := ((k : ℝ) + 1) / 2 + eta with hγ
  set β₀ : ℝ := (k : ℝ) / 2 - 1 / 4 with hβ₀
  set βr : ℝ := σt + r with hβr
  set J : ℕ → ℝ → ℂ := fun j => Jc k j b with hJ
  set cst : ℂ := (I ^ k)⁻¹ * ((2 * π : ℂ) ^ k)⁻¹ with hcst
  -- kernels
  obtain ⟨C0, hC0⟩ := kernelZero_sharp (k := k) hk3
  obtain ⟨Kt, hKt0, hKt⟩ := norm_Jc_le k r (σ := σt) (by rw [hσt]; linarith)
    (by rw [hσt, heta]; linarith) (by rw [hσt]; linarith)
  set A₀ : ℝ := |C0| + Kt with hA₀
  have hA0 : 0 ≤ A₀ := by positivity
  have hbot : ∀ y, 1 ≤ y → ‖J 0 y‖ ≤ A₀ * y ^ β₀ := by
    intro y hy
    refine (hC0 y hy).trans ?_
    have : 0 ≤ y ^ β₀ := by positivity
    calc C0 * y ^ ((k : ℝ) / 2 - 1 / 4) ≤ |C0| * y ^ β₀ := by
          rw [← hβ₀]; gcongr; exact le_abs_self C0
      _ ≤ A₀ * y ^ β₀ := by gcongr; rw [hA₀]; linarith
  have hshift_t : ∀ y, 0 < y → Jc k r b y = Jc k r σt y := fun y hy =>
    Jc_shift k r (A := σt) (B := b) (by rw [hσt]; linarith) (by rw [hb]; linarith)
      (by rw [hσt]; linarith) (by rw [hσt, hb]; linarith) le_rfl le_rfl (by rw [hσt, hb]; linarith)
      hy
  have htop : ∀ y, 1 ≤ y → ‖J r y‖ ≤ A₀ * y ^ βr := by
    intro y hy
    simp only [hJ]
    rw [hshift_t y (by linarith)]
    refine (hKt y (by linarith)).trans ?_
    have : 0 ≤ y ^ βr := by positivity
    rw [← hβr]; gcongr; rw [hA₀]; linarith [abs_nonneg C0]
  have hcont : ∀ j, ContinuousOn (J j) (Set.Ioi 0) := fun j =>
    continuousOn_Jc k j (σ := b) (by rw [hb]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      (by rw [hb]; linarith) (by rw [hb]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hrel : ∀ j, j < r → ∀ u, 0 < u → ∀ v, 0 ≤ v →
      J (j + 1) (u + v) - J (j + 1) u = ((j : ℂ) + 1) * ∫ w in (0 : ℝ)..v, J j (u + w) :=
    fun j _ u hu v hv => Jc_rel k j (σ := b) (by rw [hb]; linarith) (by rw [hb]; linarith)
      (by rw [hb]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) hu hv
  have hrep : ∀ y, 1 ≤ y → WC a r y = cst * ∑' n : ℕ, a n / (n : ℂ) ^ (k + r) * J r (n * y) := by
    intro y hy
    rw [ha, dual_rep f hk hr2 (by linarith : (0 : ℝ) < y), hcst]
    congr 1
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coef_zero]
    · have hny : 0 < (n : ℝ) * y := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      simp only [hJ]
      rw [Jc_shift k r (A := σm) (B := b) (by rw [hσm]; linarith) (by rw [hb]; linarith)
        (by rw [hσm]; linarith) le_rfl (by rw [hσm, hb]; linarith) (by rw [hσm, hb]; linarith)
        le_rfl hny]
  have hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-γ) := by
    refine (summable_norm_coef_div_rpow f hk1 (σ := γ) (by rw [hγ, heta]; linarith)).congr
      fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hβ00 : 0 ≤ β₀ := by rw [hβ₀]; linarith
  have hβr0 : 0 ≤ βr := by rw [hβr, hσt, heta]; linarith
  have hγ0 : 0 ≤ β₀ - k + γ := by rw [hβ₀, hγ, heta]; linarith
  have hγr : βr - k - r + γ ≤ 0 := by rw [hβr, hσt, hγ, heta]; linarith
  -- short sums
  obtain ⟨Crs, hRS⟩ := RankinExact.rankinSelberg_exact_general f
  have hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        Crs * (N : ℝ) ^ ((3 : ℝ) / 5) := fun N hN => hRS N hN
  obtain ⟨Q, hQ0, hQ⟩ := short_bound a (k - 1) hT r
  -- the final constant
  set L : ℝ := ∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-γ) with hL
  have hL0 : 0 ≤ L := tsum_nonneg fun n => by positivity
  set R : ℝ := (r : ℝ) + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith
  set E : ℝ := ((k : ℝ) - 1) / 2 + 2 / 5 + ε with hE
  refine ⟨‖cst‖ * L * A₀ * (R ^ β₀ + 2 ^ r / (Nat.factorial r : ℝ) * R ^ βr) + Real.sqrt Q,
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set h : ℝ := x ^ ((1 : ℝ) / 5) with hh
  have hh1 : 1 ≤ h := Real.one_le_rpow hx (by norm_num)
  have hh35 : h ≤ x ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hhx : h ≤ x := by
    calc h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  set M : ℝ := x ^ ((3 : ℝ) / 5 + ε) with hMdef
  have hM1 : 1 ≤ M := Real.one_le_rpow hx (by linarith)
  have hLI := landau_ineq a ha0 r k J cst hcont hrel hrep hA0 hβ00 hβr0 hbot htop hsum hγ0 hγr
    hx (by linarith : (0 : ℝ) < h) hM1
  have hS := hQ x hx h hh1 hh35
  -- the pieces as powers of `x`
  have hX : x + r * h ≤ R * x := by
    have : (r : ℝ) * h ≤ r * x := mul_le_mul_of_nonneg_left hhx (Nat.cast_nonneg r)
    rw [hR]; linarith
  have hXp : ∀ p : ℝ, 0 ≤ p → (x + r * h) ^ p ≤ R ^ p * x ^ p := fun p hp => by
    rw [← Real.mul_rpow (by linarith) hx0.le]
    exact Real.rpow_le_rpow (by positivity) hX hp
  have hMp : ∀ p : ℝ, M ^ p = x ^ (((3 : ℝ) / 5 + ε) * p) := fun p => by
    rw [hMdef, ← Real.rpow_mul hx0.le]
  have hhr : h ^ r = x ^ ((r : ℝ) / 5) := by
    rw [hh, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; ring
  obtain ⟨e1, e2⟩ := exps_ok (k := (k : ℝ)) (r := (r : ℝ)) hε0 hε hrε
  have hT1 : (x + r * h) ^ β₀ * M ^ (β₀ - k + γ) ≤ R ^ β₀ * x ^ E := by
    rw [hMp]
    calc (x + r * h) ^ β₀ * x ^ (((3 : ℝ) / 5 + ε) * (β₀ - k + γ)) ≤
        (R ^ β₀ * x ^ β₀) * x ^ (((3 : ℝ) / 5 + ε) * (β₀ - k + γ)) := by
          exact mul_le_mul_of_nonneg_right (hXp β₀ hβ00) (by positivity)
      _ = R ^ β₀ * x ^ (β₀ + ((3 : ℝ) / 5 + ε) * (β₀ - k + γ)) := by
          rw [Real.rpow_add hx0 β₀]; ring
      _ ≤ R ^ β₀ * x ^ E := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
          have e0 : β₀ - k + γ = 1 / 4 + ε / 8 := by rw [hβ₀, hγ, heta]; ring
          rw [e0, hβ₀, hE]; linarith [e1]
  have hT2 : 2 ^ r / ((Nat.factorial r : ℝ) * h ^ r) * (x + r * h) ^ βr * M ^ (βr - k - r + γ) ≤
      2 ^ r / (Nat.factorial r : ℝ) * R ^ βr * x ^ E := by
    rw [hMp, hhr]
    have hfac : (0 : ℝ) < (Nat.factorial r : ℝ) := by positivity
    have hxr : 0 < x ^ ((r : ℝ) / 5) := by positivity
    have e : 2 ^ r / ((Nat.factorial r : ℝ) * x ^ ((r : ℝ) / 5)) =
        2 ^ r / (Nat.factorial r : ℝ) * x ^ (-((r : ℝ) / 5)) := by
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_div]
    rw [e]
    calc 2 ^ r / (Nat.factorial r : ℝ) * x ^ (-((r : ℝ) / 5)) * (x + r * h) ^ βr *
          x ^ (((3 : ℝ) / 5 + ε) * (βr - k - r + γ))
        ≤ 2 ^ r / (Nat.factorial r : ℝ) * x ^ (-((r : ℝ) / 5)) * (R ^ βr * x ^ βr) *
          x ^ (((3 : ℝ) / 5 + ε) * (βr - k - r + γ)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hXp βr hβr0)
            (by positivity)) (by positivity)
      _ = 2 ^ r / (Nat.factorial r : ℝ) * R ^ βr *
          x ^ (-((r : ℝ) / 5) + βr + ((3 : ℝ) / 5 + ε) * (βr - k - r + γ)) := by
          rw [Real.rpow_add hx0 (-((r : ℝ) / 5) + βr), Real.rpow_add hx0 (-((r : ℝ) / 5))]; ring
      _ ≤ 2 ^ r / (Nat.factorial r : ℝ) * R ^ βr * x ^ E := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
          have e0 : βr - k - r + γ = (1 - r) / 2 + ε / 8 + ε / 8 := by
            rw [hβr, hσt, hγ, heta]; ring
          have e0' : βr = ((k : ℝ) - r) / 2 + ε / 8 + r := by rw [hβr, hσt, heta]
          rw [e0, e0', hE]; linarith [e2]
  have hT3 : Real.sqrt Q * (h ^ ((1 : ℝ) / 2) * x ^ (((k - 1 : ℕ) : ℝ) / 2 + 3 / 10)) ≤
      Real.sqrt Q * x ^ E := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have e0 : h ^ ((1 : ℝ) / 2) * x ^ (((k - 1 : ℕ) : ℝ) / 2 + 3 / 10) =
        x ^ ((1 : ℝ) / 5 * (1 / 2) + (((k - 1 : ℕ) : ℝ) / 2 + 3 / 10)) := by
      rw [hh, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    rw [e0]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    exact exp3 hk1 hε0
  have hcL : 0 ≤ ‖cst‖ * L * A₀ := by positivity
  calc ‖TauPartialSums.A a x‖ ≤ ‖cst‖ * L * A₀ * ((x + r * h) ^ β₀ * M ^ (β₀ - k + γ) +
        2 ^ r / ((Nat.factorial r : ℝ) * h ^ r) * (x + r * h) ^ βr * M ^ (βr - k - r + γ)) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + r * h⌋₊, ‖a n‖ := hLI
    _ ≤ ‖cst‖ * L * A₀ * (R ^ β₀ * x ^ E + 2 ^ r / (Nat.factorial r : ℝ) * R ^ βr * x ^ E) +
        Real.sqrt Q * x ^ E :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hcL) (hS.trans hT3)
    _ = (‖cst‖ * L * A₀ * (R ^ β₀ + 2 ^ r / (Nat.factorial r : ℝ) * R ^ βr) + Real.sqrt Q) *
        x ^ E := alg _ _ _ _ _

/-- **Cancellation in the partial sums of a level-one cusp form** (unconditional): for every
`f ∈ S_k(SL₂(ℤ))` and `ε > 0`, `‖∑_{n≤x} a_f(n)‖ ≤ C x^{(k−1)/2 + 2/5 + ε}` for all `x ≥ 1`. -/
theorem cuspForm_partial_sum_sharp (f : CuspForm 𝒮ℒ (k : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ≤ C * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := eq_zero_of_lt_twelve f hk
    refine ⟨0, fun x _ => ?_⟩
    have h0 : ∀ n, coef (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coef, UpperHalfPlane.qExpansion_zero]
    simp [h0]
  · set ε' : ℝ := min ε (1 / 2) with hε'
    have hε'0 : 0 < ε' := lt_min hε (by norm_num)
    have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
    have hε'2 : ε' ≤ ε := min_le_left _ _
    obtain ⟨C, hC⟩ := cuspForm_partial_sum_sharp_aux f hk hε'0 hε'1
    refine ⟨|C|, fun x hx => ?_⟩
    refine (hC x hx).trans ?_
    have hle : x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε') ≤ x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hx0 : 0 ≤ x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε') := by positivity
    calc C * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε') ≤ |C| * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε') :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hx0
      _ ≤ |C| * x ^ (((k : ℝ) - 1) / 2 + 2 / 5 + ε) := by gcongr

/-- **`∑_{n≤x} τ(n) ≪ x^{59/10+ε}`** (unconditional; `59/10 = 11/2 + 2/5`). -/
theorem tau_partial_sum_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((59 : ℝ) / 10 + ε) := by
  obtain ⟨C, hC⟩ := cuspForm_partial_sum_sharp (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) hε
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x hx
  simp_rw [coef_discriminant] at h
  have e1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, tauC n =
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at h
  have e2 : (((12 : ℕ) : ℝ) - 1) / 2 + 2 / 5 + ε = (59 : ℝ) / 10 + ε := by norm_num
  rw [e2] at h
  exact h

/-- The new exponent beats the previous `181/30` and the Rankin exponent `13/2`. -/
lemma exponent_lt : (59 : ℝ) / 10 < 181 / 30 ∧ (181 : ℝ) / 30 < 13 / 2 := by
  constructor <;> norm_num

end RamanujanTau.TauPartialSumsSharp

#print axioms RamanujanTau.TauPartialSumsSharp.dual_rep
#print axioms RamanujanTau.TauPartialSumsSharp.kernelZero_sharp
#print axioms RamanujanTau.TauPartialSumsSharp.bracket_signed
#print axioms RamanujanTau.TauPartialSumsSharp.landau_ineq
#print axioms RamanujanTau.TauPartialSumsSharp.short_bound
#print axioms RamanujanTau.TauPartialSumsSharp.cuspForm_partial_sum_sharp_aux
#print axioms RamanujanTau.TauPartialSumsSharp.cuspForm_partial_sum_sharp
#print axioms RamanujanTau.TauPartialSumsSharp.tau_partial_sum_sharp
