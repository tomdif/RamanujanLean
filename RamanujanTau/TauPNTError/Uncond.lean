/-
# The PNT for `τ` with de la Vallée-Poussin error term, without Deligne

* `F1_bound_vP`: the first Riesz sum of the prime part `vP` of `Λ_Δ` is `≪ x² exp(−a√log x)`
  (`F1_bound_vM` minus the higher prime powers, `sum_abs_vH_le`).
* Landau differencing (`TauPartialSums.main_ineq`) for `vP` with *Rankin–Selberg* short sums
  instead of Deligne: `|vP(p)| = √(τ(p)²/p¹¹)·log p`, Cauchy–Schwarz and
  `Σ_{N<n≤M} τ(n)²/n¹¹ ≤ c(M−N) + 2C M^{3/5}` give `Σ_{x<n≤x+h} |vP(n)| ≤ D log(2x)(h + (2x)^{3/5})`.
* `tau_PNT_error_uncond`: `|Σ_{p≤N} τ(p)p^{−11/2} log p| ≤ K N exp(−b√log N)`.
* `psiDelta_error_uncond`: `|Σ_{n≤x} Λ_Δ(n)| ≤ K x exp(−b√log x)`.
* `tau_PNT_tau_error_uncond`: `|Σ_{p<N} τ(p) log p| ≤ K N^{13/2} exp(−b√log N)`.
-/
import RamanujanTau.TauPNTError.UncondH

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Complex Filter Topology
open RamanujanTau.TauPNT RamanujanTau.EdgeNonvanishing RamanujanTau.TauPartialSums

/-- `x^{9/10} ≤ x exp(−b√log x)` for `x ≥ 3`, `0 ≤ b ≤ 1/10`. -/
lemma pow_910_le {b : ℝ} (hb : b ≤ 1 / 10) {x : ℝ} (hx : 3 ≤ x) :
    x ^ (9 / 10 : ℝ) ≤ x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := one_le_log_three.trans (Real.log_le_log (by norm_num) hx)
  set ℓ := Real.sqrt (Real.log x) with hℓ
  have hℓsq : ℓ ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogx
  rw [show (9 / 10 : ℝ) = 1 + (-(1 / 10)) by norm_num, Real.rpow_add hx0, Real.rpow_one,
    Real.rpow_def_of_pos hx0, ← hℓsq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx0.le
  nlinarith

/-- `(log x) x^{3/5} ≤ 10 x^{9/10}`. -/
lemma log_mul_pow35_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x * x ^ (3 / 5 : ℝ) ≤ 10 * x ^ (9 / 10 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_rpow_div (x := x) (by linarith) (ε := 1 / 10) (by norm_num)
  have h1 : Real.log x ≤ 10 * x ^ (1 / 10 : ℝ) := by
    linarith [show x ^ (1 / 10 : ℝ) / (1 / 10) = 10 * x ^ (1 / 10 : ℝ) by ring]
  calc Real.log x * x ^ (3 / 5 : ℝ) ≤ 10 * x ^ (1 / 10 : ℝ) * x ^ (3 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 10 * x ^ (7 / 10 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
    _ ≤ 10 * x ^ (9 / 10 : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hx (show (7 / 10 : ℝ) ≤ 9 / 10 by norm_num)
        linarith

lemma F1_sub (x : ℝ) :
    F1 (fun n => (vP n : ℂ)) x = F1 (fun n => (vM n : ℂ)) x - F1 (fun n => (vH n : ℂ)) x := by
  unfold F1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := vP_add_vH n
  have e : (vP n : ℂ) = (vM n : ℂ) - (vH n : ℂ) := by
    rw [← this]; push_cast; ring
  dsimp only
  rw [e]; ring

lemma norm_F1_vH_le {C : ℝ} (hC : ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, |vH n| ≤ C * (N : ℝ) ^ (9 / 10 : ℝ)) (hC0 : 0 ≤ C) {y : ℝ}
    (hy : 1 ≤ y) : ‖F1 (fun n => (vH n : ℂ)) y‖ ≤ C * y * y ^ (9 / 10 : ℝ) := by
  unfold F1
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖(vH n : ℂ) * ((y : ℂ) - n)‖ ≤ |vH n| * y := by
    intro n hn
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2).trans hfl
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ((y : ℂ) - n) = ((y - n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ y - n by linarith)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  have h2 := hC _ hN
  have h3 : (⌊y⌋₊ : ℝ) ^ (9 / 10 : ℝ) ≤ y ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hfl (by norm_num)
  calc (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |vH n|) * y ≤ (C * y ^ (9 / 10 : ℝ)) * y := by
        gcongr; exact h2.trans (by gcongr)
    _ = _ := by ring

/-- **First Riesz sum of the prime part** (unconditional). -/
theorem F1_bound_vP : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 64 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    ‖F1 (fun n => (vP n : ℂ)) x‖ ≤ K * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, hF⟩ := F1_bound_vM
  obtain ⟨C, hC0, hC⟩ := sum_abs_vH_le
  refine ⟨a, ha, ha64, K + C, by positivity, fun x hx => ?_⟩
  rw [F1_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 := hF x hx
  have h2 := norm_F1_vH_le hC hC0 (y := x) (by linarith)
  have h3 := pow_910_le (b := a) (by linarith) hx
  have h4 : C * x * x ^ (9 / 10 : ℝ) ≤ C * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) := by
    calc C * x * x ^ (9 / 10 : ℝ) ≤ C * x * (x * Real.exp (-a * Real.sqrt (Real.log x))) := by
          gcongr
      _ = _ := by ring
  have : (K + C) * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) =
      K * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) +
        C * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) := by ring
  linarith

lemma norm_vP_le {n : ℕ} {y : ℝ} (hn : 1 ≤ n) (hny : (n : ℝ) ≤ y) :
    ‖(vP n : ℂ)‖ ≤ Real.sqrt (rsb n) * Real.log y := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold vP
  split_ifs with hp
  · rw [vM_prime hp, abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn)),
      ← lam_sq_eq hp.pos, Real.sqrt_sq_eq_abs]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hn) hny) (abs_nonneg _)
  · simp only [abs_zero]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 ≤ Real.log y := Real.log_nonneg (h1.trans hny)
    positivity

/-- Rankin–Selberg short sums of `√(τ(n)²/n¹¹)`. -/
lemma short_rs {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Finset.Icc 1 N, rsb n - rsc * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5))
    {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ioc N M, Real.sqrt (rsb n)) ^ 2 ≤
      ((M : ℝ) - N) * (rsc * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5)) := by
  have hcard : ((Finset.Ioc N M).card : ℝ) = (M : ℝ) - N := by
    rw [Nat.card_Ioc, Nat.cast_sub hNM]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc N M) (f := fun n => Real.sqrt (rsb n))
  rw [hcard] at hCS
  simp_rw [Real.sq_sqrt (rsb_nonneg _)] at hCS
  have hsplit : ∑ n ∈ Finset.Ioc N M, rsb n =
      ∑ n ∈ Finset.Icc 1 M, rsb n - ∑ n ∈ Finset.Icc 1 N, rsb n := by
    rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hNM]
    ring
  have h1 := (abs_le.1 (hC M (hN.trans hNM))).2
  have h2 := (abs_le.1 (hC N hN)).1
  have hMN : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ ((3 : ℝ) / 5) ≤ (M : ℝ) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (by linarith) hMN (by norm_num)
  have hdiff : ∑ n ∈ Finset.Ioc N M, rsb n ≤ rsc * ((M : ℝ) - N) + 2 * C * (M : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [hsplit]; nlinarith
  refine hCS.trans ?_
  exact mul_le_mul_of_nonneg_left hdiff (by linarith)

set_option maxHeartbeats 2000000 in
/-- **Prime part: `Σ_{n≤x} vP(n) ≪ x exp(−b√log x)`** (unconditional). -/
theorem A_vP_error : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    ‖A (fun n => (vP n : ℂ)) x‖ ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, hF⟩ := F1_bound_vP
  obtain ⟨C, hC0, hC⟩ := rs_partial
  have hrsc : 0 < rsc := rsc_pos
  set D : ℝ := 2 * (rsc + C + 1) with hD
  have hD0 : 0 < D := by positivity
  refine ⟨a / 4, by positivity, by linarith, 5 * K + 2 * D * (8 / a) ^ 2 + 40 * D, by positivity,
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := one_le_log_three.trans (Real.log_le_log (by norm_num) hx)
  set ℓ := Real.sqrt (Real.log x) with hℓ
  have hℓsq : ℓ ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogx
  set e : ℝ := Real.exp (-(a / 2) * ℓ) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * e with hh
  have hh0 : 0 < h := by positivity
  have hhx : h ≤ x := by rw [hh]; nlinarith
  have hh1 : 1 ≤ h := by
    rw [hh, he, ← Real.exp_log hx0, ← Real.exp_add, Real.one_le_exp_iff, ← hℓsq]
    nlinarith
  set a' : ℕ → ℂ := fun n => (vP n : ℂ) with ha'
  have hmain := main_ineq a' hx0.le hh0.le
  -- Riesz sums
  have hE : Real.exp (-a * Real.sqrt (Real.log (x + h))) ≤ Real.exp (-a * ℓ) := by
    apply Real.exp_le_exp.mpr
    have : ℓ ≤ Real.sqrt (Real.log (x + h)) :=
      Real.sqrt_le_sqrt (Real.log_le_log hx0 (by linarith))
    have := mul_le_mul_of_nonneg_left this ha.le
    linarith
  have hF1 : ‖F1 a' (x + h)‖ ≤ 4 * K * x ^ 2 * Real.exp (-a * ℓ) := by
    refine (hF (x + h) (by linarith)).trans ?_
    have : (x + h) ^ 2 ≤ 4 * x ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : 0 ≤ x + h) (by linarith : x + h ≤ 2 * x) 2
      linarith [show (2 * x) ^ 2 = 4 * x ^ 2 by ring]
    calc K * (x + h) ^ 2 * Real.exp (-a * Real.sqrt (Real.log (x + h)))
        ≤ K * (4 * x ^ 2) * Real.exp (-a * ℓ) := by gcongr
      _ = _ := by ring
  have hF2 : ‖F1 a' x‖ ≤ K * x ^ 2 * Real.exp (-a * ℓ) := hF x hx
  -- short sum (Rankin–Selberg)
  set X : ℝ := (2 * x) ^ ((3 : ℝ) / 5) with hX
  have hX0 : 0 ≤ X := by positivity
  have hshort : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤ Real.log (2 * x) * (D * (h + X)) := by
    have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hNM : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
    have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤
        Real.sqrt (rsb n) * Real.log (2 * x) := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
      exact norm_vP_le (by omega)
        ((Nat.cast_le.2 h2).trans ((Nat.floor_le (by linarith)).trans (by linarith)))
    have hS := short_rs hC0 hC hN1 hNM
    have hcard : ((⌊x + h⌋₊ : ℕ) : ℝ) - ⌊x⌋₊ ≤ 2 * h := by
      have h1 : (⌊x + h⌋₊ : ℝ) ≤ x + h := Nat.floor_le (by linarith)
      have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hcard0 : (0 : ℝ) ≤ ((⌊x + h⌋₊ : ℕ) : ℝ) - ⌊x⌋₊ := by
      have : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ⌊x + h⌋₊ := by exact_mod_cast hNM
      linarith
    have hMX : ((⌊x + h⌋₊ : ℕ) : ℝ) ^ ((3 : ℝ) / 5) ≤ X := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      exact (Nat.floor_le (by linarith)).trans (by linarith)
    have hS2 : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, Real.sqrt (rsb n)) ^ 2 ≤ (D * (h + X)) ^ 2 := by
      refine hS.trans ?_
      set m : ℝ := ((⌊x + h⌋₊ : ℕ) : ℝ) - ⌊x⌋₊
      have i1 : rsc * m + 2 * C * ((⌊x + h⌋₊ : ℕ) : ℝ) ^ ((3 : ℝ) / 5) ≤
          rsc * (2 * h) + 2 * C * X := by gcongr
      have i2 : m * (rsc * m + 2 * C * ((⌊x + h⌋₊ : ℕ) : ℝ) ^ ((3 : ℝ) / 5)) ≤
          (2 * h) * (rsc * (2 * h) + 2 * C * X) := by
        apply mul_le_mul hcard i1 (by positivity) (by positivity)
      refine i2.trans ?_
      have hD2 : 4 * rsc ≤ D ^ 2 := by rw [hD]; nlinarith
      have hD3 : 4 * C ≤ 2 * D ^ 2 := by rw [hD]; nlinarith
      have : (D * (h + X)) ^ 2 = D ^ 2 * h ^ 2 + 2 * D ^ 2 * (h * X) + D ^ 2 * X ^ 2 := by ring
      rw [this]
      have : 0 ≤ h * X := by positivity
      have : 0 ≤ D ^ 2 * X ^ 2 := by positivity
      have : 4 * rsc * h ^ 2 ≤ D ^ 2 * h ^ 2 := by gcongr
      have : 4 * C * (h * X) ≤ 2 * D ^ 2 * (h * X) := by gcongr
      nlinarith
    have hS3 : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, Real.sqrt (rsb n) ≤ D * (h + X) :=
      (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
        (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hS2
    calc ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖
        ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, Real.sqrt (rsb n) * Real.log (2 * x) :=
          Finset.sum_le_sum hterm
      _ = Real.log (2 * x) * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, Real.sqrt (rsb n) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ Real.log (2 * x) * (D * (h + X)) := by
          gcongr
          exact Real.log_nonneg (by linarith)
  have hlog2x : Real.log (2 * x) ≤ 2 * ℓ ^ 2 := by
    rw [hℓsq, show 2 * Real.log x = Real.log (x ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    nlinarith
  -- combine
  have hxe : x ^ 2 * Real.exp (-a * ℓ) = h * (x * e) := by
    rw [hh, he]
    have : Real.exp (-a * ℓ) = Real.exp (-(a / 2) * ℓ) * Real.exp (-(a / 2) * ℓ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have key : h * ‖A a' x‖ ≤ h * (5 * K * (x * e) + 2 * ℓ ^ 2 * (D * (h + X))) := by
    have hs2 : h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤ h * (2 * ℓ ^ 2 * (D * (h + X))) := by
      apply mul_le_mul_of_nonneg_left _ hh0.le
      refine hshort.trans ?_
      have : 0 ≤ D * (h + X) := by positivity
      nlinarith
    have : ‖F1 a' (x + h)‖ + ‖F1 a' x‖ ≤ h * (5 * K * (x * e)) := by
      have : 4 * K * x ^ 2 * Real.exp (-a * ℓ) + K * x ^ 2 * Real.exp (-a * ℓ) =
          h * (5 * K * (x * e)) := by
        rw [show 4 * K * x ^ 2 * Real.exp (-a * ℓ) + K * x ^ 2 * Real.exp (-a * ℓ) =
          5 * K * (x ^ 2 * Real.exp (-a * ℓ)) by ring, hxe]; ring
      linarith
    have : h * (5 * K * (x * e) + 2 * ℓ ^ 2 * (D * (h + X))) =
        h * (5 * K * (x * e)) + h * (2 * ℓ ^ 2 * (D * (h + X))) := by ring
    linarith
  have hAb : ‖A a' x‖ ≤ 5 * K * (x * e) + 2 * ℓ ^ 2 * (D * (h + X)) :=
    le_of_mul_le_mul_left key hh0
  -- final numerics
  set E4 : ℝ := Real.exp (-(a / 4) * ℓ) with hE4
  have hsq := sq_mul_exp_le (a := a / 2) (ℓ := ℓ) (by positivity) (by linarith)
  have e1 : (4 / (a / 2)) = 8 / a := by field_simp; norm_num
  rw [e1, show -(a / 2 / 2) * ℓ = -(a / 4) * ℓ by ring] at hsq
  have he4 : e ≤ E4 := by
    rw [he, hE4]; apply Real.exp_le_exp.mpr; nlinarith
  have t1 : 2 * ℓ ^ 2 * (D * h) ≤ 2 * D * (8 / a) ^ 2 * (x * E4) := by
    calc 2 * ℓ ^ 2 * (D * h) = 2 * D * x * (ℓ ^ 2 * e) := by rw [hh]; ring
      _ ≤ 2 * D * x * ((8 / a) ^ 2 * E4) := by gcongr
      _ = _ := by ring
  have t2 : 2 * ℓ ^ 2 * (D * X) ≤ 40 * D * (x * E4) := by
    have hX2 : X ≤ 2 * x ^ ((3 : ℝ) / 5) := by
      rw [hX, Real.mul_rpow (by norm_num) hx0.le]
      gcongr
      calc (2 : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h35 := log_mul_pow35_le (x := x) (by linarith)
    have h910 := pow_910_le (b := a / 4) (by linarith) hx
    rw [← hℓ, ← hE4] at h910
    rw [← hℓsq] at h35
    calc 2 * ℓ ^ 2 * (D * X) ≤ 2 * ℓ ^ 2 * (D * (2 * x ^ ((3 : ℝ) / 5))) := by gcongr
      _ = 4 * D * (ℓ ^ 2 * x ^ ((3 : ℝ) / 5)) := by ring
      _ ≤ 4 * D * (10 * x ^ (9 / 10 : ℝ)) := by gcongr
      _ ≤ 4 * D * (10 * (x * E4)) := by gcongr
      _ = _ := by ring
  have t3 : 5 * K * (x * e) ≤ 5 * K * (x * E4) := by gcongr
  have : (5 * K + 2 * D * (8 / a) ^ 2 + 40 * D) * x * E4 =
      5 * K * (x * E4) + 2 * D * (8 / a) ^ 2 * (x * E4) + 40 * D * (x * E4) := by ring
  have : 2 * ℓ ^ 2 * (D * (h + X)) = 2 * ℓ ^ 2 * (D * h) + 2 * ℓ ^ 2 * (D * X) := by ring
  rw [hE4] at *
  linarith

/-- **PNT for `τ` with de la Vallée-Poussin error term, unconditional**:
`|Σ_{p ≤ N} τ(p) p^{−11/2} log p| ≤ K N exp(−b√log N)`. -/
theorem tau_PNT_error_uncond : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 3 ≤ N →
    |∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p| ≤
      K * N * Real.exp (-b * Real.sqrt (Real.log N)) := by
  obtain ⟨b, hb, hb256, K, hK, hA⟩ := A_vP_error
  refine ⟨b, hb, hb256, K, hK, fun N hN => ?_⟩
  have h := hA N (by exact_mod_cast hN)
  have e : ∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p =
      ∑ n ∈ Finset.Icc 1 N, vP n := by
    rw [← sum_range_succ_eq_Icc _ vP_zero, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold vP
    split_ifs with hp
    · exact (vM_prime hp).symm
    · rfl
  rw [e]
  have hA' : ‖A (fun n => (vP n : ℂ)) N‖ = |∑ n ∈ Finset.Icc 1 N, vP n| := by
    rw [A, Nat.floor_natCast, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [← hA']
  exact h

/-- **`ψ_Δ(x) ≪ x exp(−b√log x)`, unconditional.** -/
theorem psiDelta_error_uncond : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 3 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vM n| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  obtain ⟨b, hb, hb256, K, hK, hA⟩ := A_vP_error
  obtain ⟨C, hC0, hC⟩ := sum_abs_vH_le
  refine ⟨b, hb, hb256, K + C, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have e : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vM n =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vP n + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vH n := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => (vP_add_vH n).symm
  rw [e]
  have h1 : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vP n| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
    have := hA x hx
    rwa [A, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] at this
  have h2 : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vH n| ≤ C * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((hC _ hN).trans ?_)
    have h3 : (⌊x⌋₊ : ℝ) ^ (9 / 10 : ℝ) ≤ x ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hfl (by norm_num)
    have h4 := pow_910_le (b := b) (by linarith) hx
    calc C * (⌊x⌋₊ : ℝ) ^ (9 / 10 : ℝ) ≤ C * (x * Real.exp (-b * Real.sqrt (Real.log x))) := by
          gcongr; exact h3.trans h4
      _ = _ := by ring
  have := abs_add_le (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vP n) (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vH n)
  have : (K + C) * x * Real.exp (-b * Real.sqrt (Real.log x)) =
      K * x * Real.exp (-b * Real.sqrt (Real.log x)) +
        C * x * Real.exp (-b * Real.sqrt (Real.log x)) := by ring
  linarith

/-- **`Σ_{p<N} τ(p) log p ≪ N^{13/2} exp(−b√log N)`, unconditional.** -/
theorem tau_PNT_tau_error_uncond : ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 9 ≤ N →
    |∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p| ≤
      K * (N : ℝ) ^ (13 / 2 : ℝ) * Real.exp (-b * Real.sqrt (Real.log N)) := by
  obtain ⟨b, hb, hb256, K, hK, hT⟩ := tau_PNT_error_uncond
  exact tau_form_of_prime_bound hb (by linarith) hK hT

end RamanujanTau.TauPNTError
