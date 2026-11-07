/-
# Unsmoothing (Deligne): `ψ_Δ(x) ≪ x exp(−b√log x)` and the prime sum

* `F1_bound_vM` (unconditional): `‖Σ_{n≤x} Λ_Δ(n)(x−n)‖ ≤ K x² exp(−a√log x)`, `x ≥ 3`.
* `psiDelta_error` (`[DeligneBound]`): `|Σ_{n≤x} Λ_Δ(n)| ≤ K x exp(−b√log x)`.
  Landau differencing (`TauPartialSums.main_ineq`) with `h = x exp(−(a/2)√log x)` and
  `|Λ_Δ(n)| ≤ 2 log n` (Deligne).
* `tau_PNT_error` (`[DeligneBound]`): `|Σ_{p≤N} τ(p)p^{−11/2} log p| ≤ K N exp(−b√log N)`;
  prime powers `p^k`, `k ≥ 2`, contribute `≤ 4√(N+1) log(N+1)` (`TauPNT.nonprime_part_le`).
-/
import RamanujanTau.TauPNTError.Smoothed
import RamanujanTau.TauPNT.TauForm

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Complex Filter Topology
open RamanujanTau.TauPNT RamanujanTau.RankinError RamanujanTau.TauPartialSums
open RamanujanTau.EdgeNonvanishing

/-- **First Riesz sum of `Λ_Δ`** (unconditional). -/
theorem F1_bound_vM : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 64 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    ‖F1 (fun n => (vM n : ℂ)) x‖ ≤ K * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, h⟩ := smoothed_bound
  refine ⟨a, ha, ha64, K, hK, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [← tsum_phi_eq _ vM_zero hx0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0]
  have := h x hx
  calc x * ‖∑' n : ℕ, (vM n : ℂ) * (phi 1 (n / x) : ℂ)‖
      ≤ x * (K * x * Real.exp (-a * Real.sqrt (Real.log x))) := by gcongr
    _ = _ := by ring

/-- `√x log x ≤ 4 x exp(−b√log x)` for `x ≥ 3`, `b ≤ 1/4`. -/
lemma sqrt_log_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) {x : ℝ} (hx : 3 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := one_le_log_three.trans (Real.log_le_log (by norm_num) hx)
  set ℓ := Real.sqrt (Real.log x) with hℓ
  have hℓsq : ℓ ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogx
  have hxe : x = Real.exp (ℓ ^ 2) := by rw [hℓsq, Real.exp_log hx0]
  have hsx : Real.sqrt x = Real.exp (ℓ ^ 2 / 2) := by rw [Real.exp_half, ← hxe]
  have h1 : ℓ ^ 2 ≤ 4 * Real.exp (ℓ ^ 2 / 4) := by
    have := Real.add_one_le_exp (ℓ ^ 2 / 4); nlinarith
  rw [hsx, ← hℓsq]
  calc Real.exp (ℓ ^ 2 / 2) * ℓ ^ 2 ≤ Real.exp (ℓ ^ 2 / 2) * (4 * Real.exp (ℓ ^ 2 / 4)) := by
        gcongr
    _ = 4 * Real.exp (ℓ ^ 2 / 2 + ℓ ^ 2 / 4) := by rw [Real.exp_add]; ring
    _ ≤ 4 * Real.exp (ℓ ^ 2 + -b * ℓ) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        nlinarith
    _ = 4 * x * Real.exp (-b * ℓ) := by rw [Real.exp_add, ← hxe]; ring

section Deligne

variable [DeligneBound]

lemma norm_vM_le_log {n : ℕ} {y : ℝ} (hn : 1 ≤ n) (hny : (n : ℝ) ≤ y) :
    ‖(vM n : ℂ)‖ ≤ 2 * Real.log y := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_vM_le n).trans ?_
  have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 : Real.log n ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hn) hny
  linarith

set_option maxHeartbeats 2000000 in
/-- **`ψ_Δ(x) ≪ x exp(−b√log x)`** (Deligne). -/
theorem psiDelta_error : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vM n| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, hF⟩ := F1_bound_vM
  refine ⟨a / 4, by positivity, by linarith, 5 * K + 8 * (8 / a) ^ 2, by positivity,
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
  set a' : ℕ → ℂ := fun n => (vM n : ℂ) with ha'
  have hmain := main_ineq a' hx0.le hh0.le
  -- the Riesz sums
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
  -- the short sum (Deligne)
  have hshort : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤ (h + 1) * (2 * Real.log (2 * x)) := by
    have hcard : ((Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) ≤ h + 1 := by
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_le_floor (by linarith))]
      have h1 : (⌊x + h⌋₊ : ℝ) ≤ x + h := Nat.floor_le (by linarith)
      have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤ 2 * Real.log (2 * x) := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
      have hn1 : 1 ≤ n := by omega
      have hny : (n : ℝ) ≤ 2 * x :=
        (Nat.cast_le.2 h2).trans ((Nat.floor_le (by linarith)).trans (by linarith))
      exact norm_vM_le_log hn1 hny
    calc ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖
        ≤ ∑ _n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, 2 * Real.log (2 * x) := Finset.sum_le_sum hterm
      _ = (Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊).card * (2 * Real.log (2 * x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h + 1) * (2 * Real.log (2 * x)) := by
          have : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
          exact mul_le_mul_of_nonneg_right hcard (by linarith)
  have hlog2x : Real.log (2 * x) ≤ 2 * ℓ ^ 2 := by
    rw [hℓsq, show 2 * Real.log x = Real.log (x ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    nlinarith
  -- combine
  have hA : ‖A a' x‖ = |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vM n| := by
    rw [A, ha']
    simp only
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [← hA]
  have hxe : x ^ 2 * Real.exp (-a * ℓ) = h * (x * e) := by
    rw [hh, he]
    have : Real.exp (-a * ℓ) = Real.exp (-(a / 2) * ℓ) * Real.exp (-(a / 2) * ℓ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have key : h * ‖A a' x‖ ≤ h * (5 * K * (x * e) + 2 * (h + 1) * (2 * ℓ ^ 2)) := by
    have hs2 : h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a' n‖ ≤ h * (2 * (h + 1) * (2 * ℓ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hh0.le
      have : 0 ≤ h + 1 := by linarith
      nlinarith
    have : ‖F1 a' (x + h)‖ + ‖F1 a' x‖ ≤ h * (5 * K * (x * e)) := by
      have : 4 * K * x ^ 2 * Real.exp (-a * ℓ) + K * x ^ 2 * Real.exp (-a * ℓ) =
          h * (5 * K * (x * e)) := by
        rw [show 4 * K * x ^ 2 * Real.exp (-a * ℓ) + K * x ^ 2 * Real.exp (-a * ℓ) =
          5 * K * (x ^ 2 * Real.exp (-a * ℓ)) by ring, hxe]; ring
      linarith
    nlinarith
  have hAb : ‖A a' x‖ ≤ 5 * K * (x * e) + 2 * (h + 1) * (2 * ℓ ^ 2) :=
    le_of_mul_le_mul_left key hh0
  -- `h + 1 ≤ 2h = 2xe` and `ℓ² e ≤ (8/a)² exp(−(a/4)ℓ)`
  have hsq := sq_mul_exp_le (a := a / 2) (ℓ := ℓ) (by positivity) (by linarith)
  have e1 : (4 / (a / 2)) = 8 / a := by field_simp; norm_num
  rw [e1, show -(a / 2 / 2) * ℓ = -(a / 4) * ℓ by ring] at hsq
  have he4 : e ≤ Real.exp (-(a / 4) * ℓ) := by
    rw [he]; apply Real.exp_le_exp.mpr; nlinarith
  have hfinal : 5 * K * (x * e) + 2 * (h + 1) * (2 * ℓ ^ 2) ≤
      (5 * K + 8 * (8 / a) ^ 2) * x * Real.exp (-(a / 4) * ℓ) := by
    have t1 : 2 * (h + 1) * (2 * ℓ ^ 2) ≤ 8 * x * (ℓ ^ 2 * e) := by
      calc 2 * (h + 1) * (2 * ℓ ^ 2) ≤ 2 * (2 * h) * (2 * ℓ ^ 2) := by gcongr; linarith
        _ = 8 * x * (ℓ ^ 2 * e) := by rw [hh]; ring
    have t2 : 8 * x * (ℓ ^ 2 * e) ≤ 8 * x * ((8 / a) ^ 2 * Real.exp (-(a / 4) * ℓ)) := by
      gcongr
    have t3 : 5 * K * (x * e) ≤ 5 * K * (x * Real.exp (-(a / 4) * ℓ)) := by gcongr
    have t4 : (5 * K + 8 * (8 / a) ^ 2) * x * Real.exp (-(a / 4) * ℓ) =
        5 * K * (x * Real.exp (-(a / 4) * ℓ)) +
          8 * x * ((8 / a) ^ 2 * Real.exp (-(a / 4) * ℓ)) := by ring
    linarith
  exact hAb.trans hfinal

omit [DeligneBound] in
lemma sum_range_succ_eq_Icc (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Icc 1 N, f n := by
  have : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [this, Finset.sum_insert (by simp), hf, zero_add]

/-- **PNT for `τ` with de la Vallée-Poussin error term** (Deligne):
`Σ_{p ≤ N} τ(p) p^{−11/2} log p ≪ N exp(−b√log N)`. -/
theorem tau_PNT_error : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 256 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 3 ≤ N →
    |∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p| ≤
      K * N * Real.exp (-b * Real.sqrt (Real.log N)) := by
  obtain ⟨b, hb, hb256, K, hK, hψ⟩ := psiDelta_error
  refine ⟨b, hb, hb256, K + 64, by positivity, fun N hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsplit : ∑ p ∈ Finset.range (N + 1) with p.Prime, lam p * Real.log p =
      ∑ n ∈ Finset.range (N + 1), vM n - ∑ n ∈ Finset.range (N + 1) with ¬ n.Prime, vM n := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) Nat.Prime (fun n => vM n)]
    simp only [add_sub_cancel_right]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact (vM_prime (Finset.mem_filter.mp hp).2).symm
  have hv0 : vM 0 = 0 := vM_of_not (by simp [IsPrimePow])
  rw [hsplit, sum_range_succ_eq_Icc _ hv0]
  have h1 := hψ N hN3
  rw [Nat.floor_natCast] at h1
  have h2 := nonprime_part_le (N + 1) (by omega)
  -- `4√(N+1) log(N+1) ≤ 32 N exp(−b√log N)`
  have h3 : 4 * Real.sqrt ((N + 1 : ℕ) : ℝ) * Real.log ((N + 1 : ℕ) : ℝ) ≤
      64 * N * Real.exp (-b * Real.sqrt (Real.log N)) := by
    push_cast
    have hs : Real.sqrt (N + 1) ≤ 2 * Real.sqrt N := by
      rw [show (2 : ℝ) * Real.sqrt N = Real.sqrt (4 * N) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hl : Real.log (N + 1) ≤ 2 * Real.log N := by
      rw [show 2 * Real.log (N : ℝ) = Real.log ((N : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hl0 : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith)
    have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h4 := sqrt_log_le hb.le (by linarith) hN3
    calc 4 * Real.sqrt (N + 1) * Real.log (N + 1) ≤ 4 * (2 * Real.sqrt N) * (2 * Real.log N) := by
          gcongr
      _ = 16 * (Real.sqrt N * Real.log N) := by ring
      _ ≤ 16 * (4 * N * Real.exp (-b * Real.sqrt (Real.log N))) := by gcongr
      _ = _ := by ring
  have := abs_sub (∑ n ∈ Finset.Icc 1 N, vM n)
    (∑ n ∈ Finset.range (N + 1) with ¬ n.Prime, vM n)
  have hexp : (K + 64) * N * Real.exp (-b * Real.sqrt (Real.log N)) =
      K * N * Real.exp (-b * Real.sqrt (Real.log N)) +
        64 * N * Real.exp (-b * Real.sqrt (Real.log N)) := by ring
  linarith

end Deligne

end RamanujanTau.TauPNTError
