/-
# Mertens' first theorem for `ΛR` with error `O(1/log y)` (from `psiR_error`)

`ΛR = vR − 2·sqL` is the von Mangoldt function of `R(s) = Σ λ(n)² n^{−s}`.

**Theorem** (`mertens_LamR_err`, unconditional).  There are `c, B` with

  `|Σ_{m≤y} ΛR(m)/m − log y − c| ≤ B/(1 + log y)`   for all real `y ≥ 1`.

Proof.  With `D(m) = ψ_R(m) − m`, Abel summation gives (`abel_vR`)
`Σ_{m≤N} vR(m)/m = H_N + D(N)/(N+1) + Σ_{m≤N} D(m)/(m(m+1))`.  `psiR_error` makes the last
series converge with tail `≪ Σ_{m>N} 1/(m(1+log m)²) ≤ 1/(1+log N)` (telescoping
`1/(1+log m)`); `H_N = log N + γ + O(1/N)` (Mathlib's Euler–Mascheroni bounds); the square part
`Σ sqL(m)/m` converges with tail `≪ N^{−1/8}`.
-/
import RamanujanTau.SelbergDelange.Unsmooth
import RamanujanTau.SelbergCoeffs2.Cheb

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset Filter Topology
open RamanujanTau.TauPNTUncond (vR vR_nonneg)
open RamanujanTau.SelbergDelange (psiR psiR_error)
open RamanujanTau.SelbergCoeffs2 (LamR sqL sqL_nonneg sqL_sq sqL_zero_of_not)
open scoped ArithmeticFunction.vonMangoldt

lemma sum_Ioc_eq_range (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, g n = ∑ k ∈ range N, g (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_range_succ]

lemma psiR_nat (N : ℕ) : psiR (N : ℝ) = ∑ n ∈ Ioc 0 N, vR n := by
  rw [psiR, Nat.floor_natCast]
  congr 1
  first | done | (ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)

/-- `D(m) = ψ_R(m) − m`. -/
noncomputable def Dp (m : ℕ) : ℝ := psiR (m : ℝ) - m

lemma Dp_succ (N : ℕ) : Dp (N + 1) = Dp N + vR (N + 1) - 1 := by
  simp only [Dp, psiR_nat]
  rw [sum_Ioc_succ_top (Nat.zero_le _)]; push_cast; ring

/-- **Abel summation.** -/
lemma abel_vR (N : ℕ) :
    ∑ n ∈ Ioc 0 N, vR n / n = (harmonic N : ℝ) + Dp N / (N + 1) +
      ∑ m ∈ Ioc 0 N, Dp m / (m * (m + 1)) := by
  induction N with
  | zero => simp [Dp, psiR]
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_Ioc_succ_top (Nat.zero_le _), harmonic_succ,
      Dp_succ]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- A uniform bound `|D(m)| ≤ K m e^{−b√log m}` for all `m ≥ 1`. -/
lemma Dp_bound : ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
    |Dp m| ≤ K * m * Real.exp (-b * Real.sqrt (Real.log m)) := by
  obtain ⟨b, hb, K, X₀, hK, h⟩ := psiR_error
  set N₀ : ℕ := ⌈X₀⌉₊ with hN₀
  set P : ℝ := ∑ n ∈ Ioc 0 N₀, vR n + N₀ with hP
  have hP0 : 0 ≤ P := by
    have := sum_nonneg (s := Ioc 0 N₀) fun n _ => vR_nonneg n; positivity
  refine ⟨b, hb, max K (P * Real.exp (b ^ 2 / 4)), by positivity, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  rcases le_or_gt X₀ m with hX | hX
  · refine (show |psiR (m : ℝ) - m| ≤ _ from h m hX).trans ?_
    gcongr
    exact le_max_left _ _
  · -- small `m`
    have hmN : m ≤ N₀ := by
      have : (m : ℝ) ≤ N₀ := hX.le.trans (Nat.le_ceil X₀)
      exact_mod_cast this
    have hD : |Dp m| ≤ P := by
      rw [Dp, psiR_nat]
      have hs0 : 0 ≤ ∑ n ∈ Ioc 0 m, vR n := sum_nonneg fun n _ => vR_nonneg n
      have hs1 : ∑ n ∈ Ioc 0 m, vR n ≤ ∑ n ∈ Ioc 0 N₀, vR n :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hmN) fun n _ _ => vR_nonneg n
      have : (m : ℝ) ≤ N₀ := by exact_mod_cast hmN
      have hs2 : 0 ≤ ∑ n ∈ Ioc 0 N₀, vR n := sum_nonneg fun n _ => vR_nonneg n
      rw [abs_le]; constructor <;> linarith
    have hL : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hlow : Real.exp (-(b ^ 2 / 4)) ≤ m * Real.exp (-b * Real.sqrt (Real.log m)) := by
      have e : (m : ℝ) * Real.exp (-b * Real.sqrt (Real.log m)) =
          Real.exp (Real.log m + -b * Real.sqrt (Real.log m)) := by
        rw [Real.exp_add, Real.exp_log hm0]
      rw [e]
      apply Real.exp_le_exp.mpr
      have hs := Real.sq_sqrt hL
      nlinarith [sq_nonneg (Real.sqrt (Real.log m) - b / 2), Real.sqrt_nonneg (Real.log m)]
    have hE : Real.exp (b ^ 2 / 4) * Real.exp (-(b ^ 2 / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    calc |Dp m| ≤ P := hD
      _ = P * Real.exp (b ^ 2 / 4) * Real.exp (-(b ^ 2 / 4)) := by rw [mul_assoc, hE, mul_one]
      _ ≤ P * Real.exp (b ^ 2 / 4) * (m * Real.exp (-b * Real.sqrt (Real.log m))) := by gcongr
      _ ≤ max K (P * Real.exp (b ^ 2 / 4)) * (m * Real.exp (-b * Real.sqrt (Real.log m))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by ring

/-- `e^{−b√v} ≤ C/(1+v)²`. -/
lemma exp_neg_sqrt_le {b : ℝ} (hb : 0 < b) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v →
    Real.exp (-b * Real.sqrt v) ≤ C / (1 + v) ^ 2 := by
  refine ⟨2 * (1 + 24 / b ^ 4), by positivity, fun v hv => ?_⟩
  set y := b * Real.sqrt v with hy
  have hy0 : 0 ≤ y := by positivity
  have h4 := Real.pow_div_factorial_le_exp y hy0 4
  have hy4 : y ^ 4 = b ^ 4 * v ^ 2 := by
    have hs : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
    have : Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 := by ring
    rw [hy, mul_pow, this, hs]
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf, hy4] at h4
  have hE : 0 < Real.exp y := Real.exp_pos y
  have he1 : 1 ≤ Real.exp y := Real.one_le_exp hy0
  rw [show -b * Real.sqrt v = -y by ring, Real.exp_neg, le_div_iff₀ (by positivity)]
  rw [inv_mul_eq_div, div_le_iff₀ hE]
  have hb4 : 0 < b ^ 4 := by positivity
  have h5 : 24 / b ^ 4 * Real.exp y ≥ v ^ 2 := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hb4]; nlinarith
  nlinarith [sq_nonneg (v - 1)]

/-- Telescoping: `1/((m+1)(1+log(m+1))²) ≤ φ(m) − φ(m+1)`, `φ(m) = 1/(1+log m)`. -/
lemma tele_step {m : ℕ} (hm : 1 ≤ m) :
    1 / (((m + 1 : ℕ) : ℝ) * (1 + Real.log ((m + 1 : ℕ) : ℝ)) ^ 2) ≤
      1 / (1 + Real.log m) - 1 / (1 + Real.log ((m + 1 : ℕ) : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set a := Real.log m with ha
  set c := Real.log ((m + 1 : ℕ) : ℝ) with hc
  have ha0 : 0 ≤ a := Real.log_nonneg hm1
  have hac : a ≤ c := Real.log_le_log hm0 (by push_cast; linarith)
  have hdiff : 1 / ((m + 1 : ℕ) : ℝ) ≤ c - a := by
    rw [hc, ha, ← Real.log_div (by positivity) hm0.ne']
    have h := Real.one_sub_inv_le_log_of_pos (x := ((m + 1 : ℕ) : ℝ) / m) (by positivity)
    have e : 1 - (((m + 1 : ℕ) : ℝ) / m)⁻¹ = 1 / ((m + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    linarith
  have h1a : 1 + a ≠ 0 := by positivity
  have h1c : 1 + c ≠ 0 := by have := ha0.trans hac; positivity
  have e : 1 / (1 + a) - 1 / (1 + c) = (c - a) / ((1 + a) * (1 + c)) := by
    field_simp; ring
  rw [e]
  have hM : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 + a) * (1 + c) ≤ (1 + c) ^ 2 := by nlinarith
  have h2 : 1 ≤ (c - a) * ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hM] at hdiff; linarith
  nlinarith [sq_nonneg (1 + c)]

lemma tele_sum {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ k ∈ range M, 1 / (((N + k + 1 : ℕ) : ℝ) * (1 + Real.log ((N + k + 1 : ℕ) : ℝ)) ^ 2) ≤
      1 / (1 + Real.log N) := by
  have key : ∀ M : ℕ, ∑ k ∈ range M, 1 / (((N + k + 1 : ℕ) : ℝ) * (1 + Real.log ((N + k + 1 : ℕ) : ℝ)) ^ 2) ≤
      1 / (1 + Real.log N) - 1 / (1 + Real.log ((N + M : ℕ) : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have := tele_step (m := N + M) (by omega)
      have e : N + M + 1 = N + (M + 1) := by ring
      rw [e] at this ⊢
      push_cast at this ih ⊢
      linarith
  refine (key M).trans ?_
  have : 0 ≤ 1 / (1 + Real.log ((N + M : ℕ) : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((N + M : ℕ) : ℝ) by
      exact_mod_cast (show 1 ≤ N + M by omega))
    positivity
  linarith

/-! ### The vR part -/

/-- `Σ_{m≤N} vR(m)/m = log N + c_v + O(1/(1+log N))`. -/
theorem mertens_vR_err : ∃ cv B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Ioc 0 N, vR n / n - Real.log N - cv| ≤ B / (1 + Real.log N) := by
  obtain ⟨b, hb, K, hK, hD⟩ := Dp_bound
  obtain ⟨Cb, hCb, hexp⟩ := exp_neg_sqrt_le hb
  -- the summand `u (k) = D(k+1)/((k+1)(k+2))`
  set u : ℕ → ℝ := fun k => Dp (k + 1) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) with hu
  have hub : ∀ k, |u k| ≤ K * Cb * (1 / (((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ^ 2)) := by
    intro k
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by linarith
    have hl0 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg hk1
    have h1 := hD (k + 1) (by omega)
    have h2 := hexp (Real.log ((k + 1 : ℕ) : ℝ)) hl0
    simp only [hu]
    have hden : 0 < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h3 : |Dp (k + 1)| ≤ K * ((k + 1 : ℕ) : ℝ) * (Cb / (1 + Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
      refine h1.trans ?_
      have := Real.sqrt_nonneg (Real.log ((k + 1 : ℕ) : ℝ))
      gcongr
    refine h3.trans ?_
    set a : ℝ := ((k + 1 : ℕ) : ℝ)
    set L := Real.log ((k + 1 : ℕ) : ℝ)
    have hL1 : 0 < 1 + L := by linarith
    have e : K * Cb * (1 / (a * (1 + L) ^ 2)) * (a * (a + 1)) = K * Cb * (a + 1) / (1 + L) ^ 2 := by
      field_simp
    have e2 : K * a * (Cb / (1 + L) ^ 2) = K * Cb * a / (1 + L) ^ 2 := by ring
    rw [e, e2]
    have hKC : 0 ≤ K * Cb := by positivity
    gcongr
    linarith
  have hsum_maj : Summable fun k : ℕ =>
      K * Cb * (1 / (((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ^ 2)) := by
    refine Summable.mul_left _ ?_
    refine summable_of_sum_range_le (c := 2) (fun k => by positivity) ?_
    intro M
    rcases M with _ | M
    · simp
    rw [sum_range_succ']
    have := tele_sum (N := 1) le_rfl M
    have e : ∀ k : ℕ, 1 + k + 1 = k + 1 + 1 := fun k => by omega
    simp only [e, Nat.cast_one, Real.log_one, add_zero, div_one] at this
    have g0 : 1 / (((0 + 1 : ℕ) : ℝ) * (1 + Real.log ((0 + 1 : ℕ) : ℝ)) ^ 2) = 1 := by simp
    rw [g0]
    linarith
  have hsu : Summable u := Summable.of_norm_bounded hsum_maj (fun k => by
    rw [Real.norm_eq_abs]; exact hub k)
  set T : ℝ := ∑' k, u k with hT
  refine ⟨Real.eulerMascheroniConstant + T, 2 + K * Cb * 4 + K * Cb, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hab := abel_vR N
  -- the partial sum of `u`
  have hpart : ∑ m ∈ Ioc 0 N, Dp m / (m * (m + 1)) = ∑ k ∈ range N, u k := by
    rw [sum_Ioc_eq_range]
  -- tail
  have htail : |∑ k ∈ range N, u k - T| ≤ K * Cb * (1 / (1 + Real.log N)) := by
    have h := hsu.sum_add_tsum_nat_add N
    have hs2 : Summable fun k => u (k + N) := (summable_nat_add_iff N).mpr hsu
    have e : ∑ k ∈ range N, u k - T = -∑' k, u (k + N) := by rw [hT, ← h]; ring
    rw [e, abs_neg]
    have hsm2 : Summable fun k => K * Cb * (1 / (((k + N + 1 : ℕ) : ℝ) *
        (1 + Real.log ((k + N + 1 : ℕ) : ℝ)) ^ 2)) := (summable_nat_add_iff N).mpr hsum_maj
    refine (norm_tsum_le_tsum_norm hs2.norm).trans ?_
    refine (hs2.norm.tsum_le_tsum (fun k => ?_) hsm2).trans ?_
    · rw [Real.norm_eq_abs]; exact hub (k + N)
    · rw [tsum_mul_left]
      gcongr
      refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun M => ?_
      have := tele_sum hN M
      have e2 : ∀ k, N + k + 1 = k + N + 1 := fun k => by ring
      simp only [e2] at this
      exact this
  -- harmonic
  have hH : |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| ≤ 1 / N := by
    have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
    have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
    unfold Real.eulerMascheroniSeq at h1
    unfold Real.eulerMascheroniSeq' at h2
    rw [if_neg (by omega)] at h2
    have h3 : Real.log (N + 1) - Real.log N ≤ 1 / N := by
      rw [← Real.log_div (by positivity) hN0.ne']
      have := Real.log_le_sub_one_of_pos (x := (N + 1) / N) (by positivity)
      have e : (N + 1 : ℝ) / N - 1 = 1 / N := by field_simp; ring
      linarith
    rw [abs_le]; constructor <;> linarith
  -- D(N)/(N+1)
  have hDN : |Dp N / (N + 1)| ≤ K * Cb / (1 + Real.log N) := by
    have h1 := hD N hN
    have h2 := hexp (Real.log N) hlN
    have hL1 : 0 < 1 + Real.log N := by linarith
    have hsq : (1 + Real.log N) ≤ (1 + Real.log N) ^ 2 := by nlinarith
    have h3 : Cb / (1 + Real.log N) ^ 2 ≤ Cb / (1 + Real.log N) :=
      div_le_div_of_nonneg_left hCb hL1 hsq
    have h4 : |Dp N| ≤ K * N * (Cb / (1 + Real.log N)) := by
      refine h1.trans ?_
      have : 0 ≤ K * (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (h2.trans h3) this
    have hN1' : (0 : ℝ) < N + 1 := by positivity
    rw [abs_div, abs_of_pos hN1', div_le_iff₀ hN1']
    have : 0 ≤ K * Cb / (1 + Real.log N) := by positivity
    calc |Dp N| ≤ K * N * (Cb / (1 + Real.log N)) := h4
      _ = K * Cb / (1 + Real.log N) * N := by ring
      _ ≤ K * Cb / (1 + Real.log N) * (N + 1) := by nlinarith
  have h1N : 1 / (N : ℝ) ≤ 2 / (1 + Real.log N) := by
    rw [div_le_div_iff₀ hN0 (by positivity)]
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  rw [hab, hpart]
  have e : (harmonic N : ℝ) + Dp N / (N + 1) + ∑ k ∈ range N, u k - Real.log N -
      (Real.eulerMascheroniConstant + T) =
      ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) + Dp N / (N + 1) +
        (∑ k ∈ range N, u k - T) := by ring
  rw [e]
  have hpos : 0 < 1 + Real.log N := by linarith
  calc _ ≤ |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| + |Dp N / (N + 1)| +
        |∑ k ∈ range N, u k - T| := abs_add_three _ _ _
    _ ≤ 2 / (1 + Real.log N) + K * Cb / (1 + Real.log N) + K * Cb * (1 / (1 + Real.log N)) := by
        exact add_le_add (add_le_add (hH.trans h1N) hDN) htail
    _ = (2 + 2 * (K * Cb)) / (1 + Real.log N) := by ring
    _ ≤ (2 + K * Cb * 4 + K * Cb) / (1 + Real.log N) := by
        have : 0 ≤ K * Cb := by positivity
        exact div_le_div_of_nonneg_right (by linarith) hpos.le

end RamanujanTau.SelbergDelange3
