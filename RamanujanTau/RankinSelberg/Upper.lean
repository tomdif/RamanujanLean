/-
# Upper bound for the mean square of τ (Hecke–Parseval)

`exists_sum_tau_sq_div_le`: `∑_{n ≤ N} τ(n)² / n¹¹ ≤ K·N` for all `N`.

Route (no Eisenstein series): Parseval on the line `Im z = y` (`Parseval.lean`) gives
`∑ τ(n)² e^{-4πny} = ∫₀¹ |Δ(x+iy)|² dx`, and Mathlib's cusp-form bound `|Δ(z)| ≤ C y^{-6}`
(`CuspFormClass.exists_bound`) bounds the right side by `C² y^{-12}`. Taking `y = 1/(4πN)` gives
`∑_{n ≤ N} τ(n)² ≤ K N¹²`, and summation by parts (an induction with Bernoulli's inequality)
gives the weighted bound.
-/
import RamanujanTau.RankinSelberg.Parseval
import RamanujanTau.TauBound.Reduction

set_option autoImplicit false

namespace RamanujanTau.RankinSelberg

open Complex ModularForm MeasureTheory Finset
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

/-- `Δ` as a function on `ℍ` (Mathlib's discriminant cusp form). -/
noncomputable abbrev Δf : ℍ → ℂ := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)

/-- **Parseval for `Δ`**: `∑ τ(n)² e^{-4πny} = ∫₀¹ |Δ(x+iy)|² dx`. -/
theorem hasSum_tau_sq {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ((tau n : ℝ)) ^ 2 * Real.exp (-2 * π * y) ^ (2 * n))
      (∫ x in (0 : ℝ)..1, ‖Δf (hp hy x)‖ ^ 2) := by
  have h := hasSum_normSq_coeff (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ 12) hy
  refine h.congr_fun fun n => ?_
  rw [TauBound.qExpansion_discriminant_coeff_tau, Complex.norm_intCast, sq_abs]

/-- The integrand `|Δ(x+iy)|²` is bounded by `C / y¹²`. -/
theorem exists_normSq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℍ, ‖Δf z‖ ^ 2 ≤ C / z.im ^ 12 := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  refine ⟨C ^ 2, sq_nonneg _, fun z => ?_⟩
  have h := hC z
  have h6 : z.im ^ (((12 : ℤ) : ℝ) / 2) = z.im ^ 6 := by
    rw [show (((12 : ℤ) : ℝ) / 2) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h6] at h
  have h0 : 0 ≤ ‖Δf z‖ := norm_nonneg _
  calc ‖Δf z‖ ^ 2 ≤ (C / z.im ^ 6) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = C ^ 2 / z.im ^ 12 := by rw [div_pow, ← pow_mul]

/-- `∫₀¹ |Δ(x+iy)|² dx ≤ C / y¹²`. -/
theorem exists_integral_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ {y : ℝ} (hy : 0 < y),
    ∫ x in (0 : ℝ)..1, ‖Δf (hp hy x)‖ ^ 2 ≤ C / y ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := exists_normSq_le
  refine ⟨C, hC0, fun {y} hy => ?_⟩
  have hb : ∀ x, ‖Δf (hp hy x)‖ ^ 2 ≤ C / y ^ 12 := fun x => by
    have := hC (hp hy x); rwa [hp_im] at this
  have hcont : Continuous (fun x : ℝ => ‖Δf (hp hy x)‖ ^ 2) :=
    ((ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous.comp
      (continuous_hp hy)).norm.pow 2
  calc ∫ x in (0 : ℝ)..1, ‖Δf (hp hy x)‖ ^ 2 ≤ ∫ x in (0 : ℝ)..1, C / y ^ 12 :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
          intervalIntegrable_const fun x _ => hb x
    _ = C / y ^ 12 := by simp

/-- Partial sums of a nonnegative `HasSum` are at most the total. -/
lemma sum_le_of_hasSum {b : ℕ → ℝ} {S : ℝ} (h : HasSum b S) (hb : ∀ n, 0 ≤ b n)
    (s : Finset ℕ) : ∑ n ∈ s, b n ≤ S :=
  sum_le_hasSum s (fun n _ => hb n) h

/-- **Hecke–Parseval**: `∑_{n ≤ N} τ(n)² ≤ K N¹²`. -/
theorem exists_sum_tau_sq_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 ≤ K * (N : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_le
  refine ⟨Real.exp 1 * C * (4 * π) ^ 12, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set y : ℝ := 1 / (4 * π * N) with hydef
  have hy : 0 < y := by positivity
  have hS := hasSum_tau_sq hy
  -- each weight is at least `e^{-1}` for `n ≤ N`
  have hw : ∀ n ∈ Icc 1 N, Real.exp (-1) * ((tau n : ℝ)) ^ 2 ≤
      ((tau n : ℝ)) ^ 2 * Real.exp (-2 * π * y) ^ (2 * n) := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    rw [mul_comm, ← Real.exp_nat_mul]
    gcongr
    rw [hydef]
    have : ((2 * n : ℕ) : ℝ) * (-2 * π * (1 / (4 * π * N))) = -(n / N) := by
      push_cast; field_simp; ring
    rw [this, neg_le_neg_iff, div_le_one hNr]
    exact hnN
  have h1 : Real.exp (-1) * ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 ≤ C / y ^ 12 := by
    rw [mul_sum]
    refine (sum_le_sum hw).trans ?_
    exact (sum_le_of_hasSum hS (fun n => by positivity) _).trans (hC hy)
  have hy12 : C / y ^ 12 = C * (4 * π) ^ 12 * (N : ℝ) ^ 12 := by
    rw [hydef]; field_simp
  rw [hy12] at h1
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  calc ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2
      = Real.exp 1 * (Real.exp (-1) * ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp 1 * (C * (4 * π) ^ 12 * (N : ℝ) ^ 12) := by gcongr
    _ = Real.exp 1 * C * (4 * π) ^ 12 * (N : ℝ) ^ 12 := by ring

/-- Bernoulli: `1/x^k − 1/(x+1)^k ≤ k / x^{k+1}` for `x ≥ 1`. -/
lemma inv_pow_sub_inv_pow_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ k - 1 / (x + 1) ^ k ≤ k / x ^ (k + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hb := one_add_mul_le_pow (a := -1 / (x + 1)) (by
    rw [le_div_iff₀ hx1]; nlinarith) k
  have hxx : 1 + -1 / (x + 1) = x / (x + 1) := by field_simp; ring
  rw [hxx, div_pow] at hb
  have hu : 0 < x ^ k := by positivity
  have hv : 0 < (x + 1) ^ k := by positivity
  -- `1/u − 1/v = (1 − u/v)/u ≤ (k/(x+1))/u ≤ (k/x)/u`
  have e1 : 1 / x ^ k - 1 / (x + 1) ^ k = (1 - x ^ k / (x + 1) ^ k) / x ^ k := by
    field_simp
  rw [e1, pow_succ, div_le_div_iff₀ hu (by positivity)]
  have h2 : 1 - x ^ k / (x + 1) ^ k ≤ k / (x + 1) := by
    have : (k : ℝ) * (-1 / (x + 1)) = -(k / (x + 1)) := by ring
    linarith
  have h3 : (k : ℝ) / (x + 1) ≤ k / x := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hx0 (by linarith)
  have h4 : 1 - x ^ k / (x + 1) ^ k ≤ k / x := h2.trans h3
  calc (1 - x ^ k / (x + 1) ^ k) * (x ^ k * x) ≤ (k / x) * (x ^ k * x) := by
        gcongr
    _ = k * x ^ k := by field_simp

/-- **Summation by parts**: if `∑_{n ≤ N} bₙ ≤ K N^{k+1}` then `∑_{n ≤ N} bₙ/nᵏ ≤ (k+1) K N`. -/
theorem sum_div_pow_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (k : ℕ) {K : ℝ}
    (hA : ∀ N : ℕ, ∑ n ∈ Icc 1 N, b n ≤ K * (N : ℝ) ^ (k + 1)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ k ≤ (k + 1) * K * N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hK : 0 ≤ K := by
    have := (hA 1); simp at this; linarith [hb 1]
  -- invariant: `∑ bₙ/nᵏ ≤ A(N)/Nᵏ + k K N`
  have key : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ k ≤
      (∑ n ∈ Icc 1 N, b n) / (N : ℝ) ^ k + k * K * N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp; positivity
    | succ M hM ih =>
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
      set A := ∑ n ∈ Icc 1 M, b n
      have hA0 : 0 ≤ A := sum_nonneg fun n _ => hb n
      have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have hd := inv_pow_sub_inv_pow_le k hMr
      have hAM := hA M
      have hpos : (0 : ℝ) < (M : ℝ) ^ (k + 1) := by positivity
      -- `A (1/Mᵏ − 1/(M+1)ᵏ) ≤ k K`
      have hstep : A / (M : ℝ) ^ k - A / ((M : ℝ) + 1) ^ k ≤ k * K := by
        have e : A / (M : ℝ) ^ k - A / ((M : ℝ) + 1) ^ k =
            A * (1 / (M : ℝ) ^ k - 1 / ((M : ℝ) + 1) ^ k) := by ring
        rw [e]
        calc A * (1 / (M : ℝ) ^ k - 1 / ((M : ℝ) + 1) ^ k) ≤ A * (k / (M : ℝ) ^ (k + 1)) :=
              mul_le_mul_of_nonneg_left hd hA0
          _ ≤ K * (M : ℝ) ^ (k + 1) * (k / (M : ℝ) ^ (k + 1)) := by gcongr
          _ = k * K := by field_simp
      push_cast
      have e2 : (A + b (M + 1)) / ((M : ℝ) + 1) ^ k =
          A / ((M : ℝ) + 1) ^ k + b (M + 1) / ((M : ℝ) + 1) ^ k := add_div _ _ _
      rw [e2]
      nlinarith [ih, hstep]
  have hkey := key N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hAN := hA N
  have h1 : (∑ n ∈ Icc 1 N, b n) / (N : ℝ) ^ k ≤ K * N := by
    rw [div_le_iff₀ (by positivity)]
    calc ∑ n ∈ Icc 1 N, b n ≤ K * (N : ℝ) ^ (k + 1) := hAN
      _ = K * N * (N : ℝ) ^ k := by ring
  nlinarith

/-- **Upper bound** (Hecke–Parseval): `∑_{n ≤ N} τ(n)²/n¹¹ ≤ K N`. -/
theorem exists_sum_tau_sq_div_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
    ∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 ≤ K * N := by
  obtain ⟨K, hK0, hK⟩ := exists_sum_tau_sq_le
  refine ⟨12 * K, by positivity, fun N => ?_⟩
  have := sum_div_pow_le (b := fun n => ((tau n : ℝ)) ^ 2) (fun n => sq_nonneg _) 11
    (K := K) (fun N => by simpa using hK N) N
  norm_num at this ⊢
  linarith

end RamanujanTau.RankinSelberg
