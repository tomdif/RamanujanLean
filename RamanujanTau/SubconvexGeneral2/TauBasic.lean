/-
# Weight-`k` Tauberian chain, part 1: coefficients, Rankin short sums, trivial bounds

Weight-`k` copies of `SCSProof.Tauber4/Tauber5`, `SCSProof.Gbounds2.abs_laplace_le` (summability
only) and `SCSSharp.rankin_short'`, `SCSSharp.Asum_cs`, for a level-one cusp form `f` of weight `k`.

* `aT f h n = Re a(n) · Re a(n+h)` (for real coefficients this is `conj a(n) a(n+h)`);
* `lsqT f n = |a(n)|² / n^{k−1}` (plays the role of `λ(n)²`), `SlamT f N = Σ_{n≤N} lsqT f n`;
* `AsumT f h N = Σ_{n≤N} aT f h n`.
-/
import RamanujanTau.SCSSharp.Final
import RamanujanTau.SubconvexGeneral.GboundsF
import RamanujanTau.RankinExact.Main

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open Finset Complex
open RamanujanTau.HeckeConvexGeneral RamanujanTau.SubconvexGeneral
open scoped MatrixGroups Real ComplexConjugate

variable {k : ℕ}

/-- `a_n = Re a(n) Re a(n+h)`. -/
noncomputable def aT (f : CuspForm 𝒮ℒ (k : ℤ)) (h n : ℕ) : ℝ := (coef f n).re * (coef f (n + h)).re

/-- `|a_n|`. -/
noncomputable def aabsT (f : CuspForm 𝒮ℒ (k : ℤ)) (h n : ℕ) : ℝ := |aT f h n|

/-- `|a(n)|² / n^{k−1}`. -/
noncomputable def lsqT (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) : ℝ := ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1)

/-- Rankin partial sums. -/
noncomputable def SlamT (f : CuspForm 𝒮ℒ (k : ℤ)) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, lsqT f n

/-- `A(N) = Σ_{n≤N} a_n`. -/
noncomputable def AsumT (f : CuspForm 𝒮ℒ (k : ℤ)) (h N : ℕ) : ℝ := ∑ n ∈ range (N + 1), aT f h n

variable (f : CuspForm 𝒮ℒ (k : ℤ))

lemma aabsT_nonneg (h n : ℕ) : 0 ≤ aabsT f h n := abs_nonneg _

lemma abs_aT (h n : ℕ) : |aT f h n| = aabsT f h n := rfl

lemma aT_zero (h : ℕ) : aT f h 0 = 0 := by simp [aT, coef_zero]

lemma aabsT_zero (h : ℕ) : aabsT f h 0 = 0 := by simp [aabsT, aT_zero]

lemma lsqT_nonneg (n : ℕ) : 0 ≤ lsqT f n := by unfold lsqT; positivity

lemma lsqT_zero : lsqT f 0 = 0 := by simp [lsqT, coef_zero]

lemma re_sq_le (n : ℕ) : (coef f n).re ^ 2 ≤ ‖coef f n‖ ^ 2 := by
  have h1 := Complex.abs_re_le_norm (coef f n)
  have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  simpa using this

lemma coef_sq_eq (n : ℕ) : ‖coef f n‖ ^ 2 = lsqT f n * (n : ℝ) ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lsqT, coef_zero]
  have : (0 : ℝ) < (n : ℝ) ^ (k - 1) := by positivity
  unfold lsqT; field_simp

lemma aabsT_le (h n : ℕ) : aabsT f h n ≤ (‖coef f n‖ ^ 2 + ‖coef f (n + h)‖ ^ 2) / 2 := by
  unfold aabsT aT
  rw [abs_mul]
  have h1 := Complex.abs_re_le_norm (coef f n)
  have h2 := Complex.abs_re_le_norm (coef f (n + h))
  have a0 := abs_nonneg (coef f n).re
  have b0 := abs_nonneg (coef f (n + h)).re
  nlinarith [sq_nonneg (‖coef f n‖ - ‖coef f (n + h)‖), mul_le_mul h1 h2 b0 (norm_nonneg _)]

lemma aabsT_le_lsq (h n : ℕ) :
    aabsT f h n ≤ (lsqT f n + lsqT f (n + h)) / 2 * ((n : ℝ) + h) ^ (k - 1) := by
  refine (aabsT_le f h n).trans ?_
  rw [coef_sq_eq, coef_sq_eq]
  have h1 : (n : ℝ) ^ (k - 1) ≤ ((n : ℝ) + h) ^ (k - 1) := by
    gcongr; have := Nat.cast_nonneg (α := ℝ) h; linarith
  have h2 : ((n + h : ℕ) : ℝ) ^ (k - 1) = ((n : ℝ) + h) ^ (k - 1) := by push_cast; ring
  rw [h2]
  have := lsqT_nonneg f n
  nlinarith

lemma sum_range_eq_SlamT (M : ℕ) : ∑ n ∈ range (M + 1), lsqT f n = SlamT f M := by
  rw [sum_range_succ', lsqT_zero, SlamT, RamanujanTau.SCSProof.Icc_one_eq_map, sum_map]
  simp

lemma sum_lsqT_shift (h N : ℕ) :
    ∑ n ∈ range (N + 1), lsqT f (n + h) ≤ SlamT f (N + h) := by
  rw [← sum_range_eq_SlamT]
  calc ∑ n ∈ range (N + 1), lsqT f (n + h) = ∑ m ∈ (range (N + 1)).map (addRightEmbedding h),
        lsqT f m := by rw [sum_map]; rfl
    _ ≤ ∑ m ∈ range (N + h + 1), lsqT f m := by
        refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun _ _ _ => lsqT_nonneg f _)
        simp only [mem_map, mem_range, addRightEmbedding_apply] at hm ⊢
        obtain ⟨n, hn, rfl⟩ := hm; omega

lemma exists_SlamT_le (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, SlamT f N ≤ A * N :=
  exists_sum_sq_div_le f hk

/-- Trivial bound `Σ_{n≤N} |a_n| ≤ A (N+h)^k`. -/
theorem sum_aabsT_le (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧ ∀ h N : ℕ,
    ∑ n ∈ range (N + 1), aabsT f h n ≤ A * ((N : ℝ) + h) ^ k := by
  obtain ⟨A, hA0, hA⟩ := exists_SlamT_le f hk
  refine ⟨A, hA0, fun h N => ?_⟩
  have hNh : (0 : ℝ) ≤ (N : ℝ) + h := by positivity
  have hk' : ((N : ℝ) + h) * ((N : ℝ) + h) ^ (k - 1) = ((N : ℝ) + h) ^ k := by
    rw [← pow_succ']; congr 1; omega
  calc ∑ n ∈ range (N + 1), aabsT f h n
      ≤ ∑ n ∈ range (N + 1), (lsqT f n + lsqT f (n + h)) / 2 * ((N : ℝ) + h) ^ (k - 1) := by
        refine sum_le_sum fun n hn => (aabsT_le_lsq f h n).trans ?_
        have : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
        have := lsqT_nonneg f n; have := lsqT_nonneg f (n + h)
        gcongr
    _ = (∑ n ∈ range (N + 1), lsqT f n + ∑ n ∈ range (N + 1), lsqT f (n + h)) / 2 *
          ((N : ℝ) + h) ^ (k - 1) := by rw [← sum_mul, ← sum_div, sum_add_distrib]
    _ ≤ (SlamT f N + SlamT f (N + h)) / 2 * ((N : ℝ) + h) ^ (k - 1) := by
        rw [sum_range_eq_SlamT]; gcongr; exact sum_lsqT_shift f h N
    _ ≤ (A * N + A * ((N : ℝ) + h)) / 2 * ((N : ℝ) + h) ^ (k - 1) := by
        gcongr
        · exact hA N
        · have := hA (N + h); push_cast at this; exact this
    _ ≤ A * ((N : ℝ) + h) * ((N : ℝ) + h) ^ (k - 1) := by
        have : (N : ℝ) ≤ N + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
        gcongr; nlinarith
    _ = A * ((N : ℝ) + h) ^ k := by rw [mul_assoc, hk']

/-- Summability of `Σ |a_n| e^{−nσ}`. -/
lemma summable_aabsT (h : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => aabsT f h n * Real.exp (-n * σ)) := by
  obtain ⟨C₀, -, hT⟩ := coef_sq_laplace f
  have hs := (hT σ hσ).1
  have hs2 : Summable (fun n : ℕ => ‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ)) :=
    (summable_nat_add_iff h).2 hs
  have e2 : ∀ n : ℕ, ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ) =
      Real.exp (h * σ) * (‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ)) := by
    intro n
    rw [mul_left_comm, ← Real.exp_add]; congr 2; push_cast; ring
  have hs2' : Summable (fun n : ℕ => ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) := by
    simp_rw [e2]; exact hs2.mul_left _
  have hmaj : Summable (fun n : ℕ => (‖coef f n‖ ^ 2 * Real.exp (-n * σ) +
      ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) / 2) := (hs.add hs2').div_const 2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (aabsT_nonneg f h n) (Real.exp_pos _).le)
    (fun n => ?_) hmaj
  have := aabsT_le f h n
  have he := Real.exp_pos (-n * σ)
  calc aabsT f h n * Real.exp (-n * σ) ≤ (‖coef f n‖ ^ 2 + ‖coef f (n + h)‖ ^ 2) / 2 *
        Real.exp (-n * σ) := by gcongr
    _ = _ := by ring

/-- For real coefficients, `G^f_h(W) = Σ a_n e^{−nW}`. -/
lemma GhF_eq (hreal : ∀ n, (coef f n).im = 0) (h : ℕ) (W : ℂ) :
    GhF f h W = ∑' n : ℕ, (aT f h n : ℂ) * cexp (-(n : ℂ) * W) := by
  unfold GhF
  congr 1; funext n
  have e : ∀ m, coef f m = ((coef f m).re : ℂ) := fun m => Complex.ext (by simp) (by simp [hreal m])
  rw [e n, e (n + h), Complex.conj_ofReal]
  unfold aT; push_cast; simp

lemma summable_aT_term (h : ℕ) {W : ℂ} (hW : 0 < W.re)
    (hs : Summable (fun n : ℕ => aabsT f h n * Real.exp (-n * W.re))) :
    Summable (fun n : ℕ => (aT f h n : ℂ) * cexp (-(n : ℂ) * W)) := by
  refine Summable.of_norm ?_
  have e : ∀ n : ℕ, ‖(aT f h n : ℂ) * cexp (-(n : ℂ) * W)‖ = aabsT f h n * Real.exp (-n * W.re) := by
    intro n
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have : (-(n : ℂ) * W).re = -n * W.re := by simp
    rw [this]; rfl
  simp_rw [e]; exact hs

/-- **Rankin short sums** with exponent `1 − 1/22`. -/
theorem rankin_shortT : ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ a b : ℕ, a ≤ b →
    SlamT f b - SlamT f a ≤ c * ((b : ℝ) - a) + 2 * C * (b : ℝ) ^ (1 - SCSSharp.ηs) := by
  obtain ⟨C, hC35⟩ := RankinExact.rankinSelberg_exact_general f
  set c := RankinSelbergGeneral.rsConst f
  have hC0 : 0 ≤ C := by
    have := hC35 1 le_rfl
    simp at this
    exact le_trans (abs_nonneg _) (by simpa using this)
  have hη2 := SCSSharp.ηs_le
  have hb : ∀ N : ℕ, |SlamT f N - c * N| ≤ C * (N : ℝ) ^ (1 - SCSSharp.ηs) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [SlamT]
      have : (0 : ℝ) ^ (1 - SCSSharp.ηs) = 0 := Real.zero_rpow (by linarith)
      rw [this]; simp
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      refine (le_of_eq ?_).trans ((hC35 N hN).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hC0))
      rfl
  refine ⟨|c|, C, abs_nonneg _, hC0, fun a b hab => ?_⟩
  have h1 := hb b
  have h2 := hb a
  rw [abs_le] at h1 h2
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hpow : (a : ℝ) ^ (1 - SCSSharp.ηs) ≤ (b : ℝ) ^ (1 - SCSSharp.ηs) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hab' (by linarith)
  have hcab : c * ((b : ℝ) - a) ≤ |c| * ((b : ℝ) - a) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  nlinarith

end RamanujanTau.SubconvexGeneral2
