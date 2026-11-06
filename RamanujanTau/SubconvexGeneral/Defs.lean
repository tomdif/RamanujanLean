/-
# Weight-`k` shifted-convolution hypothesis `SCSf f η B`

For a level-one cusp form `f` of weight `k` with coefficients `a_f(n)` we use the normalized
coefficients `λ_f(n) = Re a_f(n) / n^{(k−1)/2}` (`EigenformEdge.nlam`; for real coefficients this
is `a_f(n) n^{−(k−1)/2}`), and the sharp shifted sums `A_h(N) = Σ_{n≤N} λ_f(n) λ_f(n+h)`.

* `SCSf f η B`: `|A_h(N)| ≤ C (N+h)^{1−η} h^B` for all `h ≥ 1`, `N`.  For `f = Δ` it is literally
  `SubconvexityCond.ShiftedConvolutionBound η B` (`Check.lean`).
* `scsf_trivial`: `SCSf f 0 0` (Cauchy–Schwarz + Rankin, every weight).
* `sum_nlam_sq_div_le`: `Σ_{n≤N} λ_f(n)²/n ≤ A (2 + log N)` (Abel summation from Rankin); this
  replaces the `τ`-specific `MeanSquare.sum_tau_sq_rpow_le` in the diagonal.
-/
import RamanujanTau.SCSSharp2.Reduction
import RamanujanTau.EigenformEdge.Eigenform

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Real Finset
open RamanujanTau.HeckeConvexGeneral RamanujanTau.EigenformEdge RamanujanTau.SubconvexityCond
open scoped MatrixGroups

variable {k : ℕ}

/-- The generic sharp shifted sum `Σ_{n=1}^{N} l(n) l(n+h)` of a real sequence. -/
noncomputable def shS (l : ℕ → ℝ) (h N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, l n * l (n + h)

/-- **Weight-`k` shifted-convolution hypothesis `SCS_f(η, B)`.** -/
class SCSf (f : CuspForm 𝒮ℒ (k : ℤ)) (η B : ℝ) : Prop where
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shS (nlam f) h N| ≤ C * ((N : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B

lemma nrm_sq (n : ℕ) : nrm k n ^ 2 = (n : ℝ) ^ (k - 1) := by
  rw [nrm, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

lemma nlam_sq_le (f : CuspForm 𝒮ℒ (k : ℤ)) (n : ℕ) :
    nlam f n ^ 2 ≤ ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k - 1) := by
  rw [nlam, div_pow, nrm_sq]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 := Complex.abs_re_le_norm (coef f n)
  have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  simpa using this

/-- Rankin: `Σ_{n ≤ N} λ_f(n)² ≤ A N`. -/
lemma exists_sum_nlam_sq_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, nlam f n ^ 2 ≤ A * N := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_sq_div_le f hk
  exact ⟨A, hA0, fun N => (sum_le_sum fun n _ => nlam_sq_le f n).trans (hA N)⟩

/-- **Sanity check**: `SCS_f(0, 0)` holds for every `f` (Cauchy–Schwarz + Rankin). -/
theorem scsf_trivial (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : SCSf f 0 0 := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_nlam_sq_le f hk
  refine ⟨⟨A, hA0, fun h N hh => ?_⟩⟩
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (nlam f) (fun n => nlam f (n + h))
  have h1 := hA N
  have h2 : ∑ n ∈ Icc 1 N, nlam f (n + h) ^ 2 ≤ A * ((N : ℝ) + h) := by
    refine (sum_shift_le (fun n => nlam f n ^ 2) (fun n => sq_nonneg _) h N).trans ?_
    have := hA (N + h); push_cast at this; exact this
  have hNh : (N : ℝ) ≤ N + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : (shS (nlam f) h N) ^ 2 ≤ (A * ((N : ℝ) + h)) ^ 2 := by
    unfold shS
    refine hcs.trans ?_
    have e : (A * ((N : ℝ) + h)) ^ 2 = (A * ((N : ℝ) + h)) * (A * ((N : ℝ) + h)) := sq _
    rw [e]
    refine mul_le_mul (h1.trans (by nlinarith)) h2 (sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity)
  have := sq_le_sq.1 hsq
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ A * ((N : ℝ) + h))] at this
  simpa using this

/-- Monotonicity of `SCS_f`. -/
theorem SCSf.mono {f : CuspForm 𝒮ℒ (k : ℤ)} {η B η' B' : ℝ} (h : SCSf f η B)
    (hη : η' ≤ η) (hB : B ≤ B') : SCSf f η' B' := by
  obtain ⟨C, hC0, hC⟩ := h.bound
  refine ⟨⟨C, hC0, fun j N hj => (hC j N hj).trans ?_⟩⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hNj : (1 : ℝ) ≤ N + j := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  gcongr

/-- **Diagonal** (any real sequence with Rankin's bound): `Σ_{n≤N} l(n)²/n ≤ A (2 + log N)`. -/
lemma sum_sq_div_le_log (l : ℕ → ℝ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ N : ℕ, ∑ n ∈ Icc 1 N, l n ^ 2 ≤ A * N) (N : ℕ) :
    ∑ n ∈ Icc 1 N, l n ^ 2 / n ≤ A * (2 + Real.log N) := by
  have e : ∑ n ∈ Icc 1 N, l n ^ 2 / n = ∑ n ∈ Icc 1 N, l n ^ 2 * (1 / (n : ℝ)) := by
    refine sum_congr rfl fun n _ => by ring
  rw [e, abel_Icc]
  have hS : ∀ n, 0 ≤ ∑ j ∈ Icc 1 n, l j ^ 2 := fun n => sum_nonneg fun _ _ => sq_nonneg _
  have t1 : (∑ j ∈ Icc 1 N, l j ^ 2) * (1 / ((N + 1 : ℕ) : ℝ)) ≤ A := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    refine (hA N).trans ?_
    push_cast; nlinarith
  have t2 : ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 n, l j ^ 2) * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) ≤
      ∑ n ∈ Icc 1 N, A * (1 / (n : ℝ)) := by
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hd : 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) = 1 / ((n : ℝ) * (n + 1)) := by
      push_cast; field_simp; ring
    rw [hd]
    calc (∑ j ∈ Icc 1 n, l j ^ 2) * (1 / ((n : ℝ) * (n + 1))) ≤
        (A * n) * (1 / ((n : ℝ) * (n + 1))) :=
          mul_le_mul_of_nonneg_right (hA n) (by positivity)
      _ = A * (1 / ((n : ℝ) + 1)) := by field_simp
      _ ≤ A * (1 / (n : ℝ)) := by
          gcongr; linarith
  have hH : ∑ n ∈ Icc 1 N, A * (1 / (n : ℝ)) ≤ A * (1 + Real.log N) := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    have := RamanujanTau.MeanSquare.H_le_one_add_log N
    unfold RamanujanTau.MeanSquare.H at this; exact this
  linarith

lemma sum_nlam_sq_div_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, nlam f n ^ 2 / n ≤ A * (2 + Real.log N) := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_nlam_sq_le f hk
  exact ⟨A, hA0, sum_sq_div_le_log (nlam f) hA0 hA⟩

end RamanujanTau.SubconvexGeneral
