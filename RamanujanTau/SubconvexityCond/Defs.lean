/-
# The shifted-convolution hypothesis `ShiftedConvolutionBound η B`

Normalization `λ(n) = τ(n) n^{−11/2}` (so `L(Δ,6+it) = ∑ λ(n) n^{−1/2−it}`).  The hypothesis is a
bound for the *sharp* shifted partial sums

    A_h(N) = ∑_{n=1}^{N} λ(n) λ(n+h)

of the form `|A_h(N)| ≤ C (N+h)^{1−η} h^B` for all `h ≥ 1`, `N ≥ 0`.  It is a statement about the
coefficients `τ(n)` only — it mentions neither `L(Δ,s)` nor any mean value of it.

* `shiftedConvolutionBound_trivial`: it holds with `η = 0`, `B = 0` (Cauchy–Schwarz + Rankin).
* `ShiftedConvolutionBound.mono`: smaller `η` / larger `B` are weaker.
* `subconvexDelta η B = η/(10B+24)`: the exponent saving delivered by `SubconvexityCond.Main`;
  `subconvexDelta 0 B = 0` (no saving = convexity).
-/
import RamanujanTau.MeanSquare.Approx
import RamanujanTau.HeckeConvex.Convex

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset

/-- The normalized Hecke eigenvalue `λ(n) = τ(n) n^{−11/2}`. -/
noncomputable def lam (n : ℕ) : ℝ := (tau n : ℝ) * (n : ℝ) ^ (-(11 / 2 : ℝ))

/-- The sharp shifted partial sum `A_h(N) = ∑_{n=1}^{N} λ(n) λ(n+h)`. -/
noncomputable def shiftSum (h N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, lam n * lam (n + h)

/-- **Shifted-convolution hypothesis `SCS(η, B)`**: there is `C` with
`|∑_{n ≤ N} λ(n) λ(n+h)| ≤ C (N+h)^{1−η} h^B` for all `h ≥ 1` and all `N`.

For `h ≤ N` this is the classical form `≪ N^{1−η} h^B`; for `h > N` and `B ≥ η` it is implied by
the trivial (Cauchy–Schwarz + Rankin) bound.  Literature: Selberg (1965), Good (1981): for every
`η < 1/3` it holds with some fixed `B` (e.g. `B = 1`); see `docs/SUBCONVEXITY_COND.md`. -/
class ShiftedConvolutionBound (η B : ℝ) : Prop where
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - η) * (h : ℝ) ^ B

/-- The exponent saving `δ(η,B) = η/(10B+24)`. -/
noncomputable def subconvexDelta (η B : ℝ) : ℝ := η / (10 * B + 24)

@[simp] lemma subconvexDelta_zero (B : ℝ) : subconvexDelta 0 B = 0 := by simp [subconvexDelta]

lemma subconvexDelta_pos {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) : 0 < subconvexDelta η B := by
  unfold subconvexDelta; positivity

lemma lam_sq (n : ℕ) : lam n ^ 2 = ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lam, tau_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lam, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(11 / 2 : ℝ))) 2, ← Real.rpow_mul hn0.le,
    show (-(11 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((11 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
    Real.rpow_natCast, div_eq_mul_inv]

/-- Rankin: `∑_{n ≤ N} λ(n)² ≤ A N`. -/
lemma exists_sum_lam_sq_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, ∑ n ∈ Icc 1 N, lam n ^ 2 ≤ A * N := by
  obtain ⟨A, hA0, hA⟩ := RamanujanTau.HeckeConvex.exists_sum_sq_div_le
  exact ⟨A, hA0, fun N => by simp_rw [lam_sq]; exact hA N⟩

lemma sum_shift_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (h N : ℕ) :
    ∑ n ∈ Icc 1 N, f (n + h) ≤ ∑ n ∈ Icc 1 (N + h), f n := by
  have e : ∑ n ∈ Icc 1 N, f (n + h) = ∑ m ∈ (Icc 1 N).map (addRightEmbedding h), f m := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hf _)
  intro m hm
  simp only [Finset.mem_map, Finset.mem_Icc, addRightEmbedding_apply] at hm
  obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := hm
  simp only [Finset.mem_Icc]; omega

/-- **Sanity check**: `SCS(0, 0)` holds unconditionally (Cauchy–Schwarz + Rankin). -/
theorem shiftedConvolutionBound_trivial : ShiftedConvolutionBound 0 0 := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_lam_sq_le
  refine ⟨⟨A, hA0, fun h N hh => ?_⟩⟩
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) lam (fun n => lam (n + h))
  have h1 := hA N
  have h2 : ∑ n ∈ Icc 1 N, lam (n + h) ^ 2 ≤ A * ((N : ℝ) + h) := by
    refine (sum_shift_le (fun n => lam n ^ 2) (fun n => sq_nonneg _) h N).trans ?_
    have := hA (N + h); push_cast at this; exact this
  have hNh : (N : ℝ) ≤ N + h := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : (shiftSum h N) ^ 2 ≤ (A * ((N : ℝ) + h)) ^ 2 := by
    unfold shiftSum
    refine hcs.trans ?_
    have e : (A * ((N : ℝ) + h)) ^ 2 = (A * ((N : ℝ) + h)) * (A * ((N : ℝ) + h)) := sq _
    rw [e]
    refine mul_le_mul (h1.trans (by nlinarith)) h2 (sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity)
  have := sq_le_sq.1 hsq
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ A * ((N : ℝ) + h))] at this
  simpa using this

/-- Monotonicity: `SCS(η, B)` implies `SCS(η', B')` for `η' ≤ η`, `B ≤ B'`. -/
theorem ShiftedConvolutionBound.mono {η B η' B' : ℝ} (h : ShiftedConvolutionBound η B)
    (hη : η' ≤ η) (hB : B ≤ B') : ShiftedConvolutionBound η' B' := by
  obtain ⟨C, hC0, hC⟩ := h.bound
  refine ⟨⟨C, hC0, fun k N hk => (hC k N hk).trans ?_⟩⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNk : (1 : ℝ) ≤ N + k := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  gcongr

end RamanujanTau.SubconvexityCond
