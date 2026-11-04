/-
# Abel summation: convergence of `Σ c_k g_k` from partial-sum growth of `c` and smoothness of `g`

`Σ_{k<N} c_k g_k = S_N g_N − Σ_{k<N} S_{k+1}(g_{k+1} − g_k)` with `S_N = Σ_{k<N} c_k` (`abel_identity`);
hence, if `Σ ‖S_{k+1}‖ |g_{k+1} − g_k| < ∞` and `S_N g_N → 0`, the partial sums converge (`tendsto_of_abel`).
No absolute convergence of `Σ c_k g_k` is assumed or implied.
-/
import Mathlib

set_option autoImplicit false

namespace AndrewsDragonette
open Filter Topology Finset

lemma abel_identity (c : ℕ → ℂ) (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range N, c k * g k =
      (∑ k ∈ range N, c k) * g N -
        ∑ k ∈ range N, (∑ j ∈ range (k + 1), c j) * ((g (k + 1) : ℂ) - g k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun k => c k * (g k : ℂ)), ih,
      sum_range_succ (fun k => (∑ j ∈ range (k + 1), c j) * ((g (k + 1) : ℂ) - g k)),
      sum_range_succ c N]
    ring

theorem tendsto_of_abel (c : ℕ → ℂ) (g : ℕ → ℝ)
    (h1 : Summable (fun k => ‖∑ j ∈ range (k + 1), c j‖ * |g (k + 1) - g k|))
    (h2 : Tendsto (fun N => (∑ k ∈ range N, c k) * (g N : ℂ)) atTop (𝓝 0)) :
    ∃ L : ℂ, Tendsto (fun N => ∑ k ∈ range N, c k * g k) atTop (𝓝 L) := by
  set u : ℕ → ℂ := fun k => (∑ j ∈ range (k + 1), c j) * ((g (k + 1) : ℂ) - g k) with hu_def
  have hu : Summable u := by
    refine Summable.of_norm (h1.congr (fun k => ?_))
    simp only [hu_def, norm_mul]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨0 - ∑' k, u k, ?_⟩
  refine (h2.sub hu.hasSum.tendsto_sum_nat).congr (fun N => ?_)
  rw [abel_identity]

end AndrewsDragonette
