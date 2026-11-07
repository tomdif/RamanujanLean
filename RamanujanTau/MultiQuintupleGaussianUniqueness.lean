/-
# Uniqueness of the coefficients of a convergent Gaussian expansion
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace Ramanujan.MultiQuintuple
open scoped Topology NNReal ENNReal
open Filter

/-- Zeros on a real interval accumulating at zero determine every complex
coefficient, provided the series converges absolutely at a positive radius. -/
theorem scalar_coefficients_zero_of_real_interval
    (c : ℕ → ℂ) (r : ℝ) (hr : 0 < r)
    (hs : Summable (fun n => ‖c n‖*r^n))
    (hz : ∀ q : ℝ, 0 < q → q < r → ∑' n, c n*(q : ℂ)^n=0) :
    ∀ n, c n=0 := by
  let P := FormalMultilinearSeries.ofScalars ℂ c
  let rNN : NNReal := ⟨r,hr.le⟩
  have hrad : (rNN : ENNReal) ≤ P.radius := by
    apply P.le_radius_of_summable
    simpa [P,FormalMultilinearSeries.ofScalars_norm] using hs
  have hpos : 0 < P.radius := lt_of_lt_of_le (by exact_mod_cast hr) hrad
  have hf := (P.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hP : P=0 := by
    by_contra hn
    have hlocal := hf.locally_ne_zero hn
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp hlocal)
    let q := min ε r/2
    have hq : 0 < q := by dsimp [q]; positivity
    have hqr : q < r := by dsimp [q]; have := min_le_right ε r; linarith
    have hqe : q < ε := by dsimp [q]; have := min_le_left ε r; linarith
    have hdist : dist (q : ℂ) 0 < ε := by simpa [Complex.norm_real,abs_of_pos hq] using hqe
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hne := hball (q : ℂ) hdist hq0
    apply hne
    change FormalMultilinearSeries.ofScalarsSum c (q : ℂ)=0
    simpa [FormalMultilinearSeries.ofScalars_sum_eq,smul_eq_mul] using hz q hq hqr
  have hc : c=0 := (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).mp hP
  exact fun n => congrFun hc n

theorem gaussian_coefficients_zero
    (c : ℕ → ℂ) (s0 : ℝ) (hs0 : 0 < s0)
    (hs : Summable (fun n => ‖c n‖*Real.exp (-s0*(n : ℝ))))
    (hz : ∀ s : ℝ, 0 < s → ∑' n, c n*(Real.exp (-s*(n : ℝ)) : ℂ)=0) :
    ∀ n, c n=0 := by
  apply scalar_coefficients_zero_of_real_interval c (Real.exp (-s0)) (Real.exp_pos _)
  · simpa only [mul_comm (-s0),Real.exp_nat_mul] using hs
  · intro q hq hqr
    have hq1 : q < 1 := lt_trans hqr (Real.exp_lt_one_iff.mpr (by linarith))
    have hslog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
    have he : ∀ n : ℕ, (q : ℂ)^n=(Real.exp (-(-Real.log q)*(n : ℝ)) : ℂ) := by
      intro n
      rw [neg_neg,mul_comm,Real.exp_nat_mul,Real.exp_log hq]
      simp
    simp_rw [he]
    exact hz (-Real.log q) hslog

theorem tsum_zero_of_fiber_sums_zero {ι κ : Type*} (f : ι → ℂ) (d : ι → κ)
    (hf : ∀ k, (∑' x : d ⁻¹' {k}, f x)=0) : (∑' x, f x)=0 := by
  by_cases hs : Summable f
  · have hh := hs.hasSum.tsum_fiberwise d
    simpa only [hf,tsum_zero] using hh.tsum_eq.symm
  · exact tsum_eq_zero_of_not_summable hs

/-- An absolutely convergent Gaussian identity separates every complete
integer norm shell. No bound on the number of vectors in a shell is used. -/
theorem gaussian_fiber_sums_zero {ι : Type*} (N : ι → ℕ) (A : ι → ℂ)
    (hs : ∀ s : ℝ, 0 < s → Summable (fun x => A x*(Real.exp (-s*(N x : ℝ)) : ℂ)))
    (hz : ∀ s : ℝ, 0 < s → (∑' x, A x*(Real.exp (-s*(N x : ℝ)) : ℂ))=0) :
    ∀ d : ℕ, (∑' x : N ⁻¹' {d}, A x)=0 := by
  let c := fun d : ℕ => ∑' x : N ⁻¹' {d}, A x
  have hfactor (s : ℝ) (d : ℕ) :
      (∑' x : N ⁻¹' {d}, A x*(Real.exp (-s*(N x : ℝ)) : ℂ)) =
        c d*(Real.exp (-s*(d : ℝ)) : ℂ) := by
    have he : (fun x : N ⁻¹' {d} => A x*(Real.exp (-s*(N x : ℝ)) : ℂ)) =
        (fun x : N ⁻¹' {d} => A x*(Real.exp (-s*(d : ℝ)) : ℂ)) := by
      funext x
      have hx : N x=d := x.property
      rw [hx]
    rw [he,tsum_mul_right]
  have hgroup (s : ℝ) (hs0 : 0 < s) :
      HasSum (fun d => c d*(Real.exp (-s*(d : ℝ)) : ℂ)) 0 := by
    have hh := (hs s hs0).hasSum.tsum_fiberwise N
    simpa only [hfactor,hz s hs0] using hh
  apply gaussian_coefficients_zero c 1 (by norm_num)
  · have hh := (hgroup 1 (by norm_num)).summable.norm
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hh
  · intro s hs0
    exact (hgroup s hs0).tsum_eq

end Ramanujan.MultiQuintuple
