/-
# Rankin's theorem exactly: error `O(N^{3/5})`, for the weight-`(m+1)` data

Same pipeline as `RankinLandau.landau_of_RSDataM`, with two changes:

* both kernels sharp: `J₁ ≪ y^{9/8}` (`α = 1/8`) and `J₁₈ ≪ y^{111/8}` (`σ = −33/8`), from
  `kernel_sharp` (the bent contour for general `j`);
* the ε-free core `landau_sharp` with `k = 18`, `θ = μ = 3/5`: then
  `1 + α + μα = 6/5 = 2θ` and `k + σ + μσ = 57/5 = (k+1)θ`, both with equality.

`ε = 1/8` appears only in the hypothesis structure `LandauHyp` (summability, used to
bootstrap the linear bound); it does not enter the exponent.
-/
import RamanujanTau.RankinExact.Core
import RamanujanTau.RankinExact.Contour
import RamanujanTau.RankinLandau.Final

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinLandau
open RamanujanTau.RankinSharp (chi chi_nonneg LSeriesSummable_chi LSeries_chi coe_mul_apply
  sum_a_eq_mobius mobius_transfer summable_of_LSeriesSummable LSeriesSummable_of_one_lt)
open ArithmeticFunction

section Main

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ}

/-- **Rankin's exponent `3/5` exactly** for the weight-`(m+1)` Rankin–Selberg data
(unconditional; no `ε`). -/
theorem landau_exact_of_RSDataM (hm : 2 ≤ m) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) (hκ : 0 ≤ κ)
    (d : RSDataM m a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConstM m * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  have hm1 : 1 ≤ m := by omega
  -- the twisted coefficients `b = χ * a`
  set aF : ArithmeticFunction ℝ := ⟨a, ha0⟩ with haF
  set b : ArithmeticFunction ℝ := chi * aF with hbdef
  have hb : ∀ n, 0 ≤ b n := by
    intro n; rw [hbdef, mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (chi_nonneg _) (ha _)
  have hb0 : b 0 = 0 := by simp
  have hbconv : (fun n => ((b n : ℝ) : ℂ)) =
      LSeries.convolution (fun n => (chi n : ℂ)) (fun n => (a n : ℂ)) := by
    funext n; rw [hbdef, coe_mul_apply]; rfl
  have hbS : ∀ w : ℂ, 1 < w.re → LSeriesSummable (fun n => ((b n : ℝ) : ℂ)) w := by
    intro w hw
    rw [hbconv]
    exact (LSeriesSummable_chi (by linarith)).convolution (LSeriesSummable_of_one_lt habs hw)
  have hbL : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => ((b n : ℝ) : ℂ)) w = riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w := by
    intro w hw
    rw [hbconv, LSeries_convolution' (LSeriesSummable_chi (by linarith))
      (LSeriesSummable_of_one_lt habs (by linarith)), LSeries_chi (by linarith)]
  have hsumA : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_one_lt habs (by simp; norm_num)
  -- parameters: `k = 18`, `α = 1/8`, `σ = −33/8`, `ε = 1/8`, `θ = μ = 3/5`
  set ξ : ℝ := 1 / 8 with hξ
  have hξ0 : 0 < ξ := by norm_num [hξ]
  set k : ℕ := 18 with hkdef
  have hk18 : 18 ≤ k := le_rfl
  set α : ℝ := 1 / 8 with hα
  set σ : ℝ := -33 / 8 with hσ
  have hσε : σ + ξ ≤ 0 := by norm_num [hσ, hξ]
  have hkσ : 0 ≤ (k : ℝ) + σ := by norm_num [hσ, hkdef]
  -- kernel bounds (both sharp)
  obtain ⟨K₁, hK₁⟩ := kernel_sharp hm1 0
  obtain ⟨Kk, hKk⟩ := kernel_sharp hm1 17
  set A : ℝ := |K₁| + |Kk| with hA
  have hKkp : ∀ y : ℝ, 1 ≤ y → ‖Jc m k (1 / 2) y‖ ≤ |Kk| * y ^ ((k : ℝ) + σ) := by
    intro y hy
    have h := hKk y hy
    rw [show (((9 + 6 * 17 : ℕ) : ℝ) / 8) = (k : ℝ) + σ by norm_num [hσ, hkdef]] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  -- the constants
  set c : ℝ := ((k : ℝ) + 1) * (κ * Rk m k 1).re with hc
  set d' : ℝ := -(κ * Rk m k 0).re with hd'
  have hc_eq : c = cB m κ := by
    rw [hc, Rk_one]
    unfold cB rsConstM
    have hpi := Real.pi_pos
    have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    simp only [← ofReal_mul, ofReal_re]
    field_simp
    ring
  have hc0 : 0 ≤ c := by rw [hc_eq]; unfold cB rsConstM; positivity
  -- the Landau hypotheses
  have hsummε : Summable fun n : ℕ => b n * (n : ℝ) ^ (-1 - ξ) := by
    have := summable_of_LSeriesSummable hb hb0 (hbS ((1 + ξ : ℝ) : ℂ) (by simp; linarith))
    simpa [show -(1 + ξ) = -1 - ξ by ring] using this
  have hJ1 : ∀ y, 1 ≤ y → |Jr m 1 y| ≤ A * y ^ (1 + α) := by
    intro y hy
    simp only [Jr, le_refl, if_true]
    have h := hK₁ y hy
    rw [show (((9 + 6 * 0 : ℕ) : ℝ) / 8) = 1 + α by norm_num [hα]] at h
    refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by rw [hA]; linarith [abs_nonneg Kk]))
      (by positivity)
  have hJk : ∀ y, 1 ≤ y → |Jr m k y| ≤ A * y ^ ((k : ℝ) + σ) := by
    intro y hy
    simp only [Jr, show 1 ≤ k by omega, if_true]
    refine (Complex.abs_re_le_norm _).trans ((hKkp y hy).trans ?_)
    exact mul_le_mul_of_nonneg_right (by rw [hA]; linarith [abs_nonneg K₁]) (by positivity)
  have hcont : ∀ j, ContinuousOn (Jr m j) (Ioi 0) := by
    intro j
    by_cases hj : 1 ≤ j
    · have e : Jr m j = fun y => (Jc m j (1 / 2) y).re := by funext y; simp [Jr, hj]
      rw [e]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_Jc m j hm1 hj)
    · have e : Jr m j = fun _ => 0 := by funext y; simp [Jr, hj]
      rw [e]; exact continuousOn_const
  have hrel : ∀ j, 1 ≤ j → j < k → ∀ u, 0 < u → ∀ v, 0 ≤ v →
      Jr m (j + 1) (u + v) - Jr m (j + 1) u = ((j : ℝ) + 1) * ∫ w in (0 : ℝ)..v, Jr m j (u + w) := by
    intro j hj _ u hu v hv
    simp only [Jr, hj, show 1 ≤ j + 1 by omega, if_true]
    have hr := Jc_rel m j hm1 hj hu hv
    have hII : IntervalIntegrable (fun w => Jc m j (1 / 2) (u + w)) volume 0 v := by
      apply ContinuousOn.intervalIntegrable
      refine (continuousOn_Jc m j hm1 hj).comp (continuous_const.add continuous_id).continuousOn
        (fun w hw => ?_)
      rw [uIcc_of_le hv] at hw; simp only [mem_Ioi]; linarith [hw.1]
    have := congrArg Complex.re hr
    rw [Complex.sub_re] at this
    have hre : (∫ w in (0 : ℝ)..v, Jc m j (1 / 2) (u + w)).re =
        ∫ w in (0 : ℝ)..v, (Jc m j (1 / 2) (u + w)).re := by
      have h' := Complex.reCLM.intervalIntegral_comp_comm hII
      simp only [Complex.reCLM_apply] at h'
      exact h'.symm
    rw [this, show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      hre]
  have hrep : ∀ x : ℝ, 1 ≤ x → W b k x = c * x ^ (k + 1) / ((k : ℝ) + 1) + d' * x ^ k +
      ∑' n : ℕ, b n / (n : ℝ) ^ (k + 1) * Jr m k (n * x) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hD := dual_rep d k hm hsumA b hb hb0 hbL (hbS _ (by simp; norm_num)) hk18 hx
    -- summability of the complex dual series
    have hsumc : Summable fun n : ℕ => ((b n / (n : ℝ) ^ (k + 1) : ℝ) : ℂ) * Jc m k (1 / 2) (n * x) := by
      refine Summable.of_norm_bounded (hsummε.mul_left (|Kk| * x ^ ((k : ℝ) + σ))) (fun n => ?_)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hb0]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hnx : 0 < (n : ℝ) * x := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := hb n; positivity)]
      have hbn := hb n
      have hσn : (n : ℝ) ^ (σ + ξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 hσε
      have hnx1 : 1 ≤ (n : ℝ) * x := by nlinarith
      calc b n / (n : ℝ) ^ (k + 1) * ‖Jc m k (1 / 2) (n * x)‖
          ≤ b n / (n : ℝ) ^ (k + 1) * (|Kk| * ((n : ℝ) * x) ^ ((k : ℝ) + σ)) := by
            gcongr; exact hKkp _ hnx1
        _ = |Kk| * x ^ ((k : ℝ) + σ) * (b n * ((n : ℝ) ^ σ / n)) := by
            rw [Real.mul_rpow hn0.le hx0.le, Real.rpow_add hn0, Real.rpow_natCast, pow_succ]
            field_simp
        _ = |Kk| * x ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ξ) * (n : ℝ) ^ (σ + ξ)) := by
            rw [rpow_div_self_eq hn0 σ ξ]; ring
        _ ≤ |Kk| * x ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ξ) * 1) := by gcongr
        _ = |Kk| * x ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ξ)) := by ring
    have := congrArg Complex.re hD
    rw [Complex.ofReal_re, Complex.add_re, Complex.re_tsum hsumc] at this
    rw [this]
    have e1 : ((RankinLandau.Psi d k x 1 - RankinLandau.Psi d k x 0) * (x : ℂ) ^ k).re =
        c * x ^ (k + 1) / ((k : ℝ) + 1) + d' * x ^ k := by
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      unfold RankinLandau.Psi
      rw [show ((x : ℂ) ^ k) = (((x ^ k : ℝ)) : ℂ) by push_cast; ring, Complex.re_mul_ofReal,
        cpow_one, cpow_zero]
      simp only [hc, hd', Complex.sub_re]
      simp only [one_mul, mul_zero, zero_mul, sub_self, zero_sub, mul_one, one_mul, zero_add]
      rw [show (x : ℂ) * Rk m k 1 * (κ : ℂ) = ((x : ℝ) : ℂ) * ((κ : ℂ) * Rk m k 1) by ring,
        Complex.re_ofReal_mul, show Rk m k 0 * (κ : ℂ) = (κ : ℂ) * Rk m k 0 by ring]
      field_simp
      ring
    rw [e1]
    congr 1
    congr 1
    funext n
    rw [Complex.re_ofReal_mul]
    simp only [Jr, show 1 ≤ k by omega, if_true]
  have H : LandauHyp b k (Jr m) c d' A σ α ξ :=
    { nonneg := hb, zero := hb0, hk := by omega, hc := hc0, hA := by positivity, hε := hξ0,
      hα := by rw [hα]; linarith, hσ := hσε, hkσ := hkσ, summ := hsummε, cont := hcont,
      rel := hrel, top := hJk, one := hJ1, rep := hrep }
  obtain ⟨C, hC⟩ := landau_sharp H (by norm_num [hα]) (by norm_num [hα]) (by norm_num [hσ])
    (θ := 1 - 2 / 5) (μ := 3 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hα]) (by norm_num [hσ, hkdef])
  -- back to `a` by Möbius
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hW0 : ∀ M : ℕ, W b 0 M = ∑ n ∈ Finset.Ioc 0 M, b n := by
    intro M; unfold W; rw [Nat.floor_natCast, hIcc]; simp
  obtain ⟨C', hC'⟩ := mobius_transfer (A := fun N => ∑ n ∈ Finset.Ioc 0 N, a n)
    (B := fun M => ∑ n ∈ Finset.Ioc 0 M, b n) (c₀ := cB m κ) (C := C) (δ := 2 / 5) (by norm_num)
    (by norm_num) (fun N => sum_a_eq_mobius aF N) (by simp)
    (fun M hM => by
      have := hC M (by exact_mod_cast hM)
      rw [hW0, hc_eq] at this
      exact this)
  refine ⟨C', fun N hN => ?_⟩
  have := hC' N hN
  rw [show (1 : ℝ) - 2 / 5 = 3 / 5 by norm_num] at this
  rw [hIcc]
  have e : cB m κ * (6 / π ^ 2) = κ * rsConstM m := by
    unfold cB; have := Real.pi_pos; field_simp
  rw [e] at this
  exact this

end Main

end RamanujanTau.RankinExact
