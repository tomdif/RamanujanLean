/-
# Jensen's inequality applied to `L(Δ,s)`: zeros in unit windows

Centre `c = 7 + i t₀`, radii `r = 8/5 < R = 2`.  The big circle lies in `5 ≤ Re ≤ 9`, where
`‖L‖ ≤ A(1+‖s‖)²` (`tauL_poly_bound`), and `‖L(c)‖ ≥ e^{−K(7)}` (`tauL_norm_lower`).  Mathlib's
`AnalyticOnNhd.sum_divisor_le` (Jensen's inequality) bounds the zeros, with multiplicity, in the
small disc; that disc contains the window `11/2 < Re < 13/2`, `|Im − t₀| ≤ 1/2`.
-/
import RamanujanTau.ZeroCount.Bounds
import Mathlib.Analysis.Complex.JensenFormula

namespace RamanujanTau.ZeroCount

open Complex Filter Topology Metric MeromorphicOn
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HeckeZeros

/-- Multiplicity of `u` as a zero of `L(Δ,s)` (`0` if `L(Δ,u) ≠ 0`). -/
noncomputable def mult (u : ℂ) : ℕ := analyticOrderNatAt tauL u

lemma analyticOnNhd_tauL (U : Set ℂ) : AnalyticOnNhd ℂ tauL U :=
  fun z _ => tauLSeries_entire.analyticAt z

lemma tauL_seven_ne_zero : tauL 7 ≠ 0 := tauL_ne_zero_of_gt (s := 7) (by norm_num)

lemma order_ne_top (u : ℂ) : analyticOrderAt tauL u ≠ ⊤ := by
  intro h
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u (fun z => tauLSeries_entire.analyticAt z)] at h
  exact tauL_seven_ne_zero (by rw [h]; rfl)

lemma one_le_mult {u : ℂ} (hu : tauL u = 0) : 1 ≤ mult u := by
  have h0 : analyticOrderAt tauL u ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨tauLSeries_entire.analyticAt u, hu⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (order_ne_top u)
  have : n ≠ 0 := by rintro rfl; exact h0 (by rw [← hn]; rfl)
  unfold mult analyticOrderNatAt
  rw [← hn, ENat.toNat_coe]; omega

lemma divisor_eq_mult {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    divisor tauL U u = (mult u : ℤ) := by
  rw [AnalyticOnNhd.divisor_apply (analyticOnNhd_tauL U) hu]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (order_ne_top u)
  unfold mult analyticOrderNatAt
  rw [← hn, ENat.toNat_coe]
  rfl

/-- **Jensen bound for the disc** `|s − (7+it₀)| ≤ 8/5`. -/
theorem jensen_disc : ∃ E : ℝ, ∀ t₀ : ℝ,
    ((∑ᶠ u, divisor tauL (closedBall ((7 : ℂ) + t₀ * I) |(8 / 5 : ℝ)|) u : ℤ) : ℝ) ≤
      (2 * Real.log (12 + |t₀|) + E) / Real.log (5 / 4) := by
  obtain ⟨A, hA0, hA⟩ := tauL_poly_bound
  refine ⟨Real.log (1 + A) + Kconst 7, fun t₀ => ?_⟩
  set c : ℂ := (7 : ℂ) + t₀ * I with hc
  have hcre : c.re = 7 := by simp [hc]
  have hcim : c.im = t₀ := by simp [hc]
  have hX : (12 : ℝ) ≤ 12 + |t₀| := by linarith [abs_nonneg t₀]
  set M : ℝ := (1 + A) * (12 + |t₀|) ^ 2 with hM
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ (12 + |t₀|) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : (1 : ℝ) ≤ 1 + A := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ M := by rw [hM]; gcongr
  have hbound : ∀ z ∈ sphere c |(2 : ℝ)|, ‖tauL z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, abs_of_pos (by norm_num : (0 : ℝ) < 2), dist_eq_norm] at hz
    have hre : |z.re - 7| ≤ 2 := by
      have := Complex.abs_re_le_norm (z - c)
      rw [sub_re, hcre, hz] at this; exact this
    have hcn : ‖c‖ ≤ 7 + |t₀| := by
      refine (Complex.norm_le_abs_re_add_abs_im c).trans ?_
      rw [hcre, hcim]; norm_num
    have hzn : ‖z‖ ≤ 9 + |t₀| := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have h := hA z (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
    calc ‖tauL z‖ ≤ A * (1 + ‖z‖) ^ 2 := h
      _ ≤ A * (12 + |t₀|) ^ 2 := by gcongr 2; linarith
      _ ≤ M := by rw [hM]; nlinarith [sq_nonneg (12 + |t₀|)]
  have hc0 : tauL c ≠ 0 := tauL_ne_zero_of_gt (by rw [hcre]; norm_num)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := 8 / 5) (R := 2) (M := M)
    (by norm_num) (by norm_num) hM1 (analyticOnNhd_tauL _) hc0 hbound
  refine hJ.trans ?_
  have hlog54 : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hRr : (2 : ℝ) / (8 / 5) = 5 / 4 := by norm_num
  rw [hRr]
  apply div_le_div_of_nonneg_right _ hlog54.le
  have hLc : 0 < ‖tauL c‖ := norm_pos_iff.2 hc0
  have hlow := tauL_norm_lower (s := c) (by rw [hcre]; norm_num)
  rw [hcre] at hlow
  have hlogc : -Kconst 7 ≤ Real.log ‖tauL c‖ := by
    rw [← Real.log_exp (-Kconst 7)]; exact Real.log_le_log (Real.exp_pos _) hlow
  rw [Real.log_div (by linarith) hLc.ne', hM, Real.log_mul (by linarith) (by positivity),
    Real.log_pow]
  push_cast
  linarith

/-- A point of the window `11/2 < Re < 13/2`, `T < Im ≤ T+1` lies in the disc of radius `8/5`
about `7 + i(T+1/2)`. -/
lemma mem_disc_of_window {T : ℝ} {u : ℂ} (h1 : 11 / 2 < u.re) (h2 : u.re < 13 / 2)
    (h3 : T < u.im) (h4 : u.im ≤ T + 1) :
    u ∈ closedBall ((7 : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I) |(8 / 5 : ℝ)| := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)]
  set w : ℂ := u - ((7 : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I) with hw
  have hwr : w.re = u.re - 7 := by simp [hw]
  have hwi : w.im = u.im - (T + 1 / 2) := by simp [hw]
  have hsq : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hb : ‖w‖ ^ 2 ≤ (8 / 5) ^ 2 := by
    rw [hsq, hwr, hwi]; nlinarith
  nlinarith [norm_nonneg w]

/-- The zeros of `L(Δ,s)` in the open strip with `a < Im ≤ b`. -/
def zeroSet (a b : ℝ) : Set ℂ :=
  {u | tauL u = 0 ∧ 11 / 2 < u.re ∧ u.re < 13 / 2 ∧ a < u.im ∧ u.im ≤ b}

/-- **Zeros in unit windows, with multiplicity.**  There is `C` such that for every real `T`
and every finite set `S` of zeros of `L(Δ,s)` with `11/2 < Re < 13/2`, `T < Im ≤ T+1`,
`∑_{ρ∈S} mult(ρ) ≤ C log(|T|+2)`. -/
theorem window_count : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∀ S : Finset ℂ, (↑S : Set ℂ) ⊆ zeroSet T (T + 1) →
    ((∑ u ∈ S, mult u : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨E, hE⟩ := jensen_disc
  have hlog54 : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := (2 + (2 * Real.log 7 + |E|) / Real.log 2) / Real.log (5 / 4) with hC
  refine ⟨C, by rw [hC]; positivity, fun T S hS => ?_⟩
  set t₀ : ℝ := T + 1 / 2
  set D := divisor tauL (closedBall ((7 : ℂ) + (t₀ : ℂ) * I) |(8 / 5 : ℝ)|)
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  have hSball : ∀ u ∈ S, u ∈ closedBall ((7 : ℂ) + (t₀ : ℂ) * I) |(8 / 5 : ℝ)| := by
    intro u hu
    obtain ⟨_, h1, h2, h3, h4⟩ := hS hu
    exact mem_disc_of_window h1 h2 h3 h4
  -- `∑_S mult ≤ ∑ᶠ D`
  have hle : ((∑ u ∈ S, mult u : ℕ) : ℤ) ≤ ∑ᶠ u, D u := by
    classical
    rw [finsum_eq_sum_of_support_subset (s := S ∪ hfin.toFinset) D
      (by intro x hx; simp [hx])]
    push_cast
    calc ∑ u ∈ S, (mult u : ℤ) = ∑ u ∈ S, D u :=
          Finset.sum_congr rfl fun u hu => (divisor_eq_mult (hSball u hu)).symm
      _ ≤ ∑ u ∈ S ∪ hfin.toFinset, D u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            fun u _ _ => (analyticOnNhd_tauL _).divisor_nonneg u
  have hleR : ((∑ u ∈ S, mult u : ℕ) : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hle
  refine hleR.trans ((hE t₀).trans ?_)
  -- arithmetic: `2 log(12+|t₀|) + E ≤ (2 + (2 log 7+|E|)/log 2) log(|T|+2)`
  have hT2 : (2 : ℝ) ≤ |T| + 2 := by linarith [abs_nonneg T]
  have hLT : Real.log 2 ≤ Real.log (|T| + 2) := Real.log_le_log (by norm_num) hT2
  have ht0 : |t₀| ≤ |T| + 1 / 2 := by
    calc |t₀| = |T + 1 / 2| := rfl
      _ ≤ |T| + |1 / 2| := abs_add_le _ _
      _ = |T| + 1 / 2 := by norm_num
  have h12 : 12 + |t₀| ≤ 7 * (|T| + 2) := by linarith [abs_nonneg T]
  have hlog12 : Real.log (12 + |t₀|) ≤ Real.log 7 + Real.log (|T| + 2) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith [abs_nonneg t₀]) h12
  have hK : 2 * Real.log 7 + |E| ≤ (2 * Real.log 7 + |E|) / Real.log 2 * Real.log (|T| + 2) := by
    have h0 : 0 ≤ 2 * Real.log 7 + |E| := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 7 by norm_num); positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hLT h0
  rw [hC, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog54.le
  have := le_abs_self E
  nlinarith

end RamanujanTau.ZeroCount
