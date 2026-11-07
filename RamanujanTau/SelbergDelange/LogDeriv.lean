/-
# `KK'/KK ≪ log²(|t|+2)` in the zero-free region of `ζ(s)L(Sym²Δ,s)`

`KK(s) = (s−1)ζ(2s)R(s) = (s−1)ζ(s)L(Sym²Δ,s)` (`TauPNTUncond.KK`).

**Theorem** (`logDerivKK_bound`, unconditional).  There are `c > 0` and `C` with: for every `s`
with `Re s ≥ 1 − c/log(|Im s|+2)`, `KK(s) ≠ 0` and `‖KK'/KK(s)‖ ≤ C log²(|Im s|+2)`.

Proof (Titchmarsh §3.11; the template is `TauPNTError.LogDerivBound`).  Only the continuation of
`KK` to `Re s > 3/5` is available with growth bounds, so the disc is small: centre
`z₀ = 33/32 + it`, radius `r = 21/50` (so the disc lies in `Re > 0.611`), and `s` within `r/12`.
* `‖KK(z)‖ ≤ A(|t|+2)²` on the disc (`KK = ζ(2·)·R1`, Rankin's Abel continuation);
* `‖KK(z₀)‖ ≥ e^{−B₁}/32` (`HH = exp(Σ cR n^{−s})`), so `M ≪ log(|t|+2)`;
* `landau_pf`: `‖KK'/KK(z) − Σ n_u/(z−u)‖ ≤ 24M/r` near `z₀`;
* at `z₀`: `Re 1/(z₀−u) ≥ 1`, so `Σ n_u ≤ B₀ + 32 + 24M/r`;
* at `s`: zeros have `Re u ≤ 1 − c₀/(2L)` (`Sym2ZeroFree`), so `|1/(s−u)| ≤ 4L/c₀`.
-/
import RamanujanTau.Sym2ZeroFree.Region
import RamanujanTau.TauPNTError.LandauGen
import RamanujanTau.HeckeConvex.Convex

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange

open Complex Metric Set Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.ZeroFreeRegion

lemma norm_zeta_le_of_re' {a : ℝ} (ha : 1 < a) {w : ℂ} (hw : a ≤ w.re) :
    ‖riemannZeta w‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ a := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by linarith)]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ a) :=
    Real.summable_one_div_nat_rpow.mpr ha
  refine tsum_of_norm_bounded hs.hasSum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
    simp [zero_cpow hw0, Real.zero_rpow (by linarith : a ≠ 0)]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]
    exact one_div_le_one_div_of_le (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 hw)

/-- `‖KK(z)‖ ≤ A(‖z‖+1)²` on `Re z ≥ 61/100`. -/
theorem norm_KK_le : ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ, 61 / 100 ≤ z.re → ‖KK z‖ ≤ A * (‖z‖ + 1) ^ 2 := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := rs_part
  set Zb : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ ((6 : ℝ) / 5) with hZb
  have hZb0 : 0 ≤ Zb := tsum_nonneg fun n => by positivity
  refine ⟨max 1 (Zb * (|rsc| + 100 * (K₁ + |rsc|))), le_max_left _ _, fun z hz => ?_⟩
  have hz35 : 3 / 5 < z.re := by linarith
  rw [Sym2ZeroFree.KK_eq_zeta_R1 hz35, norm_mul]
  have hζ : ‖riemannZeta (2 * z)‖ ≤ Zb :=
    norm_zeta_le_of_re' (by norm_num) (by simp; linarith)
  have hI := norm_abelI_le hK₁0 (by norm_num) hK₁ hz35
  rw [Complex.norm_real, Real.norm_eq_abs] at hI
  have hI' : ‖abelI rsB rsc z‖ ≤ 100 * (K₁ + |rsc|) := by
    refine hI.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ K₁ + |rsc| := by positivity
    nlinarith
  have hz1 : ‖z - 1‖ ≤ ‖z‖ + 1 := by
    have := norm_sub_le z 1; simpa using this
  have hR : ‖R1 z‖ ≤ (|rsc| + 100 * (K₁ + |rsc|)) * (‖z‖ + 1) ^ 2 := by
    unfold R1
    have h1 : ‖(rsc : ℂ) * z + (z - 1) * z * abelI rsB rsc z‖ ≤
        |rsc| * ‖z‖ + ‖z - 1‖ * ‖z‖ * ‖abelI rsB rsc z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine h1.trans ?_
    have hn := norm_nonneg z
    have h2 : ‖z - 1‖ * ‖z‖ * ‖abelI rsB rsc z‖ ≤ (‖z‖ + 1) * (‖z‖ + 1) * (100 * (K₁ + |rsc|)) := by
      gcongr; linarith
    have h3 : |rsc| * ‖z‖ ≤ |rsc| * (‖z‖ + 1) ^ 2 := by
      gcongr; nlinarith
    nlinarith
  calc ‖riemannZeta (2 * z)‖ * ‖R1 z‖ ≤ Zb * ((|rsc| + 100 * (K₁ + |rsc|)) * (‖z‖ + 1) ^ 2) := by
        gcongr
    _ = Zb * (|rsc| + 100 * (K₁ + |rsc|)) * (‖z‖ + 1) ^ 2 := by ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

lemma re_one_div_ge_one {w : ℂ} (h1 : 1 / 32 ≤ w.re) (h2 : ‖w‖ ≤ 7 / 50) : 1 ≤ (1 / w).re := by
  have hw : w ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [one_div w, Complex.inv_re, Complex.normSq_eq_norm_sq, le_div_iff₀ (by positivity)]
  nlinarith

lemma log_shift_le {t v : ℝ} (h : |v - t| ≤ 1 / 2) :
    Real.log (|v| + 3) ≤ 2 * Real.log (|t| + 2) := by
  have hv : |v| ≤ |t| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub v t; linarith
  have ht := abs_nonneg t
  rw [show (2 : ℝ) * Real.log (|t| + 2) = Real.log ((|t| + 2) ^ 2) by
    rw [Real.log_pow]; norm_num]
  exact Real.log_le_log (by positivity) (by nlinarith)

lemma norm_le_of_im_eq {s z : ℂ} (h : s.im = z.im) : ‖s - z‖ ≤ |s.re - z.re| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp [h]

lemma KK_analyticOnNhd : AnalyticOnNhd ℂ KK {s : ℂ | 0 < s.re} :=
  differentiableOn_KK.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- `‖KK'/KK(s)‖ ≤ B₀ + 32` for `Re s ≥ 33/32` (Dirichlet series of `vR`). -/
lemma logDerivKK_right : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 33 / 32 ≤ s.re →
    ‖deriv KK s / KK s‖ ≤ B := by
  have hsum := LSeriesSummable_vR (s := ((33 / 32 : ℝ) : ℂ)) (by simp; norm_num)
  set B₀ : ℝ := ∑' n, ‖LSeries.term (fun n => (vR n : ℂ)) ((33 / 32 : ℝ) : ℂ) n‖
  have hB0 : 0 ≤ B₀ := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨B₀ + 32, by positivity, fun s hs => ?_⟩
  have h := negLogDerivK_eq (s := s) (by linarith)
  have hL := HeckeConvex.norm_LSeries_le' hsum hs
  have hs1 : 1 / 32 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp only [sub_re, one_re] at this
    rw [abs_of_nonneg (by linarith)] at this; linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 32 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have : deriv KK s / KK s = -negLogDerivK s := by rw [negLogDerivK]; ring
  rw [this, norm_neg, h]
  exact (norm_sub_le _ _).trans (by linarith)

set_option maxHeartbeats 4000000 in
/-- **`KK'/KK ≪ log²` in the zero-free region** (unconditional). -/
theorem logDerivKK_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
      KK s ≠ 0 ∧ ‖deriv KK s / KK s‖ ≤ C * Real.log (|s.im| + 2) ^ 2 := by
  obtain ⟨c₀, hc₀, hzf⟩ := Sym2ZeroFree.KK_zero_free_region_uniform
  obtain ⟨A, hA1, hA⟩ := norm_KK_le
  obtain ⟨B, hB0, hright⟩ := logDerivKK_right
  have hsumc := LSeriesSummable_cR (s := ((33 / 32 : ℝ) : ℂ)) (by simp; norm_num)
  set B₁ : ℝ := ∑' n, ‖LSeries.term (fun n => (cR n : ℂ)) ((33 / 32 : ℝ) : ℂ) n‖ with hB₁
  have hB₁0 : 0 ≤ B₁ := tsum_nonneg fun _ => norm_nonneg _
  set K : ℝ := B₁ + Real.log 32 with hKdef
  have hl32 : 0 < Real.log 32 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := by positivity
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hlA : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
  set c : ℝ := min (c₀ / 4) (1 / 400) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc₀ : c ≤ c₀ / 4 := min_le_left _ _
  have hc400 : c ≤ 1 / 400 := min_le_right _ _
  set C₁ : ℝ := (Real.log (4 * A) + K) / Real.log 2 + 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  -- the final constant
  set E : ℝ := 1200 / 21 with hE
  set C : ℝ := E * C₁ / Real.log 2 + 4 * (B / Real.log 2 + E * C₁) / c₀ + B / Real.log 2 ^ 2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨c, hc0, hc400, C, hC0, fun s hs => ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 0 < L := by linarith
  have hcL : c / L ≤ 3 / 800 := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hcL' : c / L ≤ c₀ / (4 * L) := by
    rw [div_le_div_iff₀ hLpos (by positivity)]; nlinarith
  have hsre : 1 - 3 / 800 ≤ s.re := by linarith
  -- non-vanishing at `s`
  have hne : KK s ≠ 0 := by
    intro h0
    have h := hzf s h0
    have hlu : Real.log (|s.im| + 3) ≤ 2 * L := log_shift_le (t := t) (v := t) (by rw [sub_self, abs_zero]; norm_num)
    have hlu0 : 0 < Real.log (|s.im| + 3) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hk : c₀ / (2 * L) ≤ c₀ / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_left hc₀.le hlu0 hlu
    have h1 : c₀ / (4 * L) < c₀ / (2 * L) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  refine ⟨hne, ?_⟩
  have hLL : L ≤ L ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2p]; nlinarith
  rcases le_or_gt (33 / 32) s.re with hσ | hσ
  · have h := hright s hσ
    have : B ≤ B / Real.log 2 ^ 2 * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : Real.log 2 ^ 2 ≤ L ^ 2 := by gcongr
      nlinarith
    have h2 : 0 ≤ (E * C₁ / Real.log 2 + 4 * (B / Real.log 2 + E * C₁) / c₀) * L ^ 2 := by positivity
    have hCL : C * L ^ 2 = (E * C₁ / Real.log 2 + 4 * (B / Real.log 2 + E * C₁) / c₀) * L ^ 2
        + B / Real.log 2 ^ 2 * L ^ 2 := by rw [hCdef]; ring
    linarith
  -- Landau range
  set z₀ : ℂ := (33 / 32 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 33 / 32 := by simp [hz₀]
  have hz₀im : z₀.im = t := by simp [hz₀]
  set M : ℝ := Real.log (4 * A * (|t| + 2) ^ 2) + K with hM
  have hX : (16 : ℝ) ≤ 4 * A * (|t| + 2) ^ 2 := by
    have := abs_nonneg t; nlinarith
  have hM0 : 0 < M := by
    have : 0 < Real.log (4 * A * (|t| + 2) ^ 2) := Real.log_pos (by linarith)
    linarith
  -- lower bound at the centre
  have hz₀1 : z₀ ≠ 0 ∧ z₀ ≠ 1 := ⟨fun h => by
    have := congrArg Complex.re h; rw [hz₀re] at this; norm_num at this,
    fun h => by have := congrArg Complex.re h; rw [hz₀re] at this; norm_num at this⟩
  have hlow : Real.exp (-K) ≤ ‖KK z₀‖ := by
    rw [KK_eq hz₀1.1 hz₀1.2, HH_exp (by rw [hz₀re]; norm_num), norm_mul, Complex.norm_exp]
    have hn1 : 1 / 32 ≤ ‖z₀ - 1‖ := by
      have := Complex.abs_re_le_norm (z₀ - 1)
      rw [sub_re, hz₀re, one_re] at this
      calc (1 / 32 : ℝ) = |(33 / 32 : ℝ) - 1| := by norm_num
        _ ≤ ‖z₀ - 1‖ := this
    have hLs : ‖LSeries (fun n => (cR n : ℂ)) z₀‖ ≤ B₁ :=
      HeckeConvex.norm_LSeries_le' hsumc (by rw [hz₀re])
    have hre : -B₁ ≤ (LSeries (fun n => (cR n : ℂ)) z₀).re := by
      have := Complex.abs_re_le_norm (LSeries (fun n => (cR n : ℂ)) z₀)
      have := neg_abs_le (LSeries (fun n => (cR n : ℂ)) z₀).re
      linarith
    have he : Real.exp (-K) = (1 / 32) * Real.exp (-B₁) := by
      rw [hKdef, neg_add, Real.exp_add, Real.exp_neg (Real.log 32), Real.exp_log (by norm_num)]
      ring
    rw [he]
    exact mul_le_mul hn1 (Real.exp_le_exp.mpr hre) (by positivity) (norm_nonneg _)
  have hz₀ne : KK z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith [Real.exp_pos (-K)]
  have hball : ∀ z ∈ closedBall z₀ (21 / 50), 61 / 100 ≤ z.re ∧ ‖z‖ + 1 ≤ 2 * (|t| + 2) := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    have hre := (Complex.abs_re_le_norm (z - z₀)).trans hz
    rw [sub_re, hz₀re, abs_le] at hre
    have hzn : ‖z‖ ≤ 33 / 32 + |t| + 21 / 50 := by
      have h1 : ‖z₀‖ ≤ 33 / 32 + |t| := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [hz₀re, hz₀im]; norm_num
      have := norm_le_norm_add_norm_sub' z z₀
      linarith
    refine ⟨by linarith, by linarith [abs_nonneg t]⟩
  have hbd : ∀ z ∈ closedBall z₀ (21 / 50), ‖KK z‖ ≤ Real.exp M * ‖KK z₀‖ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hball z hz
    have h4 : ‖KK z‖ ≤ 4 * A * (|t| + 2) ^ 2 := by
      refine (hA z h1).trans ?_
      have : (‖z‖ + 1) ^ 2 ≤ (2 * (|t| + 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      nlinarith
    have h5 : 4 * A * (|t| + 2) ^ 2 = Real.exp M * Real.exp (-K) := by
      rw [← Real.exp_add, hM, add_neg_cancel_right, Real.exp_log (by linarith)]
    rw [h5] at h4
    exact h4.trans (by gcongr)
  have han : AnalyticOnNhd ℂ KK (closedBall z₀ (21 / 50)) := fun z hz =>
    KK_analyticOnNhd z (by have := (hball z hz).1; simp only [mem_setOf_eq]; linarith)
  obtain ⟨S, n, hS, hpf⟩ := TauPNTError.landau_pf (f := KK) (c := z₀) (r := 21 / 50) (M := M)
    (by norm_num) hM0 han hz₀ne hbd
  have h24 : 24 * M / (21 / 50) = E * M := by rw [hE]; ring
  rw [h24] at hpf
  have hSre : ∀ u ∈ S, u.re < 1 := by
    intro u hu
    by_contra h; push Not at h
    exact KK_ne_zero h (hS u hu).2
  have hSdist : ∀ u ∈ S, ‖z₀ - u‖ ≤ 7 / 50 := by
    intro u hu
    rw [← dist_eq, dist_comm]
    have := (hS u hu).1; linarith
  have hcount : ∑ u ∈ S, (n u : ℝ) ≤ B + E * M := by
    have h := hpf z₀ (mem_closedBall_self (by norm_num)) hz₀ne
    have hnl : ‖deriv KK z₀ / KK z₀‖ ≤ B := hright z₀ (by rw [hz₀re])
    have hsn : ‖∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))‖ ≤ B + E * M := by
      have := norm_sub_norm_le (∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))) (deriv KK z₀ / KK z₀)
      rw [norm_sub_rev] at this
      linarith
    have hre : ∑ u ∈ S, (n u : ℝ) * 1 ≤ (∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      rw [show ((n u : ℂ) * (1 / (z₀ - u))).re = (n u : ℝ) * (1 / (z₀ - u)).re by simp]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine re_one_div_ge_one ?_ (hSdist u hu)
      rw [sub_re, hz₀re]; linarith [hSre u hu]
    have h5 := hre.trans ((Complex.re_le_norm _).trans hsn)
    simp only [mul_one] at h5
    exact h5
  have hsz : s ∈ closedBall z₀ ((21 / 50) / 12) := by
    rw [mem_closedBall, dist_eq]
    refine (norm_le_of_im_eq (by rw [hz₀im])).trans ?_
    rw [hz₀re, abs_le]; constructor <;> linarith only [hs, hcL, hσ]
  have hmain := hpf s hsz hne
  have hterm : ∀ u ∈ S, ‖(n u : ℂ) * (1 / (s - u))‖ ≤ (n u : ℝ) * (4 * L / c₀) := by
    intro u hu
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hu0 := (hS u hu).2
    have hdu : ‖z₀ - u‖ ≤ 7 / 50 := hSdist u hu
    have huim : |u.im - t| ≤ 1 / 2 := by
      have := (Complex.abs_im_le_norm (z₀ - u)).trans hdu
      rw [sub_im, hz₀im, abs_sub_comm] at this; linarith
    have hz := hzf u hu0
    have hlu := log_shift_le huim
    have hlupos : 0 < Real.log (|u.im| + 3) :=
      Real.log_pos (by linarith [abs_nonneg u.im])
    have hk : c₀ / (2 * L) ≤ c₀ / Real.log (|u.im| + 3) :=
      div_le_div_of_nonneg_left hc₀.le hlupos (by rw [← hL] at hlu; linarith)
    have hgap : c₀ / (4 * L) ≤ (s - u).re := by
      rw [sub_re]
      have : c₀ / (2 * L) = c₀ / (4 * L) + c₀ / (4 * L) := by field_simp; ring
      linarith
    have hpos : 0 < c₀ / (4 * L) := by positivity
    have hnorm : c₀ / (4 * L) ≤ ‖s - u‖ := hgap.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one]
    calc 1 / ‖s - u‖ ≤ 1 / (c₀ / (4 * L)) := one_div_le_one_div_of_le hpos hnorm
      _ = 4 * L / c₀ := by field_simp
  have hsumS : ‖∑ u ∈ S, (n u : ℂ) * (1 / (s - u))‖ ≤ (B + E * M) * (4 * L / c₀) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hcount (by positivity)
  have hML : M ≤ C₁ * L := by
    have h1 : Real.log (4 * A * (|t| + 2) ^ 2) = Real.log (4 * A) + 2 * L := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log (4 * A) + K ≤ (Real.log (4 * A) + K) / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2p]
      have : 0 ≤ Real.log (4 * A) + K := by positivity
      nlinarith
    rw [hM, h1, hC₁]
    nlinarith
  have hfin : ‖deriv KK s / KK s‖ ≤ E * M + (B + E * M) * (4 * L / c₀) := by
    have := norm_le_norm_add_norm_sub' (deriv KK s / KK s)
      (∑ u ∈ S, (n u : ℂ) * (1 / (s - u)))
    linarith
  refine hfin.trans ?_
  have hE0 : 0 ≤ E := by rw [hE]; norm_num
  have e1 : E * M ≤ E * C₁ / Real.log 2 * L ^ 2 := by
    have : E * M ≤ E * C₁ * L := by nlinarith
    calc E * M ≤ E * C₁ * L := this
      _ ≤ E * C₁ * (L ^ 2 / Real.log 2) := by gcongr
      _ = _ := by ring
  have e2 : (B + E * M) * (4 * L / c₀) ≤ 4 * (B / Real.log 2 + E * C₁) / c₀ * L ^ 2 := by
    have hBL : B * L ≤ B / Real.log 2 * L ^ 2 := by
      calc B * L ≤ B * (L ^ 2 / Real.log 2) := by gcongr
        _ = _ := by ring
    have hM2 : M * L ≤ C₁ * L ^ 2 := by nlinarith
    have : (B + E * M) * (4 * L / c₀) = 4 * (B * L + E * (M * L)) / c₀ := by
      ring
    have key : B * L + E * (M * L) ≤ (B / Real.log 2 + E * C₁) * L ^ 2 := by nlinarith
    rw [this]
    calc 4 * (B * L + E * (M * L)) / c₀ ≤ 4 * ((B / Real.log 2 + E * C₁) * L ^ 2) / c₀ := by
          gcongr
      _ = _ := by ring
  have e3 : 0 ≤ B / Real.log 2 ^ 2 * L ^ 2 := by positivity
  have hCL : C * L ^ 2 = E * C₁ / Real.log 2 * L ^ 2 + 4 * (B / Real.log 2 + E * C₁) / c₀ * L ^ 2
      + B / Real.log 2 ^ 2 * L ^ 2 := by rw [hCdef]; ring
  linarith

end RamanujanTau.SelbergDelange
