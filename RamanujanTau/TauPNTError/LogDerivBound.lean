/-
# `L'/L(s) ≪ log²(|t|+2)` in the de la Vallée-Poussin region

Normalized coordinates: `L(s) = Lnorm s = L(Δ, s + 11/2)`, edge `Re s = 1`.

**Theorem** (`negLogDeriv_bound`, unconditional).  There are `c > 0` and `C` such that for every
`s` with `Re s ≥ 1 − c / log(|Im s| + 2)`:  `L(s) ≠ 0` and `‖L'/L(s)‖ ≤ C log²(|Im s| + 2)`.

Proof (Titchmarsh §3.11, Iwaniec–Kowalski §5.4).  Put `t = Im s`, `ℓ = log(|t|+2)`,
`z₀ = 17/16 + it`.  For `Re s ≥ 17/16` the Dirichlet series gives `‖L'/L‖ ≤ B₀`.  Otherwise:
* on `|z − z₀| ≤ 3/2` (unnormalized `5 ≤ Re ≤ 9`): `|L(z)| ≤ A(10+|t|)²` (`tauL_poly_bound`), and
  `|L(z₀)| ≥ e^{−K}` (`tauL_norm_lower`), so `|L(z)| ≤ e^M |L(z₀)|` with `M ≪ ℓ`;
* `landau_pf` gives zeros `u ∈ S` (`|u − z₀| ≤ 1/2`) with
  `‖L'/L(z) − Σ n_u/(z − u)‖ ≤ 16M` for `|z − z₀| ≤ 1/8`;
* at `z = z₀`: `Re 1/(z₀ − u) ≥ 1/4` (since `Re u < 1`), so `Σ n_u ≤ 4(B₀ + 16M) ≪ ℓ`;
* at `z = s`: each zero has `Re u ≤ 1 − c₀/(2ℓ)` (zero-free region, `|Im u − t| ≤ 1/2`), and
  `Re s ≥ 1 − c₀/(4ℓ)`, so `|1/(s − u)| ≤ 4ℓ/c₀`.  Hence `‖L'/L(s)‖ ≤ 16M + Σ n_u·4ℓ/c₀ ≪ ℓ²`.
-/
import RamanujanTau.TauPNTError.LandauGen
import RamanujanTau.ZeroFreeRegion.Uniform
import RamanujanTau.TauPNT.LogDeriv

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Complex Metric Set Filter Topology
open RamanujanTau.TauPNT RamanujanTau.HeckeL

lemma re_one_div_ge {w : ℂ} (h1 : 1 / 16 ≤ w.re) (h2 : ‖w‖ ≤ 1 / 2) : 1 / 4 ≤ (1 / w).re := by
  have hw : w ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [one_div w, Complex.inv_re, Complex.normSq_eq_norm_sq, le_div_iff₀ (by positivity)]
  nlinarith

lemma log_im_le {t v : ℝ} (h : |v - t| ≤ 1 / 2) :
    Real.log (|v| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have hv : |v| ≤ |t| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub v t; linarith
  have ht := abs_nonneg t
  rw [show (2 : ℝ) * Real.log (|t| + 2) = Real.log ((|t| + 2) ^ 2) by
    rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (by positivity)
  nlinarith

lemma norm_le_of_im_eq {s z : ℂ} (h : s.im = z.im) : ‖s - z‖ ≤ |s.re - z.re| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp [h]

set_option maxHeartbeats 2000000 in
/-- **`L'/L ≪ log²` in the zero-free region** (unconditional). -/
theorem negLogDeriv_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 32 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
      Lnorm s ≠ 0 ∧ ‖negLogDeriv s‖ ≤ C * Real.log (|s.im| + 2) ^ 2 := by
  obtain ⟨c₀, hc₀, hzf⟩ := ZeroFreeRegion.tauL_zero_free_region_uniform
  obtain ⟨A, hA0, hA⟩ := ZeroCount.tauL_poly_bound
  set K : ℝ := ZeroCount.Kconst (13 / 2 + 1 / 16) with hKdef
  have hK0 : 0 ≤ K := tsum_nonneg fun p => ZeroCount.gmaj_nonneg _ p
  have hsum := LSeriesSummable_vM (s := ((17 / 16 : ℝ) : ℂ)) (by simp; norm_num)
  set B₀ : ℝ := ∑' n, ‖LSeries.term (fun n => (vM n : ℂ)) ((17 / 16 : ℝ) : ℂ) n‖ with hB₀
  have hB0 : 0 ≤ B₀ := tsum_nonneg fun _ => norm_nonneg _
  have hright : ∀ s : ℂ, 17 / 16 ≤ s.re → ‖negLogDeriv s‖ ≤ B₀ := fun s hs => by
    rw [negLogDeriv_eq_LSeries (by linarith)]
    exact HeckeConvex.norm_LSeries_le' hsum hs
  have hl2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
  set c : ℝ := min (c₀ / 4) (1 / 32) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc₀ : c ≤ c₀ / 4 := min_le_left _ _
  have hc32 : c ≤ 1 / 32 := min_le_right _ _
  set C₁ : ℝ := (Real.log (A + 1) + 2 * Real.log 5 + K) / Real.log 2 + 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set C : ℝ := 16 * C₁ / Real.log 2 + 16 * (B₀ / Real.log 2 + 16 * C₁) / c₀ +
    B₀ / Real.log 2 ^ 2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨c, hc0, hc32, C, hC0, fun s hs => ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 0 < L := by linarith
  have hcL : c / L ≤ 1 / 16 := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hcL' : c / L ≤ c₀ / (4 * L) := by
    rw [div_le_div_iff₀ hLpos (by positivity)]; nlinarith
  have hsre : 15 / 16 ≤ s.re := by linarith
  -- nonvanishing at `s`
  have hne : Lnorm s ≠ 0 := by
    intro h0
    have hnt : ∀ n : ℕ, s + 11 / 2 ≠ -(n : ℂ) := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have := (hzf (s + 11 / 2) h0 hnt).1
    simp only [add_re, add_im, show ((11 / 2 : ℂ)).re = 11 / 2 by norm_num,
      show ((11 / 2 : ℂ)).im = 0 by norm_num, add_zero] at this
    have h1 : c₀ / (4 * L) < c₀ / L := by
      rw [div_lt_div_iff₀ (by positivity) hLpos]; nlinarith
    rw [← ht, ← hL] at this
    linarith
  refine ⟨hne, ?_⟩
  rcases le_or_gt (17 / 16) s.re with hσ | hσ
  · -- trivial range
    have h := hright s hσ
    have : B₀ ≤ B₀ / Real.log 2 ^ 2 * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : Real.log 2 ^ 2 ≤ L ^ 2 := by gcongr
      nlinarith
    have h2 : 0 ≤ (16 * C₁ / Real.log 2 + 16 * (B₀ / Real.log 2 + 16 * C₁) / c₀) * L ^ 2 := by
      positivity
    have hCL : C * L ^ 2 = (16 * C₁ / Real.log 2 + 16 * (B₀ / Real.log 2 + 16 * C₁) / c₀) * L ^ 2
        + B₀ / Real.log 2 ^ 2 * L ^ 2 := by rw [hCdef]; ring
    linarith
  -- Landau range
  set z₀ : ℂ := (17 / 16 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 17 / 16 := by simp [hz₀]
  have hz₀im : z₀.im = t := by simp [hz₀]
  set M : ℝ := Real.log ((A + 1) * (10 + |t|) ^ 2) + K with hM
  have hX : (100 : ℝ) ≤ (A + 1) * (10 + |t|) ^ 2 := by
    have := abs_nonneg t; nlinarith
  have hM0 : 0 < M := by
    have : 0 < Real.log ((A + 1) * (10 + |t|) ^ 2) := Real.log_pos (by linarith)
    linarith
  have hlow : Real.exp (-K) ≤ ‖Lnorm z₀‖ := by
    have h := ZeroCount.tauL_norm_lower (s := z₀ + 11 / 2) (by simp [hz₀re]; norm_num)
    have he : (z₀ + 11 / 2).re = 13 / 2 + 1 / 16 := by simp [hz₀re]; norm_num
    rw [he] at h
    exact h
  have hz₀ne : Lnorm z₀ ≠ 0 := Lnorm_ne_zero (by rw [hz₀re]; norm_num)
  have hbd : ∀ z ∈ closedBall z₀ (3 / 2), ‖Lnorm z‖ ≤ Real.exp M * ‖Lnorm z₀‖ := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    have hre := (Complex.abs_re_le_norm (z - z₀)).trans hz
    rw [sub_re, hz₀re, abs_le] at hre
    have hzn : ‖z‖ ≤ 17 / 16 + |t| + 3 / 2 := by
      have h1 : ‖z₀‖ ≤ 17 / 16 + |t| := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [hz₀re, hz₀im]; norm_num
      have := norm_le_norm_add_norm_sub' z z₀
      linarith
    have h1 := hA (z + 11 / 2) (by simp; linarith) (by simp; linarith)
    have h2 : ‖z + 11 / 2‖ ≤ 9 + |t| := by
      have := norm_add_le z (11 / 2 : ℂ)
      have h3 : ‖(11 / 2 : ℂ)‖ = 11 / 2 := by
        rw [show (11 / 2 : ℂ) = ((11 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
        norm_num
      linarith
    have h4 : ‖Lnorm z‖ ≤ (A + 1) * (10 + |t|) ^ 2 := by
      calc ‖Lnorm z‖ = ‖tauL (z + 11 / 2)‖ := rfl
        _ ≤ A * (1 + ‖z + 11 / 2‖) ^ 2 := h1
        _ ≤ (A + 1) * (10 + |t|) ^ 2 := by
          have h6 : (1 + ‖z + 11 / 2‖) ^ 2 ≤ (10 + |t|) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
          have h7 : 0 ≤ (10 + |t|) ^ 2 := by positivity
          calc A * (1 + ‖z + 11 / 2‖) ^ 2 ≤ A * (10 + |t|) ^ 2 :=
                mul_le_mul_of_nonneg_left h6 hA0
            _ ≤ (A + 1) * (10 + |t|) ^ 2 :=
                mul_le_mul_of_nonneg_right (by linarith) h7
    have h5 : (A + 1) * (10 + |t|) ^ 2 = Real.exp M * Real.exp (-K) := by
      rw [← Real.exp_add, hM, add_neg_cancel_right, Real.exp_log (by linarith)]
    rw [h5] at h4
    exact h4.trans (by gcongr)
  obtain ⟨S, n, hS, hpf⟩ := landau_pf (f := Lnorm) (c := z₀) (r := 3 / 2) (M := M)
    (by norm_num) hM0 (fun z _ => Lnorm_differentiable.analyticAt z) hz₀ne hbd
  have h24 : 24 * M / (3 / 2) = 16 * M := by ring
  rw [h24] at hpf
  -- facts about the zeros in `S`
  have hSre : ∀ u ∈ S, u.re < 1 := by
    intro u hu
    by_contra h; push Not at h
    exact Lnorm_ne_zero h (hS u hu).2
  have hSdist : ∀ u ∈ S, ‖z₀ - u‖ ≤ 1 / 2 := by
    intro u hu
    rw [← dist_eq, dist_comm]
    have := (hS u hu).1; linarith
  -- count
  have hcount : ∑ u ∈ S, (n u : ℝ) ≤ 4 * (B₀ + 16 * M) := by
    have h := hpf z₀ (mem_closedBall_self (by norm_num)) hz₀ne
    have hnl : ‖deriv Lnorm z₀ / Lnorm z₀‖ ≤ B₀ := by
      have := hright z₀ (by rw [hz₀re])
      rwa [negLogDeriv, neg_div, norm_neg] at this
    have hsn : ‖∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))‖ ≤ B₀ + 16 * M := by
      have := norm_sub_norm_le (∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))) (deriv Lnorm z₀ / Lnorm z₀)
      rw [norm_sub_rev] at this
      linarith
    have hre : ∑ u ∈ S, (n u : ℝ) * (1 / 4) ≤ (∑ u ∈ S, (n u : ℂ) * (1 / (z₀ - u))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      rw [show ((n u : ℂ) * (1 / (z₀ - u))).re = (n u : ℝ) * (1 / (z₀ - u)).re by simp]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine re_one_div_ge ?_ (hSdist u hu)
      rw [sub_re, hz₀re]; linarith [hSre u hu]
    have h5 := hre.trans ((Complex.re_le_norm _).trans hsn)
    rw [← Finset.sum_mul] at h5
    linarith only [h5]
  -- the main estimate at `s`
  have hsz : s ∈ closedBall z₀ ((3 / 2) / 12) := by
    rw [mem_closedBall, dist_eq]
    refine (norm_le_of_im_eq (by rw [hz₀im])).trans ?_
    rw [hz₀re, abs_le]; constructor <;> linarith only [hs, hcL, hσ]
  have hmain := hpf s hsz hne
  have hterm : ∀ u ∈ S, ‖(n u : ℂ) * (1 / (s - u))‖ ≤ (n u : ℝ) * (4 * L / c₀) := by
    intro u hu
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hu0 := (hS u hu).2
    have hdu : ‖z₀ - u‖ ≤ 1 / 2 := hSdist u hu
    have hure : 17 / 16 - 1 / 2 ≤ u.re := by
      have := (Complex.abs_re_le_norm (z₀ - u)).trans hdu
      rw [sub_re, hz₀re, abs_le] at this; linarith
    have huim : |u.im - t| ≤ 1 / 2 := by
      have := (Complex.abs_im_le_norm (z₀ - u)).trans hdu
      rw [sub_im, hz₀im, abs_sub_comm] at this; exact this
    have hnt : ∀ k : ℕ, u + 11 / 2 ≠ -(k : ℂ) := by
      intro k h
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hz := (hzf (u + 11 / 2) hu0 hnt).1
    simp only [add_re, add_im, show ((11 / 2 : ℂ)).re = 11 / 2 by norm_num,
      show ((11 / 2 : ℂ)).im = 0 by norm_num, add_zero] at hz
    have hlu := log_im_le huim
    have hlupos : 0 < Real.log (|u.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg u.im])
    have hk : c₀ / (2 * L) ≤ c₀ / Real.log (|u.im| + 2) :=
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
  have hsumS : ‖∑ u ∈ S, (n u : ℂ) * (1 / (s - u))‖ ≤ (4 * (B₀ + 16 * M)) * (4 * L / c₀) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hcount (by positivity)
  have hML : M ≤ C₁ * L := by
    have h1 : Real.log ((A + 1) * (10 + |t|) ^ 2) =
        Real.log (A + 1) + 2 * Real.log (10 + |t|) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
    have h2 : Real.log (10 + |t|) ≤ Real.log 5 + L := by
      rw [hL, ← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
    have h3 : Real.log (A + 1) + 2 * Real.log 5 + K ≤
        (Real.log (A + 1) + 2 * Real.log 5 + K) / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2p]
      have : 0 ≤ Real.log (A + 1) + 2 * Real.log 5 + K := by positivity
      nlinarith
    rw [hM, h1, hC₁]
    nlinarith
  have hnl : ‖negLogDeriv s‖ = ‖deriv Lnorm s / Lnorm s‖ := by
    rw [negLogDeriv, neg_div, norm_neg]
  have hfin : ‖negLogDeriv s‖ ≤ 16 * M + (4 * (B₀ + 16 * M)) * (4 * L / c₀) := by
    rw [hnl]
    have := norm_le_norm_add_norm_sub' (deriv Lnorm s / Lnorm s)
      (∑ u ∈ S, (n u : ℂ) * (1 / (s - u)))
    linarith
  refine hfin.trans ?_
  -- `16M + 16(B₀ + 16M)L/c₀ ≤ C L²`
  have hLL : L ≤ L ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2p]; nlinarith
  have e1 : 16 * M ≤ 16 * C₁ / Real.log 2 * L ^ 2 := by
    have : 16 * M ≤ 16 * C₁ * L := by nlinarith
    calc 16 * M ≤ 16 * C₁ * L := this
      _ ≤ 16 * C₁ * (L ^ 2 / Real.log 2) := by gcongr
      _ = _ := by ring
  have e2 : (4 * (B₀ + 16 * M)) * (4 * L / c₀) ≤
      16 * (B₀ / Real.log 2 + 16 * C₁) / c₀ * L ^ 2 := by
    have hB : B₀ * L ≤ B₀ / Real.log 2 * L ^ 2 := by
      calc B₀ * L ≤ B₀ * (L ^ 2 / Real.log 2) := by gcongr
        _ = _ := by ring
    have hM2 : M * L ≤ C₁ * L ^ 2 := by nlinarith
    have : (4 * (B₀ + 16 * M)) * (4 * L / c₀) = 16 * (B₀ * L + 16 * (M * L)) / c₀ := by
      field_simp; ring
    rw [this, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hc₀.le
    nlinarith
  have e3 : 0 ≤ B₀ / Real.log 2 ^ 2 * L ^ 2 := by positivity
  have hCL : C * L ^ 2 = 16 * C₁ / Real.log 2 * L ^ 2 + 16 * (B₀ / Real.log 2 + 16 * C₁) / c₀ * L ^ 2
      + B₀ / Real.log 2 ^ 2 * L ^ 2 := by rw [hCdef]; ring
  linarith

end RamanujanTau.TauPNTError
