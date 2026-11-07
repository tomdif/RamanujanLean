/-
# Rankin–Selberg: `R(x) = Ω±(x^β)` for every `β < 1/4`

Upgrade of `RankinOmegaPM.rs_omega_pm` (`β < 3/20`) using the mean square of `ζ` on `1/2 < Re < 3/4`.

Suppose `εR(x) ≥ −c₁x^β` for large `x` (`ε = ±1`, `β < 1/4`). By `RankinOmegaPM.conv_of_one_sided`
(Landau, strip form) `M(s) = ∫₁^∞ R(x)x^{−s−1}dx` converges absolutely on `Re s > β`, so on the line
`Re s = σ ∈ (β, 1/4)` we have `|M(s)| ≤ L := ∫ |R| x^{−σ−1}`. With `s = σ − iy`, `w = 1 − s`:

    c_g y^{2−4σ} |Z(w)| ≤ |ζ(2s)| |sM(s) + cs/(s−1)| ≤ |ζ(2s)| · A y          (A = 2L + 2|c|).

Integrate over `[Y, 2Y]`: the first moment `∫|Z(w)| ≥ c₃Y` (`Re w = 1−σ ∈ (3/4, 7/8)`) and the mean
square `∫|ζ(2s)|² ≪ Y^{2−4σ}` (functional equation + Hardy–Littlewood at `Re = 1 − 2σ ∈ (1/2, 3/4)`,
`ZetaLeft.zeta_two_s_mean_sq`), with AM–GM at weight `Y^{(3−e)/2}`, `e = 2 − 4σ`, give

    c_g c₃ Y^{e+1} ≤ (K/2 + 2A²) Y^{(3+e)/2},

impossible for large `Y` because `e > 1 ⟺ σ < 1/4`.
-/
import RamanujanTau.ZetaMeanSquare.ZetaLeft
import RamanujanTau.RankinOmegaPM.Main

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega RamanujanTau.RankinOmegaPM
open scoped Real Interval

/-- **Uniform `Γ`-ratio lower bound** for `0 < σ ≤ 1/2` (copy of `RankinOmega.gamma_ratio_lower`,
whose range was `3/8 ≤ σ ≤ 1/2`; the proof only uses `σ > 0`). -/
theorem gamma_ratio_lower' (m : ℕ) (hm : 1 ≤ m) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ σ y : ℝ, 0 < σ → σ ≤ 1 / 2 → 1 ≤ y →
      cg * y ^ (2 - 4 * σ) * ‖invGamM m (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
        ‖invGamM m ((σ : ℂ) - y * I)‖ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.RankinLandau.norm_Gamma_ratio_unif' (R := m + 1) (by linarith)
  refine ⟨1 / (8 * Real.pi ^ 2 * C ^ 2), by positivity, fun σ y h1 h2 hy => ?_⟩
  set s : ℂ := (σ : ℂ) - y * I with hs
  set w : ℂ := ((1 - σ : ℝ) : ℂ) + y * I with hw
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = -y := by simp [hs]
  have hwre : w.re = 1 - σ := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hy0 : 0 < y := by linarith
  -- (i) `Γ(s+1)` vs `Γ(w+1)`
  have g1 := hC (s + 1) (w + 1) (by simp [hsre]; linarith) (by simp [hsre]; linarith)
    (by simp [hwre]; linarith) (by simp [hwre]; linarith) (by simp [hsim, hwim])
  have g2 := hC (s + m) (w + m) (by simp [hsre]; linarith) (by simp [hsre]; linarith)
    (by simp [hwre]; linarith) (by simp [hwre]; linarith) (by simp [hsim, hwim])
  have e1 : (s + 1).re - (w + 1).re = 2 * σ - 1 := by simp [hsre, hwre]; ring
  have e2 : (s + m).re - (w + m).re = 2 * σ - 1 := by simp [hsre, hwre]; ring
  have e3 : |(w + 1).im| = y := by simp [hwim, abs_of_pos hy0]
  have e4 : |(w + (m : ℂ)).im| = y := by simp [hwim, abs_of_pos hy0]
  rw [e1, e3] at g1
  rw [e2, e4] at g2
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hw0 : w ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  rw [Complex.Gamma_add_one s hs0, Complex.Gamma_add_one w hw0, norm_mul, norm_mul] at g1
  have hns : y ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rw [hsim, abs_neg, abs_of_pos hy0] at this; exact this
  have hnw : ‖w‖ ≤ 2 * y := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [hwre, hwim, abs_of_nonneg (by linarith), abs_of_pos hy0]; linarith
  set P : ℝ := (1 + y) ^ (2 * σ - 1) with hP
  have hP0 : 0 < P := by positivity
  have hPy : P ≤ y ^ (2 * σ - 1) := Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)
  have hGw : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hGwm : 0 < ‖Complex.Gamma (w + m)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hwre]; linarith))
  have hGs : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hGsm : 0 < ‖Complex.Gamma (s + m)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hsre]; linarith))
  have hsn : 0 < ‖s‖ := by linarith
  -- `‖Γ(s)‖ ≤ 2 C P ‖Γ(w)‖`
  have hG1 : ‖Complex.Gamma s‖ ≤ 2 * C * P * ‖Complex.Gamma w‖ := by
    have : ‖s‖ * ‖Complex.Gamma s‖ ≤ ‖s‖ * (2 * C * P * ‖Complex.Gamma w‖) := by
      calc ‖s‖ * ‖Complex.Gamma s‖ ≤ C * P * (‖w‖ * ‖Complex.Gamma w‖) := g1
        _ ≤ C * P * (2 * y * ‖Complex.Gamma w‖) := by gcongr
        _ ≤ C * P * (2 * ‖s‖ * ‖Complex.Gamma w‖) := by gcongr
        _ = ‖s‖ * (2 * C * P * ‖Complex.Gamma w‖) := by ring
    exact le_of_mul_le_mul_left this hsn
  have hGG : ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖ ≤
      2 * C ^ 2 * y ^ (4 * σ - 2) * (‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖) := by
    have hPP : P * P ≤ y ^ (4 * σ - 2) := by
      have : y ^ (4 * σ - 2) = y ^ (2 * σ - 1) * y ^ (2 * σ - 1) := by
        rw [← Real.rpow_add hy0]; ring_nf
      rw [this]; exact mul_le_mul hPy hPy hP0.le (by positivity)
    calc ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖
        ≤ (2 * C * P * ‖Complex.Gamma w‖) * (C * P * ‖Complex.Gamma (w + m)‖) := by
          gcongr
      _ = 2 * C ^ 2 * (P * P) * (‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖) := by ring
      _ ≤ _ := by gcongr
  -- the prefactors
  rw [norm_invGamM, norm_invGamM, hsre, hwre]
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hπ4 : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hpre : Real.pi ^ (1 - σ) * (4 * Real.pi) ^ (1 - σ + m) ≤
      4 * Real.pi ^ 2 * (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) := by
    have a1 : Real.pi ^ (1 - σ) = Real.pi ^ σ * Real.pi ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add Real.pi_pos]; ring_nf
    have a2 : (4 * Real.pi) ^ (1 - σ + m) = (4 * Real.pi) ^ (σ + m) * (4 * Real.pi) ^ (1 - 2 * σ) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have b1 : Real.pi ^ (1 - 2 * σ) ≤ Real.pi := by
      calc Real.pi ^ (1 - 2 * σ) ≤ Real.pi ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hπ (by linarith)
        _ = Real.pi := Real.rpow_one _
    have b2 : (4 * Real.pi) ^ (1 - 2 * σ) ≤ 4 * Real.pi := by
      calc (4 * Real.pi) ^ (1 - 2 * σ) ≤ (4 * Real.pi) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hπ4 (by linarith)
        _ = 4 * Real.pi := Real.rpow_one _
    rw [a1, a2]
    have : 0 ≤ Real.pi ^ σ * (4 * Real.pi) ^ (σ + m) := by positivity
    calc Real.pi ^ σ * Real.pi ^ (1 - 2 * σ) * ((4 * Real.pi) ^ (σ + m) * (4 * Real.pi) ^ (1 - 2 * σ))
        = (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) * (Real.pi ^ (1 - 2 * σ) * (4 * Real.pi) ^ (1 - 2 * σ)) := by ring
      _ ≤ (Real.pi ^ σ * (4 * Real.pi) ^ (σ + m)) * (Real.pi * (4 * Real.pi)) := by gcongr
      _ = _ := by ring
  set Ps : ℝ := Real.pi ^ σ * (4 * Real.pi) ^ (σ + m) with hPs
  set Pw : ℝ := Real.pi ^ (1 - σ) * (4 * Real.pi) ^ (1 - σ + m) with hPw
  set Gs := ‖Complex.Gamma s‖ * ‖Complex.Gamma (s + m)‖ with hGsdef
  set Gw := ‖Complex.Gamma w‖ * ‖Complex.Gamma (w + m)‖ with hGwdef
  have hGs0 : 0 < Gs := by positivity
  have hGw0 : 0 < Gw := by positivity
  have hPs0 : 0 < Ps := by positivity
  have hPw0 : 0 ≤ Pw := by positivity
  have hyy : y ^ (2 - 4 * σ) * y ^ (4 * σ - 2) = 1 := by
    rw [← Real.rpow_add hy0]; simp
  have hy1 : 0 < y ^ (2 - 4 * σ) := by positivity
  rw [div_div, div_div]
  rw [show 1 / (8 * Real.pi ^ 2 * C ^ 2) * y ^ (2 - 4 * σ) * (Pw / (2 * Gw)) =
    (y ^ (2 - 4 * σ) * Pw) / (16 * Real.pi ^ 2 * C ^ 2 * Gw) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `y^{2−4σ} Pw · 2 Gs ≤ Ps · 16 π² C² Gw`
  have key1 : y ^ (2 - 4 * σ) * Gs ≤ 2 * C ^ 2 * Gw := by
    calc y ^ (2 - 4 * σ) * Gs ≤ y ^ (2 - 4 * σ) * (2 * C ^ 2 * y ^ (4 * σ - 2) * Gw) := by gcongr
      _ = 2 * C ^ 2 * Gw * (y ^ (2 - 4 * σ) * y ^ (4 * σ - 2)) := by ring
      _ = 2 * C ^ 2 * Gw := by rw [hyy, mul_one]
  calc y ^ (2 - 4 * σ) * Pw * (2 * Gs) = 2 * Pw * (y ^ (2 - 4 * σ) * Gs) := by ring
    _ ≤ 2 * (4 * Real.pi ^ 2 * Ps) * (2 * C ^ 2 * Gw) := by gcongr
    _ = Ps * (16 * Real.pi ^ 2 * C ^ 2 * Gw) := by ring


section Quarter

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

include habs in
/-- **Uniform first-moment lower bound** for `‖Z‖` on `9/16 ≤ Re w ≤ 1` (copy of
`RankinOmega.Zf_first_moment`, whose range was `[9/16, 5/8]`; the proof only uses `σ' ≤ c`). -/
theorem Zf_first_moment' (hm : 1 ≤ m) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hlow : ∀ n, 0 < n → n < n0 → a n = 0) (ha0 : a n0 ≠ 0) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∃ Y0 : ℝ, 1 ≤ Y0 ∧ ∀ σ' : ℝ, 9 / 16 ≤ σ' → σ' ≤ 1 →
      ∀ Y : ℝ, Y0 ≤ Y → c3 * Y ≤ ∫ y in Y..2 * Y, ‖Zf d ((σ' : ℂ) + y * I)‖ := by
  obtain ⟨c, hc3, htail⟩ := Zf_tail d habs hn0 hlow ha0
  obtain ⟨K, hK0, hK⟩ := Zf_horiz d habs hm c (by linarith)
  set A : ℝ := |a n0| with hAdef
  have hA0 : 0 < A := abs_pos.2 ha0
  have hnR : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
  set mc : ℝ := (n0 : ℝ) ^ c with hmc
  have hmc1 : 1 ≤ mc := Real.one_le_rpow hnR (by linarith)
  set G : ℂ → ℂ := fun w => Zf d w * (n0 : ℂ) ^ w with hG
  have hn0' : (n0 : ℂ) ≠ 0 := by exact_mod_cast (show n0 ≠ 0 by omega)
  have hGd : ∀ w : ℂ, 1 ≤ w.im → DifferentiableAt ℂ G w := by
    intro w hw
    have h0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
    have h1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw; linarith
    exact (differentiableAt_Zf d h0 h1).mul (differentiableAt_id.const_cpow (Or.inl hn0'))
  have hGn : ∀ x y : ℝ, x ≤ c → ‖G ((x : ℂ) + y * I)‖ ≤ mc * ‖Zf d ((x : ℂ) + y * I)‖ := by
    intro x y hx
    simp only [hG, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have : ((x : ℂ) + y * I).re = x := by simp
    rw [this, mul_comm]
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hnR hx
  have hcontG : ∀ x Y : ℝ, 1 ≤ Y → ContinuousOn (fun y : ℝ => G ((x : ℂ) + y * I)) (uIcc Y (2 * Y)) := by
    intro x Y hY y hy
    rw [uIcc_of_le (by linarith)] at hy
    have : 1 ≤ ((x : ℂ) + y * I).im := by simp; linarith [hy.1]
    exact ((hGd _ this).continuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I) (x := y)
      (by fun_prop)).continuousWithinAt
  have hcontZ : ∀ x Y : ℝ, 1 ≤ Y →
      ContinuousOn (fun y : ℝ => ‖Zf d ((x : ℂ) + y * I)‖) (uIcc Y (2 * Y)) := by
    intro x Y hY y hy
    rw [uIcc_of_le (by linarith)] at hy
    have him : 1 ≤ ((x : ℂ) + y * I).im := by simp; linarith [hy.1]
    have h0 : (x : ℂ) + y * I ≠ 0 := by intro h; rw [h] at him; simp at him; linarith
    have h1 : (x : ℂ) + y * I ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
    exact ((differentiableAt_Zf d h0 h1).continuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I)
      (x := y) (by fun_prop)).norm.continuousWithinAt
  set E : ℝ := 4 * c * mc * K with hE
  have hE0 : 0 ≤ E := by rw [hE]; have : 0 ≤ c := by linarith
                         positivity
  set Y0 : ℝ := max 1 ((4 * E / A) ^ (16 : ℕ)) with hY0
  refine ⟨A / (4 * mc), by positivity, Y0, le_max_left _ _, fun σ' h1 h2 Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hY0' : 0 < Y := by linarith
  have hσc : σ' ≤ c := by linarith
  -- horizontal sides
  have hhor : ∀ y₀ : ℝ, 1 ≤ y₀ → y₀ ≤ 2 * Y →
      ‖∫ x in σ'..c, G ((x : ℂ) + y₀ * I)‖ ≤ E / 2 * Y ^ ((15 : ℝ) / 16) := by
    intro y₀ hy1 hy2
    have hb : ∀ x ∈ Ι σ' c, ‖G ((x : ℂ) + y₀ * I)‖ ≤ mc * (K * y₀ ^ ((15 : ℝ) / 16)) := by
      intro x hx
      rw [Set.uIoc_of_le hσc] at hx
      exact (hGn x y₀ hx.2).trans (by gcongr; exact hK x y₀ (by linarith [hx.1]) hx.2 hy1)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have hp : y₀ ^ ((15 : ℝ) / 16) ≤ 2 * Y ^ ((15 : ℝ) / 16) := by
      calc y₀ ^ ((15 : ℝ) / 16) ≤ (2 * Y) ^ ((15 : ℝ) / 16) :=
            Real.rpow_le_rpow (by linarith) hy2 (by norm_num)
        _ = 2 ^ ((15 : ℝ) / 16) * Y ^ ((15 : ℝ) / 16) := Real.mul_rpow (by norm_num) hY0'.le
        _ ≤ 2 * Y ^ ((15 : ℝ) / 16) := by
          gcongr
          calc (2 : ℝ) ^ ((15 : ℝ) / 16) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    rw [abs_of_nonneg (by linarith), hE]
    have : 0 ≤ c - σ' := by linarith
    have : c - σ' ≤ c := by linarith
    have : 0 ≤ mc * K := by positivity
    calc mc * (K * y₀ ^ ((15 : ℝ) / 16)) * (c - σ') ≤ mc * (K * (2 * Y ^ ((15 : ℝ) / 16))) * (c - σ') :=
          by gcongr
      _ = 2 * (mc * K) * (c - σ') * Y ^ ((15 : ℝ) / 16) := by ring
      _ ≤ 2 * (mc * K) * c * Y ^ ((15 : ℝ) / 16) := by gcongr
      _ = _ := by ring
  have hrectD : DifferentiableOn ℂ G ([[σ', c]] ×ℂ [[Y, 2 * Y]]) := by
    intro z hz
    rw [mem_reProdIm, uIcc_of_le hσc, uIcc_of_le (show Y ≤ 2 * Y by linarith)] at hz
    exact (hGd z (by linarith [hz.2.1])).differentiableWithinAt
  have hrect := RamanujanTau.KernelPhase.rect_diff G σ' c Y (2 * Y) hrectD
  have hh1 := hhor Y hY1 (by linarith)
  have hh2 := hhor (2 * Y) (by linarith) le_rfl
  -- right line
  have hright : A * Y / 2 ≤ ‖∫ y in Y..2 * Y, G ((c : ℂ) + y * I)‖ := by
    have hint : IntervalIntegrable (fun y : ℝ => G ((c : ℂ) + y * I)) volume Y (2 * Y) :=
      (hcontG c Y hY1).intervalIntegrable
    have hdiff : ‖(∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * a n0‖ ≤ A / 2 * Y := by
      have e : (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)) - (Y : ℂ) * a n0 =
          ∫ y in Y..2 * Y, (G ((c : ℂ) + y * I) - a n0) := by
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        congr 1; rw [Complex.real_smul]; push_cast; ring
      rw [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := Y) (b := 2 * Y) (C := A / 2) (f := fun y => G ((c : ℂ) + y * I) - a n0)
        (fun y _ => htail y)
      rw [show |2 * Y - Y| = Y by rw [abs_of_nonneg (by linarith)]; ring] at this
      exact this
    have hnY : ‖(Y : ℂ) * a n0‖ = Y * A := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hY0'.le, Complex.norm_real,
        Real.norm_eq_abs]
    have := norm_sub_norm_le ((Y : ℂ) * a n0)
      ((Y : ℂ) * a n0 - (∫ y in Y..2 * Y, G ((c : ℂ) + y * I)))
    rw [sub_sub_cancel, norm_sub_rev, hnY] at this
    linarith
  -- left line
  have hY116 : 4 * E / A ≤ Y ^ ((1 : ℝ) / 16) := by
    have h16 : (4 * E / A) ^ (16 : ℕ) ≤ Y := le_trans (le_max_right _ _) hY
    have h0 : 0 ≤ 4 * E / A := by positivity
    calc 4 * E / A = ((4 * E / A) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
      _ ≤ Y ^ ((1 : ℝ) / 16) := Real.rpow_le_rpow (by positivity) h16 (by norm_num)
  have hYsplit : Y = Y ^ ((15 : ℝ) / 16) * Y ^ ((1 : ℝ) / 16) := by
    rw [← Real.rpow_add hY0']; norm_num
  have hEY : E * Y ^ ((15 : ℝ) / 16) ≤ A * Y / 4 := by
    have h78 : 0 ≤ Y ^ ((15 : ℝ) / 16) := by positivity
    have : E ≤ A / 4 * Y ^ ((1 : ℝ) / 16) := by
      have := mul_le_mul_of_nonneg_left hY116 (show 0 ≤ A / 4 by positivity)
      calc E = A / 4 * (4 * E / A) := by field_simp
        _ ≤ _ := this
    calc E * Y ^ ((15 : ℝ) / 16) ≤ A / 4 * Y ^ ((1 : ℝ) / 16) * Y ^ ((15 : ℝ) / 16) := by gcongr
      _ = A / 4 * (Y ^ ((15 : ℝ) / 16) * Y ^ ((1 : ℝ) / 16)) := by ring
      _ = A / 4 * Y := by rw [← hYsplit]
      _ = A * Y / 4 := by ring
  have hleft : A * Y / 4 ≤ ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ := by
    have := norm_sub_norm_le (∫ y in Y..2 * Y, G ((c : ℂ) + y * I))
      (∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I))
    have hb : ‖∫ x in σ'..c, G ((x : ℂ) + (Y : ℝ) * I)‖ +
        ‖∫ x in σ'..c, G ((x : ℂ) + ((2 * Y : ℝ) : ℂ) * I)‖ ≤ E * Y ^ ((15 : ℝ) / 16) := by
      linarith
    have hrect' := hrect
    push_cast at hrect' hb
    linarith
  -- pass to `‖Z‖`
  have hni : ‖∫ y in Y..2 * Y, G ((σ' : ℂ) + y * I)‖ ≤ ∫ y in Y..2 * Y, ‖G ((σ' : ℂ) + y * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hmono : ∫ y in Y..2 * Y, ‖G ((σ' : ℂ) + y * I)‖ ≤
      ∫ y in Y..2 * Y, mc * ‖Zf d ((σ' : ℂ) + y * I)‖ := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hcontG σ' Y hY1).norm.intervalIntegrable
    · exact ((hcontZ σ' Y hY1).const_smul mc).intervalIntegrable
    · intro y _; exact hGn σ' y hσc
  rw [intervalIntegral.integral_const_mul] at hmono
  have hfin : A * Y / 4 ≤ mc * ∫ y in Y..2 * Y, ‖Zf d ((σ' : ℂ) + y * I)‖ := by linarith
  have hmc0 : 0 < mc := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith


/-- `‖M(s)‖ ≤ ∫ |R(t)| t^{−σ−1} dt` on the line `Re s = σ`. -/
lemma norm_mellin_le (c σ y : ℝ) :
    ‖mellin (Rf a c) (-((σ : ℂ) - y * I))‖ ≤
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (-(σ : ℂ) - 1) • Rf a c t‖ := by
  unfold mellin
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [TauOmegaPM.norm_integrand ht0, TauOmegaPM.norm_integrand ht0]
  simp

/-- **The pointwise inequality** on the line `Re s = σ ∈ (0, 1/2]`, with `‖M(s)‖ ≤ L`. -/
lemma quarter_pt {cg : ℝ}
    (hΓ : ∀ σ y : ℝ, 0 < σ → σ ≤ 1 / 2 → 1 ≤ y →
      cg * y ^ (2 - 4 * σ) * ‖invGamM m (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
        ‖invGamM m ((σ : ℂ) - y * I)‖)
    {σ : ℝ} (h1 : 0 < σ) (h2 : σ ≤ 1 / 2) (c L : ℝ) {y : ℝ} (hy : 1 ≤ y) (M : ℂ)
    (hML : ‖M‖ ≤ L)
    (hid : Lam d ((σ : ℂ) - y * I) * invGamM m ((σ : ℂ) - y * I) =
      riemannZeta (2 * ((σ : ℂ) - y * I)) *
        (((σ : ℂ) - y * I) * M + c * ((σ : ℂ) - y * I) / (((σ : ℂ) - y * I) - 1))) :
    cg * y ^ (2 - 4 * σ) * ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
      ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ * (y * (2 * L + 2 * |c|)) := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) - y * I := ⟨_, rfl⟩
  rw [← hs] at hid ⊢
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((1 - σ : ℝ) : ℂ) + y * I := ⟨_, rfl⟩
  rw [← hw]
  have hw1s : w = 1 - s := by rw [hw, hs]; push_cast; ring
  have hG := hΓ σ y h1 h2 hy
  rw [← hs, ← hw] at hG
  have hLam : Lam d w = Lam d s := by rw [hw1s]; exact Lam_fe d s
  obtain ⟨X, hX⟩ : ∃ X : ℂ, X = s * M + c * s / (s - 1) := ⟨_, rfl⟩
  rw [← hX] at hid
  have hZ : Zf d w * invGamM m s = riemannZeta (2 * s) * X * invGamM m w := by
    rw [Zf, hLam, ← hid]; ring
  have hnorm := congrArg norm hZ
  simp only [norm_mul] at hnorm
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  have hiw : 0 < ‖invGamM m w‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := gamM_mul_invGamM m hwre
    rw [h, mul_zero] at this; exact zero_ne_one this
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = -y := by rw [hs]; simp
  have hZ1 : cg * y ^ (2 - 4 * σ) * ‖Zf d w‖ ≤ ‖riemannZeta (2 * s)‖ * ‖X‖ := by
    have : (cg * y ^ (2 - 4 * σ) * ‖Zf d w‖) * ‖invGamM m w‖ ≤
        (‖riemannZeta (2 * s)‖ * ‖X‖) * ‖invGamM m w‖ := by
      calc (cg * y ^ (2 - 4 * σ) * ‖Zf d w‖) * ‖invGamM m w‖
          = ‖Zf d w‖ * (cg * y ^ (2 - 4 * σ) * ‖invGamM m w‖) := by ring
        _ ≤ ‖Zf d w‖ * ‖invGamM m s‖ := by gcongr
        _ = _ := by rw [hnorm]
    exact le_of_mul_le_mul_right this hiw
  have hsn : ‖s‖ ≤ 2 * y := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim, abs_neg, abs_of_pos h1, abs_of_pos (by linarith)]
    linarith
  have hs1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = -y := by simp [hsim]
    rw [him, abs_neg, abs_of_pos (by linarith)] at this; linarith
  have hcs : ‖c * s / (s - 1)‖ ≤ 2 * |c| := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by linarith)]
    have : ‖s‖ ≤ ‖s - 1‖ + 1 := by
      have := norm_add_le (s - 1) 1; simp at this; linarith
    have := abs_nonneg c
    nlinarith
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) hML
  have hXn : ‖X‖ ≤ y * (2 * L + 2 * |c|) := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖s‖ * ‖M‖ ≤ 2 * y * L := by
      calc ‖s‖ * ‖M‖ ≤ (2 * y) * L := mul_le_mul hsn hML (norm_nonneg _) (by linarith)
        _ = _ := by ring
    have h4 : 2 * |c| ≤ y * (2 * |c|) := by
      have := abs_nonneg c; nlinarith
    linarith
  calc cg * y ^ (2 - 4 * σ) * ‖Zf d w‖ ≤ ‖riemannZeta (2 * s)‖ * ‖X‖ := hZ1
    _ ≤ _ := by gcongr

include d habs in
/-- **Mellin convergence on `Re s > β` with `β < 1/4` is impossible.** -/
theorem false_of_conv_quarter (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) {c β : ℝ}
    (hβ : β < 1 / 4) (hconv : ∀ s : ℂ, β < s.re → MellinConvergent (Rf a c) (-s)) : False := by
  obtain ⟨n0, hn0, hlow, ha0⟩ := exists_first hne
  set σ : ℝ := (max β (1 / 8) + 1 / 4) / 2 with hσ
  have hmx : max β (1 / 8) < 1 / 4 := max_lt hβ (by norm_num)
  have hσβ : β < σ := by rw [hσ]; linarith [le_max_left β (1 / 8)]
  have hσ8 : 1 / 8 < σ := by rw [hσ]; linarith [le_max_right β (1 / 8)]
  have hσ4 : σ < 1 / 4 := by rw [hσ]; linarith
  have hσ0 : 0 < σ := by linarith
  obtain ⟨cg, hcg, hΓ⟩ := gamma_ratio_lower' m hm
  obtain ⟨c3, hc3, Y0, hY0, hfm⟩ := Zf_first_moment' d habs hm hn0 hlow ha0
  obtain ⟨K, hK0, hζ⟩ := zeta_two_s_mean_sq hσ0 hσ4
  set L : ℝ := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (-(σ : ℂ) - 1) • Rf a c t‖ with hL
  have hL0 : 0 ≤ L := setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _
  set A : ℝ := 2 * L + 2 * |c| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set e : ℝ := 2 - 4 * σ with he
  have he1 : 1 < e := by rw [he]; linarith
  set p : ℝ := (3 - e) / 2 with hp
  set q : ℝ := (3 + e) / 2 with hq
  set B : ℝ := (K / 2 + 2 * A ^ 2) / (cg * c3) with hB
  -- choose `Y` large
  have hev : ∀ᶠ Y : ℝ in atTop, B < Y ^ ((e - 1) / 2) ∧ max Y0 1 ≤ Y :=
    ((tendsto_rpow_atTop (by linarith)).eventually_gt_atTop B).and (eventually_ge_atTop _)
  obtain ⟨Y, hYB, hYm⟩ := hev.exists
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hYm
  have hYY0 : Y0 ≤ Y := le_trans (le_max_left _ _) hYm
  have hY0' : 0 < Y := by linarith
  -- the pointwise bound on `[Y, 2Y]`
  set lam : ℝ := Y ^ p with hlam
  have hlam0 : 0 < lam := by positivity
  have hpt : ∀ y ∈ Icc Y (2 * Y),
      cg * Y ^ e * ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖ ≤
        lam / 2 * ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2 + (2 * Y * A) ^ 2 / (2 * lam) := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hY1 hy.1
    have hs : β < ((σ : ℂ) - y * I).re := by simpa using hσβ
    have him : ((σ : ℂ) - y * I).im < 0 := by simp; linarith
    have hid := Lam_eq_mellin_conv d habs c hconv hs him
    have h := quarter_pt d hΓ hσ0 (by linarith) c L hy1 _ (norm_mellin_le c σ y) hid
    rw [← hA] at h
    have hYe : Y ^ e ≤ y ^ e := Real.rpow_le_rpow (by linarith) hy.1 (by linarith)
    have hZ0 := norm_nonneg (Zf d (((1 - σ : ℝ) : ℂ) + y * I))
    set g := ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ with hg
    have hg0 : 0 ≤ g := norm_nonneg _
    have hyA : y * A ≤ 2 * Y * A := by
      have := hy.2; nlinarith
    have hamgm := amgm_aux (g := g) (X := 2 * Y * A) hlam0
    have e1 : (lam ^ 2 * g ^ 2 + (2 * Y * A) ^ 2) / (2 * lam) =
        lam / 2 * g ^ 2 + (2 * Y * A) ^ 2 / (2 * lam) := by field_simp
    calc cg * Y ^ e * ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖
        ≤ cg * y ^ e * ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖ := by gcongr
      _ ≤ g * (y * A) := h
      _ ≤ g * (2 * Y * A) := by gcongr
      _ ≤ _ := by rw [← e1]; exact hamgm
  -- continuity
  have hcZ : ContinuousOn (fun y : ℝ => ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖) (uIcc Y (2 * Y)) := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have him : 0 < (((1 - σ : ℝ) : ℂ) + y * I).im := by simp; linarith [hy.1]
    have h0 : ((1 - σ : ℝ) : ℂ) + y * I ≠ 0 := by intro h; rw [h] at him; simp at him
    have h1 : ((1 - σ : ℝ) : ℂ) + y * I ≠ 1 := by intro h; rw [h] at him; simp at him
    exact ((differentiableAt_Zf d h0 h1).continuousAt.comp
      (f := fun y : ℝ => ((1 - σ : ℝ) : ℂ) + y * I) (x := y) (by fun_prop)).norm.continuousWithinAt
  have hcζ : ContinuousOn (fun y : ℝ => ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2)
      (uIcc Y (2 * Y)) := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have hne : 2 * ((σ : ℂ) - y * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [hy.1]
    exact ((((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun y : ℝ => 2 * ((σ : ℂ) - y * I)) (x := y) (by fun_prop)).norm).pow 2).continuousWithinAt
  have hiZ := hcZ.intervalIntegrable (μ := volume)
  have hiζ := hcζ.intervalIntegrable (μ := volume)
  have hint := intervalIntegral.integral_mono_on (by linarith) (hiZ.const_mul (cg * Y ^ e))
    ((hiζ.const_mul (lam / 2)).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add (hiζ.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hint
  have hfm' := hfm (1 - σ) (by linarith) (by linarith) Y hYY0
  have hζ' := hζ Y hY1
  -- the inequality `cg c₃ Y^{e+1} ≤ (K/2 + 2A²) Y^q`
  have hkey : cg * c3 * Y ^ (e + 1) ≤ (K / 2 + 2 * A ^ 2) * Y ^ q := by
    have hYe0 : 0 ≤ Y ^ e := by positivity
    have h1 : cg * c3 * Y ^ (e + 1) ≤ cg * Y ^ e * ∫ y in Y..2 * Y,
        ‖Zf d (((1 - σ : ℝ) : ℂ) + y * I)‖ := by
      rw [Real.rpow_add hY0', Real.rpow_one]
      calc cg * c3 * (Y ^ e * Y) = cg * Y ^ e * (c3 * Y) := by ring
        _ ≤ _ := by gcongr
    have h2 : lam / 2 * ∫ y in Y..2 * Y, ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2 ≤
        lam / 2 * (K * Y ^ e) := by gcongr
    have h3 : lam / 2 * (K * Y ^ e) = K / 2 * Y ^ q := by
      rw [hlam, show K / 2 * Y ^ q = K / 2 * (Y ^ p * Y ^ e) by
        rw [← Real.rpow_add hY0', hp, hq]; ring_nf]
      ring
    have h4 : (2 * Y - Y) * ((2 * Y * A) ^ 2 / (2 * lam)) = 2 * A ^ 2 * Y ^ q := by
      have e3 : Y ^ q * Y ^ p = Y ^ (3 : ℝ) := by
        rw [← Real.rpow_add hY0']; congr 1; rw [hp, hq]; ring
      have e4 : Y ^ (3 : ℝ) = Y ^ 3 := by exact_mod_cast Real.rpow_natCast Y 3
      rw [hlam]
      field_simp
      rw [← e4, ← e3]; ring
    linarith
  -- contradiction
  have hsplit : Y ^ (e + 1) = Y ^ ((e - 1) / 2) * Y ^ q := by
    rw [← Real.rpow_add hY0']; congr 1; rw [hq]; ring
  rw [hsplit] at hkey
  have hYq : 0 < Y ^ q := by positivity
  have hc : cg * c3 * Y ^ ((e - 1) / 2) ≤ K / 2 + 2 * A ^ 2 := by
    have h' : (cg * c3 * Y ^ ((e - 1) / 2)) * Y ^ q ≤ (K / 2 + 2 * A ^ 2) * Y ^ q := by
      linarith
    exact le_of_mul_le_mul_right h' hYq
  have hcc : 0 < cg * c3 := by positivity
  rw [hB, div_lt_iff₀ hcc] at hYB
  linarith

include d habs in
/-- **`R = Ω±(x^β)` for every `β < 1/4`**, abstract Rankin–Selberg data with `|R(x)| ≤ C x^{3/5}`. -/
theorem rs_omega_pm_quarter (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) {C c : ℝ}
    (hR : ∀ x : ℝ, 1 ≤ x → ‖Rf a c x‖ ≤ C * x ^ ((3 : ℝ) / 5)) {β : ℝ} (hβ : β < 1 / 4)
    (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧ c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x) := by
  set β' : ℝ := max β (1 / 40) with hβ'
  have hβ'0 : 0 < β' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ'1 : β' < 1 / 4 := max_lt hβ (by norm_num)
  set X' : ℝ := max X 2 with hX'
  have hpow : ∀ x : ℝ, X' ≤ x → |c1| * x ^ β ≤ |c1| * x ^ β' := by
    intro x hx
    have hx1 : 1 ≤ x := le_trans (by norm_num) (le_trans (le_max_right _ _) hx)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
      (abs_nonneg _)
  have hreX : ∀ x : ℝ, X' ≤ x → (Rf a c x).re = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - c * x := by
    intro x hx
    exact Rf_re_of_one_lt c (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx))
  have hc1 : ∀ x : ℝ, X' ≤ x → -|c1| * x ^ β' ≤ -c1 * x ^ β := by
    intro x hx
    have h1 := hpow x hx
    have hx0 : 0 ≤ x ^ β := Real.rpow_nonneg (by linarith [le_max_right X 2]) β
    have : c1 * x ^ β ≤ |c1| * x ^ β := mul_le_mul_of_nonneg_right (le_abs_self c1) hx0
    linarith
  have hc1' : ∀ x : ℝ, X' ≤ x → c1 * x ^ β ≤ |c1| * x ^ β' := by
    intro x hx
    have h1 := hpow x hx
    have hx0 : 0 ≤ x ^ β := Real.rpow_nonneg (by linarith [le_max_right X 2]) β
    have : c1 * x ^ β ≤ |c1| * x ^ β := mul_le_mul_of_nonneg_right (le_abs_self c1) hx0
    linarith
  constructor
  · by_contra hcon
    push Not at hcon
    have h : ∀ x ≥ X', -|c1| * x ^ β' ≤ 1 * (Rf a c x).re := by
      intro x hx
      rw [one_mul, hreX x hx]
      exact (hc1 x hx).trans (hcon x (le_trans (le_max_left _ _) hx))
    exact false_of_conv_quarter d habs hm hne hβ'1
      (conv_of_one_sided d habs hR hβ'0 (by linarith) (Or.inl rfl) h)
  · by_contra hcon
    push Not at hcon
    have h : ∀ x ≥ X', -|c1| * x ^ β' ≤ -1 * (Rf a c x).re := by
      intro x hx
      rw [hreX x hx]
      have := (hcon x (le_trans (le_max_left _ _) hx))
      have := hc1' x hx
      linarith
    exact false_of_conv_quarter d habs hm hne hβ'1
      (conv_of_one_sided d habs hR hβ'0 (by linarith) (Or.inr rfl) h)

end Quarter

section Cusp

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn
open ModularForm
open scoped MatrixGroups

variable {k : ℕ}

/-- **Ω±(x^β), `β < 1/4`, for every nonzero level-one cusp form**, given a `3/5` bound for `c`. -/
theorem cuspForm_omega_pm_quarter_of_bound (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (c : ℝ)
    (hC : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - c * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5))
    {β : ℝ} (hβ : β < 1 / 4) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - c * x) := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (cuspForm_eq_zero_of_lt f (by omega))
  letI := rsFnCusp f (by omega)
  have hm : 2 ≤ RSFn.m := show 2 ≤ k - 1 by omega
  obtain ⟨n, hn1, hn⟩ := exists_coeff_ne_zero f hf (by omega)
  have hne : ∃ n, 0 < n ∧ aF n ≠ 0 := by
    refine ⟨n, hn1, ?_⟩
    show coeffSq f n / (n : ℝ) ^ (k - 1) ≠ 0
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact div_ne_zero hn (by positivity)
  obtain ⟨C, hC⟩ := hC
  have hR := hR_of_nat (a := aF) (c := c) (C := C) hC
  exact rs_omega_pm_quarter rsDataG (abscissa_aF_le_one hm) (by omega) hne hR hβ c1 X

/-- **Ω±(x^β), `β < 1/4`, for every nonzero level-one cusp form** with its Rankin constant. -/
theorem cuspForm_rankin_omega_pm_quarter (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    {β : ℝ} (hβ : β < 1 / 4) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * x < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * x) :=
  cuspForm_omega_pm_quarter_of_bound f hf _ (RankinExact.rankinSelberg_exact_general f) hβ c1 X

end Cusp

section Tau

open RamanujanTau.RankinSelbergGeneral
open ModularForm
open scoped MatrixGroups

/-- **Headline (τ, Rankin's constant): `R(x) = Ω±(x^β)` for every `β < 1/4`.**
For every real `c₁` and every `X` there are `x, x' ≥ X` with `R(x) < −c₁ x^β` and `R(x') > c₁ x'^β`,
`R(x) = ∑_{n≤x} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11!·x`. -/
theorem tau_rankin_omega_pm_quarter {β : ℝ} (hβ : β < 1 / 4) (c1 X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * x
        < -c1 * x ^ β) ∧
    (∃ x : ℝ, X ≤ x ∧
      c1 * x ^ β < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * x) := by
  have hC : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, coeffSq (k := 12)
          (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n / (n : ℝ) ^ (12 - 1) -
        3 / Real.pi * (4 * Real.pi) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
    obtain ⟨C, hC⟩ := RankinExact.rankinSelberg_exact
    refine ⟨C, fun N hN => ?_⟩
    simp only [coeffSq_discriminant]
    exact hC N hN
  have h := cuspForm_omega_pm_quarter_of_bound (k := 12) _ discriminant_ne_zero' _ hC hβ c1 X
  simp only [coeffSq_discriminant] at h
  exact h

end Tau

end RamanujanTau.ZetaMeanSquare
