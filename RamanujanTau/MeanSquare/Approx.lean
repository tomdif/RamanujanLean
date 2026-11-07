/-
# Approximating `L(Δ,s)` in the strip by a Riesz-smoothed Dirichlet polynomial

`approx_tauL`: for `6 ≤ σ ≤ 13/2`, `0 < δ < 1`, `σ − δ ≥ 11/2`, `ε > 0` with
`θ = 13/2 − σ + δ + ε ≤ 2`, there is `C` with, for all `X ≥ 1` and real `t`,

    |L(Δ, σ+it) − ∑_{n ≤ X} τ(n) (1 − n/X)³ n^{-σ-it}| ≤ C X^{-δ} (1+|t|)^θ.

Proof: Perron (`perron_c`) on `Re w = c = 7 − σ` writes the smoothed sum as
`(1/2π)∫ X^w P₃(w) L(Δ, s+w) dw`; `shift_identity` moves the line to `Re w = −δ`, picking up
`L(Δ,s) φ₃(1/X)` at `w = 0`; on `Re w = −δ` the convexity bound
`HeckeConvex.tauL_convexity_strip` at `Re(s+w) = σ − δ ∈ [11/2, 13/2]` gives
`‖L(Δ,s+w)‖ ≤ K (1+|t|)^θ (1+|Im w|)^θ`, integrable against `|P₃| ≪ (1+|Im w|)^{-4}`.
In the strip `5 ≤ Re ≤ 7` the crude bound `‖L(Δ,z)‖ ≪ (1+|Im z|)²` (`tauL_growth`, from
`HeckeConvex.tauL_line` with `ε = 1/2`) justifies the shift.
-/
import RamanujanTau.MeanSquare.Shift
import RamanujanTau.MeanSquare.AbsConv

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError RamanujanTau.HeckeL

/-- `‖L(Δ,z)‖ ≤ K (1+|Im z|)²` on `5 ≤ Re z ≤ 7`. -/
lemma tauL_growth : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 5 ≤ z.re → z.re ≤ 7 →
    ‖tauL z‖ ≤ K * (1 + |z.im|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.HeckeConvex.fC_bound (ε := 1 / 2) (by norm_num) le_rfl
  refine ⟨2 * Real.exp 10 * C * 16, by positivity, fun z h1 h2 => ?_⟩
  have hL := RamanujanTau.HeckeConvex.tauL_line (ε := 1 / 2) (by norm_num) le_rfl hC (s := z)
    (by linarith) (by linarith)
  have hn1 : 1 ≤ ‖z / 2‖ := by
    rw [norm_div, Complex.norm_two, le_div_iff₀ (by norm_num)]
    have := Complex.abs_re_le_norm z
    rw [abs_of_nonneg (by linarith)] at this; linarith
  have hn2 : ‖z / 2‖ ≤ 4 * (1 + |z.im|) := by
    rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z.re)]; linarith [abs_nonneg z.im]
  have h3 : ‖z / 2‖ ^ (13 / 2 + 1 / 2 - z.re) ≤ ‖z / 2‖ ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4 : ‖z / 2‖ ^ (2 : ℝ) ≤ (4 * (1 + |z.im|)) ^ 2 := by
    rw [Real.rpow_two]; exact pow_le_pow_left₀ (norm_nonneg _) hn2 2
  calc ‖tauL z‖ ≤ 2 * Real.exp 10 * C * ‖z / 2‖ ^ (13 / 2 + 1 / 2 - z.re) := hL
    _ ≤ 2 * Real.exp 10 * C * (4 * (1 + |z.im|)) ^ 2 := by gcongr; exact h3.trans h4
    _ = _ := by ring

lemma one_add_abs_add_le (a b : ℝ) : 1 + |a + b| ≤ (1 + |a|) * (1 + |b|) := by
  have := abs_add_le a b
  nlinarith [abs_nonneg a, abs_nonneg b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- The coefficients `aₙ = τ(n) n^{-s}`. -/
noncomputable def aS (s : ℂ) (n : ℕ) : ℂ := RamanujanTau.tauC n * (n : ℂ) ^ (-s)

lemma aS_zero (s : ℂ) : aS s 0 = 0 := by simp [aS, RamanujanTau.tauC, tau_zero]

lemma LSeries_aS {s w : ℂ} (h : 13 / 2 < (s + w).re) : LSeries (aS s) w = tauL (s + w) := by
  rw [RamanujanTau.HeckeConvex.tauL_eq_LSeries_of_gt h, LSeries, LSeries]
  congr 1; funext n
  rw [LSeries.term_def, LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [if_neg hn, if_neg hn, aS, mul_div_assoc, ← cpow_sub _ _ hn0,
      show -s - w = -(s + w) by ring, cpow_neg, div_eq_mul_inv]

lemma summable_aS {s : ℂ} {c : ℝ} (h : s.re + c = 7) :
    Summable fun n : ℕ => ‖aS s n‖ * (n : ℝ) ^ (-c) := by
  have h7 := RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (σ := 7) (by norm_num)
  refine h7.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aS, RamanujanTau.tauC, tau_zero]
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [aS, norm_mul, norm_natCast_cpow_neg hn.ne', RamanujanTau.tauC, Complex.norm_intCast,
      mul_assoc, ← Real.rpow_add hnr, show -s.re + -c = -7 by linarith,
      Real.rpow_neg hnr.le, div_eq_mul_inv]

/-- The Riesz-smoothed coefficients `τ(n) n^{-σ} (1 − n/X)₊³`. -/
noncomputable def bsm (σ X : ℝ) (n : ℕ) : ℂ :=
  (tau n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (phi 3 (n / X) : ℂ)

lemma tsum_eq_dpoly {σ X : ℝ} (hX : 0 < X) (t : ℝ) :
    ∑' n : ℕ, aS ((σ : ℂ) + t * I) n * (phi 3 (n / X) : ℂ) = dpoly (bsm σ X) ⌊X⌋₊ t := by
  rw [tsum_eq_sum (s := range (⌊X⌋₊ + 1))]
  · rw [dpoly, sum_Icc_eq_sum_range (g := fun n => bsm σ X n * ex (-Real.log n) t)
      (by simp [bsm, tau_zero])]
    refine sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [aS_zero, bsm, tau_zero]
    · rw [aS, cpow_neg, natCast_cpow_inv hn, bsm, RamanujanTau.tauC]; ring
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h1 : X < n := by
      have := Nat.lt_floor_add_one X
      have : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this; linarith
    have : 1 < (n : ℝ) / X := by rw [one_lt_div hX]; exact h1
    rw [phi_of_gt (by norm_num) this]; simp

lemma one_sub_phi_le {X : ℝ} (hX : 1 ≤ X) : |phi 3 (1 / X) - 1| ≤ 3 / X := by
  have hX0 : 0 < X := by linarith
  have hu : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX
  rw [phi_of_le hu]
  have h0 : 0 ≤ 1 - 1 / X := by linarith
  have hpos : 0 < 1 / X := by positivity
  have h1 : (1 - 1 / X) ^ 3 ≤ 1 := pow_le_one₀ h0 (by linarith)
  have h2 := one_add_mul_le_pow (a := -(1 / X)) (by
    have : 1 / X ≤ 1 := hu; linarith) 3
  rw [abs_of_nonpos (by linarith)]
  have e : (1 : ℝ) + -(1 / X) = 1 - 1 / X := by ring
  rw [e] at h2
  push_cast at h2
  have : 3 * (1 / X) = 3 / X := by ring
  linarith

/-- **Approximation of `L(Δ, σ+it)` by a smoothed Dirichlet polynomial of length `X`.** -/
theorem approx_tauL {σ δ ε : ℝ} (hσ1 : 6 ≤ σ) (hσ2 : σ ≤ 13 / 2) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hσδ : 11 / 2 ≤ σ - δ) (hε : 0 < ε) (hθ : 13 / 2 - σ + δ + ε ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ t : ℝ,
      ‖tauL ((σ : ℂ) + t * I) - dpoly (bsm σ X) ⌊X⌋₊ t‖ ≤
        C * X ^ (-δ) * (1 + |t|) ^ (13 / 2 - σ + δ + ε) := by
  set θ := 13 / 2 - σ + δ + ε with hθdef
  obtain ⟨K0, hK00, hK0⟩ := tauL_growth
  obtain ⟨Kc, hKc0, hKc⟩ := RamanujanTau.HeckeConvex.tauL_convexity_strip hε
  set A : ℝ := 6 * (2 / min (-(-δ)) (1 + -δ)) ^ 4 with hA
  have hA0 : 0 ≤ A := by
    have : 0 < min (-(-δ)) (1 + -δ) := lt_min (by linarith) (by linarith)
    positivity
  set J : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  refine ⟨Kc * (3 + A * J / π), by positivity, fun X hX t => ?_⟩
  have hX0 : 0 < X := by linarith
  set s : ℂ := (σ : ℂ) + t * I with hs
  set c : ℝ := 7 - σ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  set F : ℂ → ℂ := fun w => tauL (s + w) with hF
  have hFd : Differentiable ℂ F := tauLSeries_entire.comp (differentiable_const _ |>.add
    differentiable_id)
  have ht1 : (0 : ℝ) < 1 + |t| := by positivity
  -- growth of `F` in the strip
  have hK : ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖F w‖ ≤ (K0 * (1 + |t|) ^ 2) * (1 + |w.im|) ^ 2 := by
    intro w h1 h2
    have hre : (s + w).re = σ + w.re := by simp [hsre]
    have him : (s + w).im = t + w.im := by simp [hsim]
    have := hK0 (s + w) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at this
    refine this.trans ?_
    have h3 := one_add_abs_add_le t w.im
    calc K0 * (1 + |t + w.im|) ^ 2 ≤ K0 * ((1 + |t|) * (1 + |w.im|)) ^ 2 := by
          gcongr
      _ = _ := by ring
  -- Perron
  have hP := perron_c (aS s) (aS_zero s) (k := 3) (by norm_num) hc0 hX0
    (summable_aS (by rw [hsre, hc]; ring))
  have hLS : (fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * LSeries (aS s) (ln c y)) =
      fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) := by
    funext y
    rw [LSeries_aS (by simp [hsre, ln, hc]; norm_num)]
  rw [hLS, shift_identity hFd hX hc0 hδ0 hδ1 hK, tsum_eq_dpoly hX0 t] at hP
  -- notation
  set D := dpoly (bsm σ X) ⌊X⌋₊ t with hD
  set Ig := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y) with hIg
  set IX := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) with hIX
  have hF0 : F 0 = tauL s := by simp [hF]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hkey : tauL s - D = -(F 0 * ((phi 3 (1 / X) : ℂ) - 1)) - (Ig - F 0 * IX) / (2 * π) := by
    rw [hF0] at hP ⊢
    field_simp
    linear_combination (-1 : ℂ) * hP
  -- bounds
  have hXδ : X ^ (-δ) * X ^ (-δ) ≥ 0 := by positivity
  have hθ1 : 13 / 2 - σ + ε ≤ θ := by rw [hθdef]; linarith
  have hF0b : ‖F 0‖ ≤ Kc * (1 + |t|) ^ θ := by
    rw [hF0]
    have := hKc σ t (by linarith) hσ2
    refine this.trans ?_
    gcongr
    · linarith [abs_nonneg t]
  have hphi : ‖((phi 3 (1 / X) : ℂ) - 1)‖ ≤ 3 * X ^ (-δ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1X : 1 / X ≤ X ^ (-δ) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    calc |phi 3 (1 / X) - 1| ≤ 3 / X := one_sub_phi_le hX
      _ = 3 * (1 / X) := by ring
      _ ≤ 3 * X ^ (-δ) := by gcongr
  have hlineP : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ ≤ X ^ (-δ) * A / (1 + |y|) ^ 4 := by
    intro y
    rw [norm_mul, norm_X_cpow hX0]
    have hre : (ln (-δ) y).re = -δ := by simp [ln]
    rw [hre]
    have := norm_Pk3_le_left (σ := -δ) (by linarith) (by linarith) y
    rw [mul_div_assoc]
    gcongr
  have hIX : ‖IX‖ ≤ X ^ (-δ) * A * J := by
    have hb : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ ≤ X ^ (-δ) * A / (1 + |y|) ^ 2 := by
      intro y
      refine (hlineP y).trans ?_
      have h1y : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
      have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 4 := pow_le_pow_right₀ h1y (by norm_num)
      gcongr
    refine (norm_integral_le_of_norm_le (integrable_div_sq _) (ae_of_all _ hb)).trans
      (le_of_eq ?_)
    rw [hJ, ← integral_const_mul]
    congr 1; funext y; ring
  have hIg : ‖Ig‖ ≤ X ^ (-δ) * A * Kc * (1 + |t|) ^ θ * J := by
    have hb : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y)‖ ≤
        X ^ (-δ) * A * Kc * (1 + |t|) ^ θ / (1 + |y|) ^ 2 := by
      intro y
      rw [norm_mul]
      have hFy : ‖F (ln (-δ) y)‖ ≤ Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ := by
        have e : s + ln (-δ) y = ((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
          simp only [hs, ln]; push_cast; ring
        simp only [hF]
        rw [e]
        have := hKc (σ - δ) (t + y) hσδ (by linarith)
        have he : 13 / 2 - (σ - δ) + ε = θ := by rw [hθdef]; ring
        rw [he] at this
        refine this.trans ?_
        have h3 := one_add_abs_add_le t y
        have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
        calc Kc * (1 + |t + y|) ^ θ ≤ Kc * ((1 + |t|) * (1 + |y|)) ^ θ := by
              gcongr
          _ = Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ := by
              rw [Real.mul_rpow ht1.le (by positivity)]; ring
      have hy1 : (0 : ℝ) < 1 + |y| := by positivity
      have hyθ : (1 + |y|) ^ θ ≤ (1 + |y|) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) hθ
      rw [Real.rpow_two] at hyθ
      calc ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ * ‖F (ln (-δ) y)‖
          ≤ (X ^ (-δ) * A / (1 + |y|) ^ 4) * (Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ) :=
            mul_le_mul (hlineP y) hFy (norm_nonneg _) (by positivity)
        _ ≤ (X ^ (-δ) * A / (1 + |y|) ^ 4) * (Kc * (1 + |t|) ^ θ * (1 + |y|) ^ 2) := by
            gcongr
        _ = X ^ (-δ) * A * Kc * (1 + |t|) ^ θ / (1 + |y|) ^ 2 := by
            field_simp
    refine (norm_integral_le_of_norm_le (integrable_div_sq _) (ae_of_all _ hb)).trans
      (le_of_eq ?_)
    rw [hJ, ← integral_const_mul]
    congr 1; funext y; ring
  -- combine
  rw [hkey]
  have hnorm2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hπ : 0 < π := Real.pi_pos
  calc ‖-(F 0 * ((phi 3 (1 / X) : ℂ) - 1)) - (Ig - F 0 * IX) / (2 * π)‖
      ≤ ‖F 0‖ * ‖((phi 3 (1 / X) : ℂ) - 1)‖ + (‖Ig‖ + ‖F 0‖ * ‖IX‖) / (2 * π) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, norm_div, hnorm2π]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ (Kc * (1 + |t|) ^ θ) * (3 * X ^ (-δ)) +
          (X ^ (-δ) * A * Kc * (1 + |t|) ^ θ * J + (Kc * (1 + |t|) ^ θ) * (X ^ (-δ) * A * J)) /
            (2 * π) := by
        gcongr
    _ = Kc * (3 + A * J / π) * X ^ (-δ) * (1 + |t|) ^ θ := by
        field_simp; ring

end RamanujanTau.MeanSquare
