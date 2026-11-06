/-
# Riesz–Perron approximation of `L(f, k/2 + it)` (weight-`k` copy of `MeanSquare.approx_tauL`)

`approx_fL`: for `12 ≤ k`, `0 < δ ≤ 1/2`, `ε > 0`, `1/2 + δ + ε ≤ 2`, there is `C` with

    ‖L(f, k/2+it) − Σ_{n≤X} a_f(n) (1 − n/X)³ n^{−k/2−it}‖ ≤ C X^{−δ} (1+|t|)^{1/2+δ+ε}

for all `X ≥ 1`, real `t`.  Same proof as `approx_tauL` at `σ = 6`: Perron (`perron_c`) on
`Re w = 1`, `shift_identity` to `Re w = −δ`, convexity `fL_convexity_strip` on `Re = k/2 − δ`;
the strip growth `fL_growth` comes from `HeckeConvexGeneral.fC_bound`/`fL_line`.  Only the
abscissae are shifted by `k/2 − 6`.
-/
import RamanujanTau.SubconvexGeneral.GOffDiag

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError RamanujanTau.MeanSquare RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- `‖L(f,z)‖ ≤ K (1+|Im z|)²` on `k/2 − 1 ≤ Re z ≤ k/2 + 1`. -/
lemma fL_growth (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ,
    (k : ℝ) / 2 - 1 ≤ z.re → z.re ≤ (k : ℝ) / 2 + 1 → ‖fL f z‖ ≤ K * (1 + |z.im|) ^ 2 := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := fC_bound f hk (ε := 1 / 2) (by norm_num) le_rfl
  set M : ℝ := (k : ℝ) / 2 + 1 with hM
  refine ⟨2 * Real.exp 10 * C * M ^ 2, by positivity, fun z h1 h2 => ?_⟩
  have hL := fL_line f hk (ε := 1 / 2) (by norm_num) le_rfl hC (s := z)
    (by linarith) (by linarith)
  have hn1 : 1 ≤ ‖z / 2‖ := by
    rw [norm_div, Complex.norm_two, le_div_iff₀ (by norm_num)]
    have := Complex.abs_re_le_norm z
    rw [abs_of_nonneg (by linarith)] at this; linarith
  have hn2 : ‖z / 2‖ ≤ M * (1 + |z.im|) := by
    rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z.re)]
    nlinarith [abs_nonneg z.im]
  have h3 : ‖z / 2‖ ^ (((k : ℝ) + 1) / 2 + 1 / 2 - z.re) ≤ ‖z / 2‖ ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h4 : ‖z / 2‖ ^ (2 : ℝ) ≤ (M * (1 + |z.im|)) ^ 2 := by
    rw [Real.rpow_two]; exact pow_le_pow_left₀ (norm_nonneg _) hn2 2
  calc ‖fL f z‖ ≤ 2 * Real.exp 10 * C * ‖z / 2‖ ^ (((k : ℝ) + 1) / 2 + 1 / 2 - z.re) := hL
    _ ≤ 2 * Real.exp 10 * C * (M * (1 + |z.im|)) ^ 2 := by gcongr; exact h3.trans h4
    _ = _ := by ring

/-- The coefficients `a_f(n) n^{−s}`. -/
noncomputable def aSF (f : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) (n : ℕ) : ℂ := coef f n * (n : ℂ) ^ (-s)

lemma aSF_zero (f : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : aSF f s 0 = 0 := by simp [aSF, coef_zero]

lemma LSeries_aSF (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s w : ℂ}
    (h : ((k : ℝ) + 1) / 2 < (s + w).re) : LSeries (aSF f s) w = fL f (s + w) := by
  rw [fL_eq_LSeries f hk h, LSeries, LSeries]
  congr 1; funext n
  rw [LSeries.term_def, LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [if_neg hn, if_neg hn, aSF, mul_div_assoc, ← cpow_sub _ _ hn0,
      show -s - w = -(s + w) by ring, cpow_neg, div_eq_mul_inv]

lemma summable_aSF (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {s : ℂ} {c : ℝ}
    (h : s.re + c = (k : ℝ) / 2 + 1) :
    Summable fun n : ℕ => ‖aSF f s n‖ * (n : ℝ) ^ (-c) := by
  have h7 := summable_norm_coef_div_rpow f hk (σ := (k : ℝ) / 2 + 1) (by linarith)
  refine h7.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aSF, coef_zero]
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [aSF, norm_mul, norm_natCast_cpow_neg hn.ne', mul_assoc, ← Real.rpow_add hnr,
      show -s.re + -c = -((k : ℝ) / 2 + 1) by linarith, Real.rpow_neg hnr.le, div_eq_mul_inv]

/-- The Riesz-smoothed coefficients `a_f(n) n^{−σ} (1 − n/X)₊³`. -/
noncomputable def bsmF (f : CuspForm 𝒮ℒ (k : ℤ)) (σ X : ℝ) (n : ℕ) : ℂ :=
  coef f n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (phi 3 (n / X) : ℂ)

lemma tsum_eq_dpolyF (f : CuspForm 𝒮ℒ (k : ℤ)) {σ X : ℝ} (hX : 0 < X) (t : ℝ) :
    ∑' n : ℕ, aSF f ((σ : ℂ) + t * I) n * (phi 3 (n / X) : ℂ) = dpoly (bsmF f σ X) ⌊X⌋₊ t := by
  rw [tsum_eq_sum (s := range (⌊X⌋₊ + 1))]
  · rw [dpoly, sum_Icc_eq_sum_range (g := fun n => bsmF f σ X n * ex (-Real.log n) t)
      (by simp [bsmF, coef_zero])]
    refine sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [aSF_zero, bsmF, coef_zero]
    · rw [aSF, cpow_neg, natCast_cpow_inv hn, bsmF]; ring
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h1 : X < n := by
      have := Nat.lt_floor_add_one X
      have : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this; linarith
    have : 1 < (n : ℝ) / X := by rw [one_lt_div hX]; exact h1
    rw [phi_of_gt (by norm_num) this]; simp

/-- **Approximation of `L(f, k/2+it)` by a smoothed Dirichlet polynomial of length `X`.** -/
theorem approx_fL (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hε : 0 < ε) (hθ : 1 / 2 + δ + ε ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ t : ℝ,
      ‖fL f ((((k : ℝ) / 2 : ℝ) : ℂ) + t * I) - dpoly (bsmF f ((k : ℝ) / 2) X) ⌊X⌋₊ t‖ ≤
        C * X ^ (-δ) * (1 + |t|) ^ (1 / 2 + δ + ε) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set σ : ℝ := (k : ℝ) / 2 with hσ
  set θ := 1 / 2 + δ + ε with hθdef
  obtain ⟨K0, hK00, hK0⟩ := fL_growth f hk
  obtain ⟨Kc, hKc0, hKc⟩ := fL_convexity_strip f hε
  set A : ℝ := 6 * (2 / min (-(-δ)) (1 + -δ)) ^ 4 with hA
  have hA0 : 0 ≤ A := by
    have : 0 < min (-(-δ)) (1 + -δ) := lt_min (by linarith) (by linarith)
    positivity
  set J : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  refine ⟨Kc * (3 + A * J / π), by positivity, fun X hX t => ?_⟩
  have hX0 : 0 < X := by linarith
  set s : ℂ := (σ : ℂ) + t * I with hs
  set c : ℝ := 1 with hc
  have hc0 : 0 < c := by rw [hc]; norm_num
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  set F : ℂ → ℂ := fun w => fL f (s + w) with hF
  have hFd : Differentiable ℂ F := (fL_entire f hk1).comp (differentiable_const _ |>.add
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
  have hP := perron_c (aSF f s) (aSF_zero f s) (k := 3) (by norm_num) hc0 hX0
    (summable_aSF f hk1 (by rw [hsre, hc]))
  have hLS : (fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * LSeries (aSF f s) (ln c y)) =
      fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) := by
    funext y
    rw [LSeries_aSF f hk1 (by simp [hsre, ln, hc]; linarith)]
  rw [hLS, shift_identity hFd hX hc0 hδ0 (by linarith) hK, tsum_eq_dpolyF f hX0 t] at hP
  -- notation
  set D := dpoly (bsmF f σ X) ⌊X⌋₊ t with hD
  set Ig := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y) with hIg
  set IX := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) with hIX
  have hF0 : F 0 = fL f s := by simp [hF]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hkey : fL f s - D = -(F 0 * ((phi 3 (1 / X) : ℂ) - 1)) - (Ig - F 0 * IX) / (2 * π) := by
    rw [hF0] at hP ⊢
    field_simp
    linear_combination (-1 : ℂ) * hP
  -- bounds
  have hF0b : ‖F 0‖ ≤ Kc * (1 + |t|) ^ θ := by
    rw [hF0]
    have := hKc σ t (by linarith) (by linarith)
    refine this.trans ?_
    gcongr
    · linarith [abs_nonneg t]
    · linarith
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
        have := hKc (σ - δ) (t + y) (by linarith) (by linarith)
        have he : ((k : ℝ) + 1) / 2 - (σ - δ) + ε = θ := by rw [hθdef, hσ]; ring
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

end RamanujanTau.SubconvexGeneral
