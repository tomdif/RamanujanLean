/-
# The main term on a Ford segment

`∫_ℝ W(k+iu) du = (π/12k)^{3/2} · 2π · Σ_m y^m/(m!Γ(m+5/2))` with `y = π²(n−1/24)/(6k²)` (`fullLine`), by
rescaling `u = t/a` to the Bessel line integral. Also `‖W(k+iu)‖ ≤ e^{π/12 + 2πn}(k²+u²)^{−5/4}` (`norm_Wf_le`),
so the tails beyond the segment are small (`tail_bound`).
-/
import RamanujanTau.Rademacher.Integrand
import RamanujanTau.Rademacher.Bessel

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Filter Metric MeasureTheory Set
open scoped Real Topology

noncomputable section

lemma ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : s ≠ 0) (w : ℂ) :
    ((r : ℂ) * s) ^ w = (r : ℂ) ^ w * s ^ w := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hs), Complex.log_ofReal_mul hr hs,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), cpow_def_of_ne_zero hs, ← Complex.exp_add,
    ofReal_log hr.le]
  congr 1; ring

/-- `y = π²(n − 1/24)/(6k²)`. -/
def yk (k n : ℕ) : ℝ := π ^ 2 * ((n : ℝ) - 1 / 24) / (6 * k ^ 2)

/-- **the full line**. -/
theorem fullLine {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) :
    ∫ u : ℝ, Wf k n ((k : ℂ) + u * I) =
      ((π / (12 * k)) ^ (3 / 2 : ℝ) : ℝ) * (2 * π * ∑' m, (bco (yk k n) m : ℂ)) := by
  set a : ℝ := π / (12 * k) with ha
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 < a := by positivity
  have hy : 0 ≤ yk k n := by
    unfold yk
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) ≤ (n : ℝ) - 1 / 24 := by linarith
    positivity
  have hc : (0 : ℝ) < π / 12 := by positivity
  have hB := bessel_line hy hc
  -- substitution `u = t/a`
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => Wf k n ((k : ℂ) + ((t / a : ℝ) : ℂ) * I)) a
  have e1 : ∀ u : ℝ, (fun t : ℝ => Wf k n ((k : ℂ) + ((t / a : ℝ) : ℂ) * I)) (a * u) = Wf k n ((k : ℂ) + u * I) := by
    intro u
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    simp only; congr 3; push_cast; field_simp
  simp only [e1] at hsub
  rw [hsub, abs_of_pos (inv_pos.mpr ha0), Complex.real_smul]
  -- the rescaled integrand
  have e2 : ∀ t : ℝ, Wf k n ((k : ℂ) + ((t / a : ℝ) : ℂ) * I) =
      ((a ^ (5 / 2 : ℝ) : ℝ) : ℂ) * (((π / 12 : ℝ) : ℂ) + t * I) ^ (-(5 / 2 : ℂ)) *
        cexp ((((π / 12 : ℝ) : ℂ) + t * I) + (yk k n : ℂ) / (((π / 12 : ℝ) : ℂ) + t * I)) := by
    intro t
    have hs : ((π / 12 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; try linarith [Real.pi_pos]
    have hw : (k : ℂ) + ((t / a : ℝ) : ℂ) * I = ((1 / a : ℝ) : ℂ) * (((π / 12 : ℝ) : ℂ) + t * I) := by
      rw [ha]; push_cast; field_simp; try ring
    unfold Wf
    rw [hw, ofReal_mul_cpow (by positivity) hs]
    have hpow : ((1 / a : ℝ) : ℂ) ^ (-(5 / 2 : ℂ)) = ((a ^ (5 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (-(5 / 2 : ℂ)) = ((-(5 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
        one_div, Real.inv_rpow ha0.le, Real.rpow_neg ha0.le, inv_inv]
    have hexp : (π : ℂ) / (12 * k) * (((1 / a : ℝ) : ℂ) * (((π / 12 : ℝ) : ℂ) + t * I)) +
        2 * π / k * ((n : ℂ) - 1 / 24) / (((1 / a : ℝ) : ℂ) * (((π / 12 : ℝ) : ℂ) + t * I)) =
        (((π / 12 : ℝ) : ℂ) + t * I) + (yk k n : ℂ) / (((π / 12 : ℝ) : ℂ) + t * I) := by
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      rw [ha]
      unfold yk
      push_cast
      field_simp
      ring
    rw [hpow, hexp, mul_assoc]
  simp only [e2, mul_assoc, integral_const_mul]
  rw [hB]
  have hr : a⁻¹ * a ^ (5 / 2 : ℝ) = a ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add ha0, Real.rpow_one, ← mul_assoc,
      inv_mul_cancel₀ ha0.ne', one_mul]
  rw [← mul_assoc, ← ofReal_mul, hr]
  ring

/-! ### bounds -/

lemma normSq_wk (k : ℕ) (u : ℝ) : ‖(k : ℂ) + u * I‖ ^ 2 = (k : ℝ) ^ 2 + u ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- the constant `e^{π/12 + 2πn}`. -/
def Cn (n : ℕ) : ℝ := Real.exp (π / 12 + 2 * π * n)

lemma norm_Wf_le {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (u : ℝ) :
    ‖Wf k n ((k : ℂ) + u * I)‖ ≤ Cn n * ((k : ℝ) ^ 2 + u ^ 2) ^ (-(5 / 4 : ℝ)) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hw0 := wk_ne hk u
  have hq : 0 < (k : ℝ) ^ 2 + u ^ 2 := by positivity
  unfold Wf
  rw [norm_mul, norm_cpow_of_ne_zero hw0, norm_exp]
  simp only [neg_im, div_ofNat_im, re_ofNat, im_ofNat, zero_div, neg_zero, mul_zero, Real.exp_zero, div_one,
    neg_re, div_ofNat_re]
  have hn1 : ‖(k : ℂ) + u * I‖ = ((k : ℝ) ^ 2 + u ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← normSq_wk, Real.sqrt_sq (norm_nonneg _)]
  have hp : ‖(k : ℂ) + u * I‖ ^ (-(5 / 2) : ℝ) = ((k : ℝ) ^ 2 + u ^ 2) ^ (-(5 / 4 : ℝ)) := by
    rw [hn1, ← Real.rpow_mul hq.le]; norm_num
  rw [hp, mul_comm]
  gcongr
  unfold Cn
  apply Real.exp_le_exp.mpr
  -- real part of the exponent
  have hre1 : ((π : ℂ) / (12 * k) * ((k : ℂ) + u * I)).re = π / 12 := by
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    rw [show (π : ℂ) / (12 * k) = ((π / (12 * k) : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
    simp
    field_simp
  have hre2 : (2 * π / k * ((n : ℂ) - 1 / 24) / ((k : ℂ) + u * I)).re =
      2 * π / k * ((n : ℝ) - 1 / 24) * k / ((k : ℝ) ^ 2 + u ^ 2) := by
    rw [show (2 * π / k * ((n : ℂ) - 1 / 24)) = ((2 * π / k * ((n : ℝ) - 1 / 24) : ℝ) : ℂ) by push_cast; ring,
      div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero, Complex.normSq_eq_norm_sq, normSq_wk]
    simp
  rw [add_re, hre1, hre2]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 2 * π / k * ((n : ℝ) - 1 / 24) * k / ((k : ℝ) ^ 2 + u ^ 2) ≤ 2 * π * n := by
    rw [div_le_iff₀ hq]
    have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
    have : 2 * π / k * ((n : ℝ) - 1 / 24) * k = 2 * π * ((n : ℝ) - 1 / 24) := by field_simp
    rw [this]
    have h1 : 1 ≤ (k : ℝ) ^ 2 + u ^ 2 := le_trans hkr hk2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π * n)
    nlinarith [Real.pi_pos]
  linarith

/-- `∫ (k²+u²)⁻¹ du = π/k`. -/
lemma integral_inv_sq_add {k : ℝ} (hk : 0 < k) : ∫ u : ℝ, ((k ^ 2 + u ^ 2)⁻¹ : ℝ) = π / k := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => (k ^ 2 + u ^ 2)⁻¹) k
  have e : ∀ x : ℝ, (k ^ 2 + (k * x) ^ 2)⁻¹ = (k ^ 2)⁻¹ * (1 + x ^ 2)⁻¹ := fun x => by
    rw [← mul_inv]; ring_nf
  simp only [e, integral_const_mul, integral_univ_inv_one_add_sq] at h
  rw [abs_of_pos (inv_pos.mpr hk), smul_eq_mul] at h
  field_simp at h ⊢
  linarith

lemma integrable_inv_sq_add {k : ℝ} (hk : 0 < k) : Integrable fun u : ℝ => ((k ^ 2 + u ^ 2)⁻¹ : ℝ) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hk.ne')).const_mul ((k ^ 2)⁻¹)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [← mul_inv]
  congr 1
  field_simp

lemma rpow_split {x : ℝ} (hx : 0 < x) : x ^ (-(5 / 4 : ℝ)) = x ^ (-(1 / 4 : ℝ)) * x⁻¹ := by
  rw [show (-(5 / 4 : ℝ)) = -(1 / 4) + (-1) by norm_num, Real.rpow_add hx, Real.rpow_neg_one]

lemma Wf_cont {k n : ℕ} (hk : 0 < k) : Continuous fun u : ℝ => Wf k n ((k : ℂ) + u * I) := by
  unfold Wf
  have hs : ∀ u : ℝ, (k : ℂ) + u * I ∈ slitPlane := fun u =>
    mem_slitPlane_iff.mpr (Or.inl (by simpa using (show (0 : ℝ) < k by exact_mod_cast hk)))
  refine Continuous.mul ?_ ?_
  · exact continuous_iff_continuousAt.mpr fun u =>
      ContinuousAt.cpow (by fun_prop) continuousAt_const (hs u)
  · refine Continuous.cexp (Continuous.add (by fun_prop) ?_)
    exact continuous_const.div (by fun_prop) fun u => wk_ne hk u

lemma norm_Wf_le' {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (u : ℝ) :
    ‖Wf k n ((k : ℂ) + u * I)‖ ≤ Cn n * ((k : ℝ) ^ 2 + u ^ 2)⁻¹ := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 1 ≤ (k : ℝ) ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  refine (norm_Wf_le hk hn u).trans ?_
  have hC : 0 ≤ Cn n := (Real.exp_pos _).le
  gcongr
  rw [rpow_split (by linarith)]
  have : ((k : ℝ) ^ 2 + u ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num)
  have h0 : 0 ≤ ((k : ℝ) ^ 2 + u ^ 2)⁻¹ := by positivity
  nlinarith

lemma integrable_Wf {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) : Integrable fun u : ℝ => Wf k n ((k : ℂ) + u * I) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  refine ((integrable_inv_sq_add hkr).const_mul (Cn n)).mono' (Wf_cont hk).aestronglyMeasurable
    (Eventually.of_forall fun u => norm_Wf_le' hk hn u)

lemma quarter_bound {x : ℝ} {N : ℕ} (hN : 1 ≤ N) (hx : (N : ℝ) ^ 2 / 2 ≤ x) : x ^ (-(1 / 4 : ℝ)) ≤ 2 / √N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN0
  rw [Real.rpow_neg hx0.le, inv_le_comm₀ (by positivity) (by positivity), inv_div]
  -- `√N/2 ≤ x^{1/4}` since `(√N/2)^4 = N²/16 ≤ x`
  have h4 : (√(N : ℝ) / 2) ^ (4 : ℕ) ≤ (x ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)), ← Real.rpow_mul hx0.le]
    norm_num
    rw [div_pow, show (√(N : ℝ)) ^ 4 = (N : ℝ) ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hN0.le]]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h4

/-- **the tails**. -/
lemma tail_bound {k n kp kn N : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (hN : 1 ≤ N) (hkp : N < k + kp) (hkn : N < k + kn) :
    ‖(∫ u in (-(kp : ℝ))..(kn : ℝ), Wf k n ((k : ℂ) + u * I)) - ∫ u : ℝ, Wf k n ((k : ℂ) + u * I)‖ ≤
      Cn n * (4 * π / (k * √N)) := by
  set g : ℝ → ℂ := fun u => Wf k n ((k : ℂ) + u * I) with hg
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hgi := integrable_Wf hk hn
  have hsplit1 := intervalIntegral.integral_Iic_sub_Iic (f := g) (a := -(kp : ℝ)) (b := kn)
    hgi.integrableOn hgi.integrableOn
  have hsplit2 := intervalIntegral.integral_Iic_add_Ioi (f := g) (b := (kn : ℝ)) hgi.integrableOn hgi.integrableOn
  have e : (∫ u in (-(kp : ℝ))..(kn : ℝ), g u) - ∫ u, g u = -((∫ u in Iic (-(kp : ℝ)), g u) + ∫ u in Ioi (kn : ℝ), g u) := by
    rw [← hsplit1, ← hsplit2]; ring
  rw [e, norm_neg]
  have hC : 0 ≤ Cn n := (Real.exp_pos _).le
  -- a tail bound
  have tailI : ∀ (s : Set ℝ) (K : ℕ), MeasurableSet s → (∀ u ∈ s, (K : ℝ) ^ 2 ≤ u ^ 2) → N < k + K →
      ‖∫ u in s, g u‖ ≤ Cn n * (2 / √N * (π / k)) := by
    intro s K hs hsK hK
    have hKN : (N : ℝ) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + K ^ 2 := by
      have : (N : ℝ) < k + K := by exact_mod_cast hK
      nlinarith [sq_nonneg ((k : ℝ) - K), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hq := quarter_bound hN hKN
    have hpt : ∀ u ∈ s, ‖g u‖ ≤ Cn n * (2 / √N) * ((k : ℝ) ^ 2 + u ^ 2)⁻¹ := by
      intro u hu
      have hpos : 0 < (k : ℝ) ^ 2 + u ^ 2 := by positivity
      refine (norm_Wf_le hk hn u).trans ?_
      rw [rpow_split hpos, ← mul_assoc]
      gcongr
      exact (Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by nlinarith [hsK u hu]) (by norm_num)).trans hq
    have hint := (integrable_inv_sq_add hkr).const_mul (Cn n * (2 / √N))
    calc ‖∫ u in s, g u‖ ≤ ∫ u in s, ‖g u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in s, Cn n * (2 / √N) * ((k : ℝ) ^ 2 + u ^ 2)⁻¹ :=
          setIntegral_mono_on hgi.norm.integrableOn hint.integrableOn hs hpt
      _ ≤ ∫ u, Cn n * (2 / √N) * ((k : ℝ) ^ 2 + u ^ 2)⁻¹ :=
          setIntegral_le_integral hint (Eventually.of_forall fun u => by positivity)
      _ = Cn n * (2 / √N * (π / k)) := by rw [integral_const_mul, integral_inv_sq_add hkr]; ring
  have t1 := tailI (Iic (-(kp : ℝ))) kp measurableSet_Iic (fun u hu => by
    rw [Set.mem_Iic] at hu; nlinarith [(Nat.cast_nonneg kp : (0 : ℝ) ≤ kp)]) hkp
  have t2 := tailI (Ioi (kn : ℝ)) kn measurableSet_Ioi (fun u hu => by
    rw [Set.mem_Ioi] at hu; nlinarith [(Nat.cast_nonneg kn : (0 : ℝ) ≤ kn)]) hkn
  calc ‖(∫ u in Iic (-(kp : ℝ)), g u) + ∫ u in Ioi (kn : ℝ), g u‖ ≤ ‖∫ u in Iic (-(kp : ℝ)), g u‖ +
        ‖∫ u in Ioi (kn : ℝ), g u‖ := norm_add_le _ _
    _ ≤ Cn n * (2 / √N * (π / k)) + Cn n * (2 / √N * (π / k)) := add_le_add t1 t2
    _ = _ := by ring

end

end Rademacher
