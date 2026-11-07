/-
# The dual kernels on vertical lines: integrability, contour shift, bounds, relations

For `σ ≤ 1/2` with `1 − 4σ − j < −1` (i.e. `σ > (2 − j)/4`) the integral defining
`J_j^{(σ)}(y)` converges absolutely (`Qk_bound`), and:

* `Jc_shift`: `J_j^{(σ₁)} = J_j^{(σ₂)}` for `A₀ ≤ σ₁, σ₂ ≤ 1/2`, `1 − 4A₀ − j < −1`
  (Cauchy on the strip, `Stirling.integral_line_eq_rpow`);
* `norm_Jc_le`: `‖J_j^{(σ)}(y)‖ ≤ K y^{σ+j}` — the **phase-free** kernel bound;
* `Jc_rel`: on `Re s = 1/2`, `J_{j+1}(u+v) − J_{j+1}(u) = (j+1) ∫₀^v J_j(u+w) dw` (`j ≥ 1`),
  by Fubini and `Q_{j+1}(s)(s+j+1) = (j+1) Q_j(s)`;
* `continuousOn_Jc`: `y ↦ J_j^{(1/2)}(y)` is continuous on `(0, ∞)` (`j ≥ 1`).
-/
import RamanujanTau.RankinLandau.Kernel
import RamanujanTau.Stirling.RieszReal

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinErrorGeneral

variable (m j : ℕ)

/-- The integrand of `J_j^{(σ)}(y)`. -/
noncomputable def jint (σ y t : ℝ) : ℂ := (y : ℂ) ^ ((σ : ℂ) + t * I + j) * Qk m j (σ + t * I)

lemma Jc_eq (σ y : ℝ) : Jc m j σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, jint m j σ y t := rfl

lemma continuous_jint {σ y : ℝ} (hσ : σ < 1) (hy : 0 < y) : Continuous (jint m j σ y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  refine (Continuous.const_cpow (by fun_prop) (Or.inl hy0)).mul ?_
  exact (differentiableOn_Qk m j).continuousOn.comp_continuous (by fun_prop)
    (fun t => by simp [hσ])

lemma norm_cpow_line {y : ℝ} (hy : 0 < y) (σ t : ℝ) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I + j)‖ = y ^ (σ + j) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp

lemma jint_bound (hm : 1 ≤ m) {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, 0 < y → ∀ t : ℝ,
      ‖jint m j σ y t‖ ≤ y ^ (σ + j) * (K * (1 + |t|) ^ (1 - 4 * σ - j)) := by
  obtain ⟨K, hK0, hK⟩ := Qk_bound m j hm hσ
  refine ⟨K, hK0, fun y hy t => ?_⟩
  unfold jint
  rw [norm_mul, norm_cpow_line j hy]
  have := hK (σ + t * I) (by simp) (by simpa using hσ)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma integrable_rpow_line {p : ℝ} (hp : 1 < p) (K : ℝ) :
    Integrable fun t : ℝ => K * (1 + |t|) ^ (-p) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp)).const_mul K
  simpa [Real.norm_eq_abs] using this

lemma integrable_jint (hm : 1 ≤ m) {σ : ℝ} (hσ : σ ≤ 1 / 2) (hσj : 1 - 4 * σ - j < -1)
    {y : ℝ} (hy : 0 < y) : Integrable (jint m j σ y) := by
  obtain ⟨K, -, hK⟩ := jint_bound m j hm hσ
  have hI := (integrable_rpow_line (p := -(1 - 4 * σ - j)) (by linarith) K).const_mul
    (y ^ (σ + j))
  refine hI.mono' (continuous_jint m j (by linarith) hy).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [neg_neg]; exact hK y hy t

/-- **The phase-free kernel bound** `‖J_j^{(σ)}(y)‖ ≤ K y^{σ+j}`. -/
theorem norm_Jc_le (hm : 1 ≤ m) {σ : ℝ} (hσ : σ ≤ 1 / 2) (hσj : 1 - 4 * σ - j < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, 0 < y → ‖Jc m j σ y‖ ≤ K * y ^ (σ + j) := by
  obtain ⟨K, hK0, hK⟩ := jint_bound m j hm hσ
  set I₀ : ℝ := ∫ t : ℝ, K * (1 + |t|) ^ (1 - 4 * σ - j) with hI₀
  have hI : Integrable fun t : ℝ => K * (1 + |t|) ^ (1 - 4 * σ - j) := by
    have := integrable_rpow_line (p := -(1 - 4 * σ - j)) (by linarith) K
    simpa using this
  have hI0 : 0 ≤ I₀ := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * π) * I₀, by positivity, fun y hy => ?_⟩
  rw [Jc_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  have : ‖∫ t : ℝ, jint m j σ y t‖ ≤ y ^ (σ + j) * I₀ := by
    calc ‖∫ t : ℝ, jint m j σ y t‖ ≤ ∫ t : ℝ, y ^ (σ + j) * (K * (1 + |t|) ^ (1 - 4 * σ - j)) :=
          norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall (hK y hy))
      _ = y ^ (σ + j) * I₀ := by rw [integral_const_mul]
  calc 1 / (2 * π) * ‖∫ t : ℝ, jint m j σ y t‖ ≤ 1 / (2 * π) * (y ^ (σ + j) * I₀) := by gcongr
    _ = 1 / (2 * π) * I₀ * y ^ (σ + j) := by ring

/-- **Contour shift for the kernel.** -/
theorem Jc_shift (hm : 1 ≤ m) {A₀ σ₁ σ₂ : ℝ} (hA : 1 - 4 * A₀ - j < -1) (h1 : A₀ ≤ σ₁)
    (h2 : A₀ ≤ σ₂) (h1' : σ₁ ≤ 1 / 2) (h2' : σ₂ ≤ 1 / 2) {y : ℝ} (hy : 0 < y) :
    Jc m j σ₁ y = Jc m j σ₂ y := by
  have hA0 : A₀ ≤ 1 / 2 := le_trans h1 h1'
  obtain ⟨K, hK0, hK⟩ := Qk_bound m j hm hA0
  set g : ℂ → ℂ := fun s => (y : ℂ) ^ (s + j) * Qk m j s with hg
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have key : ∀ a b : ℝ, A₀ ≤ a → a ≤ b → b ≤ 1 / 2 →
      ∫ t : ℝ, g (b + t * I) = ∫ t : ℝ, g (a + t * I) := by
    intro a b ha hab hb
    have hdiff : DifferentiableOn ℂ g {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
      intro s hs
      refine DifferentiableWithinAt.mul ?_ ?_
      · exact ((differentiableAt_id.add_const _).const_cpow (Or.inl hy0)).differentiableWithinAt
      · exact ((differentiableOn_Qk m j) s (by simp only [mem_setOf_eq]; linarith [hs.2])).mono
          (fun z hz => by simp only [mem_setOf_eq] at hz ⊢; linarith [hz.2])
    refine Stirling.integral_line_eq_rpow (p := -(1 - 4 * A₀ - j)) (by linarith) hab hdiff
      (C := (y ^ (a + j) + y ^ (b + j)) * K) (fun s hs1 hs2 => ?_)
    rw [hg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, neg_neg]
    have hQ := hK s (by linarith) (by linarith)
    have hre : (s + j).re = s.re + j := by simp
    rw [hre]
    have hyp : y ^ (s.re + j) ≤ y ^ (a + j) + y ^ (b + j) := by
      rcases le_or_gt 1 y with hy1 | hy1
      · have := Real.rpow_le_rpow_of_exponent_le hy1 (show s.re + j ≤ b + j by linarith)
        linarith [Real.rpow_nonneg hy.le (a + j)]
      · have := Real.rpow_le_rpow_of_exponent_ge hy hy1.le (show a + j ≤ s.re + j by linarith)
        linarith [Real.rpow_nonneg hy.le (b + j)]
    calc y ^ (s.re + j) * ‖Qk m j s‖ ≤ (y ^ (a + j) + y ^ (b + j)) *
          (K * (1 + |s.im|) ^ (1 - 4 * A₀ - j)) := by
          gcongr
      _ = (y ^ (a + j) + y ^ (b + j)) * K * (1 + |s.im|) ^ (1 - 4 * A₀ - j) := by ring
  have e : ∀ σ : ℝ, Jc m j σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, g (σ + t * I) := by
    intro σ; rfl
  rw [e, e]
  rcases le_total σ₁ σ₂ with h | h
  · rw [key σ₁ σ₂ h1 h h2']
  · rw [key σ₂ σ₁ h2 h h1']

/-! ### The relation `J_{j+1}' = (j+1) J_j` on the line `Re s = 1/2` -/

lemma integral_cpow_shift {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) {r : ℂ} (hr : -1 < r.re) :
    ∫ w in (0 : ℝ)..v, ((u + w : ℝ) : ℂ) ^ r =
      (((u + v : ℝ) : ℂ) ^ (r + 1) - ((u : ℝ) : ℂ) ^ (r + 1)) / (r + 1) := by
  have := intervalIntegral.integral_comp_add_left (fun x : ℝ => (x : ℂ) ^ r) u (a := 0) (b := v)
  simp only [add_zero] at this
  rw [this, integral_cpow (Or.inl hr)]

/-- **The kernel relation** (complex form), `j ≥ 1`, on `Re s = 1/2`. -/
theorem Jc_rel (hm : 1 ≤ m) (hj : 1 ≤ j) {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    Jc m (j + 1) (1 / 2) (u + v) - Jc m (j + 1) (1 / 2) u =
      ((j : ℂ) + 1) * ∫ w in (0 : ℝ)..v, Jc m j (1 / 2) (u + w) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hσj : 1 - 4 * (1 / 2 : ℝ) - j < -1 := by linarith
  have hσj' : 1 - 4 * (1 / 2 : ℝ) - ((j + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  obtain ⟨K, hK0, hK⟩ := jint_bound m j hm (σ := 1 / 2) (by norm_num)
  -- a globally continuous version of the integrand
  set F : ℝ → ℝ → ℂ := fun w t => jint m j (1 / 2) (u + max (min w v) 0) t with hF
  have hF' : ∀ w ∈ Ioc (0 : ℝ) v, ∀ t, F w t = jint m j (1 / 2) (u + w) t := by
    intro w hw t; simp only [hF, min_eq_left hw.2, max_eq_left hw.1.le]
  have hFc : Continuous (Function.uncurry F) := by
    have hpos : ∀ p : ℝ × ℝ, 0 < u + max (min p.1 v) 0 := fun p => by positivity
    simp only [hF, jint, Function.uncurry_def]
    refine Continuous.mul ?_ ?_
    · refine Continuous.cpow (by fun_prop) (by fun_prop) (fun p => ?_)
      exact Or.inl (by simpa using hpos p)
    · exact (differentiableOn_Qk m j).continuousOn.comp_continuous (by fun_prop)
        (fun p => by simp; norm_num)
  -- Fubini
  have hbound : ∀ w t, ‖F w t‖ ≤
      (u + v) ^ ((1 / 2 : ℝ) + j) * (K * (1 + |t|) ^ (1 - 4 * (1 / 2 : ℝ) - j)) := by
    intro w t
    have h0 : 0 ≤ max (min w v) 0 := le_max_right _ _
    have h1 : max (min w v) 0 ≤ v := max_le (min_le_right _ _) hv
    refine (hK (u + max (min w v) 0) (by linarith) t).trans ?_
    gcongr
    all_goals linarith
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc (0 : ℝ) v)).prod volume) := by
    have hI := (integrable_rpow_line (p := -(1 - 4 * (1 / 2 : ℝ) - j)) (by linarith) K)
    have hg : Integrable (fun p : ℝ × ℝ => (u + v) ^ ((1 / 2 : ℝ) + j) *
        (K * (1 + |p.2|) ^ (-(-(1 - 4 * (1 / 2 : ℝ) - j)))))
        ((volume.restrict (Ioc (0 : ℝ) v)).prod volume) :=
      (integrable_const ((u + v) ^ ((1 / 2 : ℝ) + j))).mul_prod hI
    refine hg.mono' hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [neg_neg]
    exact hbound p.1 p.2
  have hswap := integral_integral_swap hint
  -- the inner `w`-integral
  have hinner : ∀ t : ℝ, ∫ w in Ioc (0 : ℝ) v, F w t =
      Qk m j (((1 / 2 : ℝ) : ℂ) + t * I) *
        ((((u + v : ℝ) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * I + j) + 1) -
          ((u : ℝ) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * I + j) + 1)) /
          ((((1 / 2 : ℝ) : ℂ) + t * I + j) + 1)) := by
    intro t
    rw [setIntegral_congr_fun measurableSet_Ioc (fun w hw => hF' w hw t),
      ← intervalIntegral.integral_of_le hv]
    simp only [jint]
    rw [intervalIntegral.integral_mul_const, integral_cpow_shift hu hv (by simp; linarith [hj1])]
    ring
  -- assemble
  have hJ : ∀ w ∈ Ioc (0 : ℝ) v, Jc m j (1 / 2) (u + w) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, F w t := by
    intro w hw; rw [Jc_eq]; congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => (hF' w hw t).symm)
  rw [intervalIntegral.integral_of_le hv,
    setIntegral_congr_fun measurableSet_Ioc hJ, integral_const_mul, hswap]
  simp only [hinner]
  rw [Jc_eq, Jc_eq, ← mul_sub, ← integral_sub
    (integrable_jint m (j + 1) hm (by norm_num) hσj' (by linarith))
    (integrable_jint m (j + 1) hm (by norm_num) hσj' hu), mul_left_comm,
    ← integral_const_mul ((j : ℂ) + 1)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [jint]
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hs
  have hsj : s + ((j + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hQ := Qk_succ_mul m j s
  have e1 : s + ((j + 1 : ℕ) : ℂ) = s + j + 1 := by push_cast; ring
  rw [e1] at hsj hQ
  have hQ' : Qk m (j + 1) s = ((j : ℂ) + 1) * Qk m j s / (s + j + 1) := by
    rw [eq_div_iff hsj, hQ]
  rw [hQ', show (s : ℂ) + ((j + 1 : ℕ) : ℂ) = s + j + 1 by push_cast; ring]
  field_simp

/-- Continuity of `y ↦ J_j^{(1/2)}(y)` on `(0, ∞)`, `j ≥ 1`. -/
theorem continuousOn_Jc (hm : 1 ≤ m) (hj : 1 ≤ j) :
    ContinuousOn (fun y => Jc m j (1 / 2) y) (Ioi 0) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨K, hK0, hK⟩ := jint_bound m j hm (σ := 1 / 2) (by norm_num)
  intro y₀ hy₀
  simp only [mem_Ioi] at hy₀
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun y => ∫ t : ℝ, jint m j (1 / 2) y t) y₀ := by
    have hnhds : Ioo (y₀ / 2) (2 * y₀) ∈ 𝓝 y₀ := Ioo_mem_nhds (by linarith) (by linarith)
    refine continuousAt_of_dominated (bound := fun t => (2 * y₀) ^ ((1 / 2 : ℝ) + j) *
      (K * (1 + |t|) ^ (1 - 4 * (1 / 2 : ℝ) - j))) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy
      exact (continuous_jint m j (by norm_num) (by linarith [hy.1])).aestronglyMeasurable
    · filter_upwards [hnhds] with y hy
      refine Eventually.of_forall fun t => (hK y (by linarith [hy.1]) t).trans ?_
      gcongr
      · linarith [hy.1]
      · linarith [hy.2]
    · have := (integrable_rpow_line (p := -(1 - 4 * (1 / 2 : ℝ) - j)) (by linarith) K).const_mul
        ((2 * y₀) ^ ((1 / 2 : ℝ) + j))
      simpa using this
    · refine Eventually.of_forall fun t => ?_
      simp only [jint]
      refine ContinuousAt.mul ?_ continuousAt_const
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const
        (Or.inl (by simpa using hy₀))
  exact continuousAt_const.mul hc

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.norm_Jc_le
#print axioms RamanujanTau.RankinLandau.Jc_shift
#print axioms RamanujanTau.RankinLandau.Jc_rel
#print axioms RamanujanTau.RankinLandau.continuousOn_Jc
