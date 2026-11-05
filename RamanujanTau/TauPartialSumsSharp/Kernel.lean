/-
# Degree-two dual kernels for a weight-`k` cusp form

For the functional equation `Λ(s) = (2π)^{−s}Γ(s)L(f,s)`, `Λ(k−s) = i^k Λ(s)`, and the Riesz
factor `P_j(s) = j!/(s(s+1)⋯(s+j))`, the kernel factor is

    Q_j(s) = j! (2π)^{2s} Γ(k−s) / Γ(s+j+1)

(`P_j(s)·L(f,s) = i^{−k}(2π)^{−k} Q_j(s) L(f,k−s)`). It is holomorphic on `Re s < k` and
off the real axis, and

* `Q_succ_mul`: `Q_{j+1}(s)(s+j+1) = (j+1) Q_j(s)`;
* `Q_bound`: on `A ≤ Re s ≤ B` (`−j ≤ A`, `B ≤ k−1`),
  `‖Q_j(s)‖ ≤ K (1+|t|)^{k−1−2Re s−j}` (one uniform `Γ`-ratio bound, `GammaUnif`).

The dual kernels are `J_j^{(σ)}(y) = (1/2π) ∫ y^{σ+it+j} Q_j(σ+it) dt`, absolutely convergent
when `k − 1 − 2σ − j < −1`. Proved here: the phase-free bound `‖J_j^{(σ)}(y)‖ ≤ K y^{σ+j}`,
the contour shift `J_j^{(σ₁)} = J_j^{(σ₂)}`, the relation
`J_{j+1}(u+v) − J_{j+1}(u) = (j+1) ∫₀^v J_j(u+w) dw`, and continuity in `y`.
-/
import RamanujanTau.RankinLandau.GammaUnif
import RamanujanTau.Stirling.RieszReal

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinLandau

/-- `Q_j(s) = j! (2π)^{2s} Γ(k−s) Γ(s+j+1)⁻¹`. -/
noncomputable def Q (k j : ℕ) (s : ℂ) : ℂ :=
  (j.factorial : ℂ) * ((2 * π : ℝ) : ℂ) ^ (2 * s) * Complex.Gamma ((k : ℂ) - s) *
    (Complex.Gamma (s + j + 1))⁻¹

/-- The dual kernel on the line `Re s = σ`. -/
noncomputable def Jc (k j : ℕ) (σ y : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I + j) * Q k j (σ + t * I)

lemma two_pi_pos' : (0 : ℝ) < 2 * π := by positivity

lemma Q_succ_mul (k j : ℕ) (s : ℂ) :
    Q k (j + 1) s * (s + j + 1) = ((j : ℂ) + 1) * Q k j s := by
  unfold Q
  have e := inv_Gamma_eq_mul (s + j + 1)
  rw [show s + ((j + 1 : ℕ) : ℂ) + 1 = s + j + 1 + 1 by push_cast; ring]
  rw [e, Nat.factorial_succ]
  push_cast
  ring

lemma differentiableAt_Q (k j : ℕ) {s : ℂ} (hs : s.re < k ∨ s.im ≠ 0) :
    DifferentiableAt ℂ (Q k j) s := by
  have h2pi : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos'.ne'
  have g1 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma ((k : ℂ) - s)) s := by
    refine (Complex.differentiableAt_Gamma ((k : ℂ) - s) (fun n h => ?_)).comp s
      ((differentiableAt_const _).sub differentiableAt_id)
    rcases hs with hs | hs
    · have := congrArg Complex.re h; simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · have := congrArg Complex.im h; simp at this; exact hs (by linarith)
  have g2 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma (s + j + 1))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + j + 1)).comp s
      ((differentiableAt_id.add_const (j : ℂ)).add_const 1)
    simpa [Function.comp_def] using this
  unfold Q
  exact (((differentiableAt_const _).mul
    ((differentiableAt_id.const_mul (2 : ℂ)).const_cpow (Or.inl h2pi))).mul g1).mul g2

lemma norm_two_pi_cpow (s : ℂ) : ‖((2 * π : ℝ) : ℂ) ^ (2 * s)‖ = (2 * π) ^ (2 * s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pi_pos']; simp

/-- **The strip bound** with the exact exponent `k − 1 − 2 Re s − j`. -/
theorem Q_bound (k j : ℕ) {A B : ℝ} (hA : -(j : ℝ) ≤ A) (hB : B ≤ (k : ℝ) - 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
      ‖Q k j s‖ ≤ K * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re - j) := by
  set R : ℝ := (k : ℝ) + j + |A| + |B| + 2 with hR
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hR1 : 1 ≤ R := by
    rw [hR]; have := abs_nonneg A; have := abs_nonneg B
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_unif' hR1
  have h2pi1 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  refine ⟨(j.factorial : ℝ) * C * (2 * π) ^ (2 * |B|), by positivity, fun s h1 h2 => ?_⟩
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hw : 0 < (s + j + 1).re := by simp; linarith
  have hpos : 0 < ‖Complex.Gamma (s + j + 1)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos hw)
  have hz := hC ((k : ℂ) - s) (s + j + 1) (by simp; linarith) (by simp; rw [hR]; linarith)
    (by simp; linarith) (by simp; rw [hR]; linarith) (by simp)
  have him : (s + j + 1).im = s.im := by simp
  have hre : ((k : ℂ) - s).re - (s + j + 1).re = (k : ℝ) - 1 - 2 * s.re - j := by simp; ring
  rw [him, hre] at hz
  have h2 : (2 * π) ^ (2 * s.re) ≤ (2 * π) ^ (2 * |B|) :=
    Real.rpow_le_rpow_of_exponent_le h2pi1 (by linarith)
  unfold Q
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_two_pi_cpow]
  rw [← div_eq_mul_inv]
  have hz' : ‖Complex.Gamma ((k : ℂ) - s)‖ / ‖Complex.Gamma (s + j + 1)‖ ≤
      C * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re - j) := by
    rw [div_le_iff₀ hpos]; exact hz
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  calc (j.factorial : ℝ) * (2 * π) ^ (2 * s.re) * ‖Complex.Gamma ((k : ℂ) - s)‖ /
        ‖Complex.Gamma (s + j + 1)‖
      = (j.factorial : ℝ) * (2 * π) ^ (2 * s.re) *
          (‖Complex.Gamma ((k : ℂ) - s)‖ / ‖Complex.Gamma (s + j + 1)‖) := by ring
    _ ≤ (j.factorial : ℝ) * (2 * π) ^ (2 * |B|) *
          (C * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re - j)) := by gcongr
    _ = _ := by ring

/-! ### The kernels on vertical lines -/

variable (k j : ℕ)

/-- The integrand of `J_j^{(σ)}(y)`. -/
noncomputable def jint (σ y t : ℝ) : ℂ := (y : ℂ) ^ ((σ : ℂ) + t * I + j) * Q k j (σ + t * I)

lemma Jc_eq (σ y : ℝ) : Jc k j σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, jint k j σ y t := rfl

lemma continuous_Q_line {σ : ℝ} (hσ : σ < k) :
    Continuous fun t : ℝ => Q k j ((σ : ℂ) + t * I) := by
  have : Continuous fun t : ℝ => ((σ : ℂ) + t * I) := by fun_prop
  refine continuous_iff_continuousAt.2 fun t => ?_
  exact ((differentiableAt_Q k j (Or.inl (by simpa using hσ))).continuousAt).comp
    this.continuousAt

lemma continuous_jint {σ y : ℝ} (hσ : σ < k) (hy : 0 < y) : Continuous (jint k j σ y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (Continuous.const_cpow (by fun_prop) (Or.inl hy0)).mul (continuous_Q_line k j hσ)

lemma norm_cpow_line {y : ℝ} (hy : 0 < y) (σ t : ℝ) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I + j)‖ = y ^ (σ + j) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp

lemma jint_bound {σ : ℝ} (hA : -(j : ℝ) ≤ σ) (hB : σ ≤ (k : ℝ) - 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, 0 < y → ∀ t : ℝ,
      ‖jint k j σ y t‖ ≤ y ^ (σ + j) * (K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j)) := by
  obtain ⟨K, hK0, hK⟩ := Q_bound k j hA hB
  refine ⟨K, hK0, fun y hy t => ?_⟩
  unfold jint
  rw [norm_mul, norm_cpow_line j hy]
  have := hK (σ + t * I) (by simp) (by simpa using hB)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, add_re, mul_re, sub_zero] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma integrable_rpow_line {p : ℝ} (hp : 1 < p) (K : ℝ) :
    Integrable fun t : ℝ => K * (1 + |t|) ^ (-p) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp)).const_mul K
  simpa [Real.norm_eq_abs] using this

lemma integrable_jint {σ : ℝ} (hA : -(j : ℝ) ≤ σ) (hB : σ ≤ (k : ℝ) - 1)
    (hσj : (k : ℝ) - 1 - 2 * σ - j < -1) {y : ℝ} (hy : 0 < y) : Integrable (jint k j σ y) := by
  obtain ⟨K, -, hK⟩ := jint_bound k j hA hB
  have hI := (integrable_rpow_line (p := -((k : ℝ) - 1 - 2 * σ - j)) (by linarith) K).const_mul
    (y ^ (σ + j))
  refine hI.mono' (continuous_jint k j (by linarith) hy).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [neg_neg]; exact hK y hy t

/-- **The phase-free kernel bound** `‖J_j^{(σ)}(y)‖ ≤ K y^{σ+j}`. -/
theorem norm_Jc_le {σ : ℝ} (hA : -(j : ℝ) ≤ σ) (hB : σ ≤ (k : ℝ) - 1)
    (hσj : (k : ℝ) - 1 - 2 * σ - j < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, 0 < y → ‖Jc k j σ y‖ ≤ K * y ^ (σ + j) := by
  obtain ⟨K, hK0, hK⟩ := jint_bound k j hA hB
  set I₀ : ℝ := ∫ t : ℝ, K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j) with hI₀
  have hI : Integrable fun t : ℝ => K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j) := by
    have := integrable_rpow_line (p := -((k : ℝ) - 1 - 2 * σ - j)) (by linarith) K
    simpa using this
  have hI0 : 0 ≤ I₀ := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * π) * I₀, by positivity, fun y hy => ?_⟩
  rw [Jc_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  have : ‖∫ t : ℝ, jint k j σ y t‖ ≤ y ^ (σ + j) * I₀ := by
    calc ‖∫ t : ℝ, jint k j σ y t‖ ≤
        ∫ t : ℝ, y ^ (σ + j) * (K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j)) :=
          norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall (hK y hy))
      _ = y ^ (σ + j) * I₀ := by rw [integral_const_mul]
  calc 1 / (2 * π) * ‖∫ t : ℝ, jint k j σ y t‖ ≤ 1 / (2 * π) * (y ^ (σ + j) * I₀) := by gcongr
    _ = 1 / (2 * π) * I₀ * y ^ (σ + j) := by ring

/-- **Contour shift for the kernel.** -/
theorem Jc_shift {A σ₁ σ₂ B : ℝ} (hA : -(j : ℝ) ≤ A) (hB : B ≤ (k : ℝ) - 1)
    (hAj : (k : ℝ) - 1 - 2 * A - j < -1) (h1 : A ≤ σ₁) (h2 : A ≤ σ₂) (h1' : σ₁ ≤ B)
    (h2' : σ₂ ≤ B) {y : ℝ} (hy : 0 < y) :
    Jc k j σ₁ y = Jc k j σ₂ y := by
  obtain ⟨K, hK0, hK⟩ := Q_bound k j hA hB
  set g : ℂ → ℂ := fun s => (y : ℂ) ^ (s + j) * Q k j s with hg
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have key : ∀ a b : ℝ, A ≤ a → a ≤ b → b ≤ B →
      ∫ t : ℝ, g (b + t * I) = ∫ t : ℝ, g (a + t * I) := by
    intro a b ha hab hb
    have hdiff : DifferentiableOn ℂ g {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
      intro s hs
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
      · exact (differentiableAt_id.add_const _).const_cpow (Or.inl hy0)
      · exact differentiableAt_Q k j (Or.inl (by linarith [hs.2]))
    refine Stirling.integral_line_eq_rpow (p := -((k : ℝ) - 1 - 2 * A - j)) (by linarith) hab
      hdiff (C := (y ^ (a + j) + y ^ (b + j)) * K) (fun s hs1 hs2 => ?_)
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
    have hexp : (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * s.re - j) ≤
        (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * A - j) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) (by linarith)
    calc y ^ (s.re + j) * ‖Q k j s‖ ≤ (y ^ (a + j) + y ^ (b + j)) *
          (K * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * A - j)) := by
          gcongr
          exact hQ.trans (by gcongr)
      _ = (y ^ (a + j) + y ^ (b + j)) * K * (1 + |s.im|) ^ ((k : ℝ) - 1 - 2 * A - j) := by ring
  have e : ∀ σ : ℝ, Jc k j σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, g (σ + t * I) := by
    intro σ; rfl
  rw [e, e]
  rcases le_total σ₁ σ₂ with h | h
  · rw [key σ₁ σ₂ h1 h h2']
  · rw [key σ₂ σ₁ h2 h h1']

/-! ### The relation `J_{j+1}' = (j+1) J_j` -/

lemma integral_cpow_shift {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) {r : ℂ} (hr : -1 < r.re) :
    ∫ w in (0 : ℝ)..v, ((u + w : ℝ) : ℂ) ^ r =
      (((u + v : ℝ) : ℂ) ^ (r + 1) - ((u : ℝ) : ℂ) ^ (r + 1)) / (r + 1) := by
  have := intervalIntegral.integral_comp_add_left (fun x : ℝ => (x : ℂ) ^ r) u (a := 0) (b := v)
  simp only [add_zero] at this
  rw [this, integral_cpow (Or.inl hr)]

/-- **The kernel relation** on a line `Re s = σ` where `J_j` converges absolutely. -/
theorem Jc_rel {σ : ℝ} (hσ0 : 0 < σ) (hB : σ ≤ (k : ℝ) - 1)
    (hσj : (k : ℝ) - 1 - 2 * σ - j < -1) {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    Jc k (j + 1) σ (u + v) - Jc k (j + 1) σ u =
      ((j : ℂ) + 1) * ∫ w in (0 : ℝ)..v, Jc k j σ (u + w) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA : -(j : ℝ) ≤ σ := by linarith
  have hA' : -((j + 1 : ℕ) : ℝ) ≤ σ := by push_cast; linarith
  have hσj' : (k : ℝ) - 1 - 2 * σ - ((j + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hσk : σ < k := by linarith
  obtain ⟨K, hK0, hK⟩ := jint_bound k j hA hB
  set F : ℝ → ℝ → ℂ := fun w t => jint k j σ (u + max (min w v) 0) t with hF
  have hF' : ∀ w ∈ Ioc (0 : ℝ) v, ∀ t, F w t = jint k j σ (u + w) t := by
    intro w hw t; simp only [hF, min_eq_left hw.2, max_eq_left hw.1.le]
  have hFc : Continuous (Function.uncurry F) := by
    have hpos : ∀ p : ℝ × ℝ, 0 < u + max (min p.1 v) 0 := fun p => by positivity
    simp only [hF, jint, Function.uncurry_def]
    refine Continuous.mul ?_ ?_
    · refine Continuous.cpow (by fun_prop) (by fun_prop) (fun p => ?_)
      exact Or.inl (by simpa using hpos p)
    · exact (continuous_Q_line k j hσk).comp continuous_snd
  have hbound : ∀ w t, ‖F w t‖ ≤
      (u + v) ^ (σ + j) * (K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j)) := by
    intro w t
    have h0 : 0 ≤ max (min w v) 0 := le_max_right _ _
    have h1 : max (min w v) 0 ≤ v := max_le (min_le_right _ _) hv
    refine (hK (u + max (min w v) 0) (by linarith) t).trans ?_
    gcongr
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc (0 : ℝ) v)).prod volume) := by
    have hI := (integrable_rpow_line (p := -((k : ℝ) - 1 - 2 * σ - j)) (by linarith) K)
    have hg : Integrable (fun p : ℝ × ℝ => (u + v) ^ (σ + j) *
        (K * (1 + |p.2|) ^ (-(-((k : ℝ) - 1 - 2 * σ - j)))))
        ((volume.restrict (Ioc (0 : ℝ) v)).prod volume) :=
      (integrable_const ((u + v) ^ (σ + j))).mul_prod hI
    refine hg.mono' hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [neg_neg]
    exact hbound p.1 p.2
  have hswap := integral_integral_swap hint
  have hinner : ∀ t : ℝ, ∫ w in Ioc (0 : ℝ) v, F w t =
      Q k j ((σ : ℂ) + t * I) *
        ((((u + v : ℝ) : ℂ) ^ (((σ : ℂ) + t * I + j) + 1) -
          ((u : ℝ) : ℂ) ^ (((σ : ℂ) + t * I + j) + 1)) /
          (((σ : ℂ) + t * I + j) + 1)) := by
    intro t
    rw [setIntegral_congr_fun measurableSet_Ioc (fun w hw => hF' w hw t),
      ← intervalIntegral.integral_of_le hv]
    simp only [jint]
    rw [intervalIntegral.integral_mul_const, integral_cpow_shift hu hv (by simp; linarith)]
    ring
  have hJ : ∀ w ∈ Ioc (0 : ℝ) v, Jc k j σ (u + w) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, F w t := by
    intro w hw; rw [Jc_eq]; congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => (hF' w hw t).symm)
  rw [intervalIntegral.integral_of_le hv,
    setIntegral_congr_fun measurableSet_Ioc hJ, integral_const_mul, hswap]
  simp only [hinner]
  rw [Jc_eq, Jc_eq, ← mul_sub, ← integral_sub
    (integrable_jint k (j + 1) hA' hB hσj' (by linarith))
    (integrable_jint k (j + 1) hA' hB hσj' hu), mul_left_comm,
    ← integral_const_mul ((j : ℂ) + 1)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [jint]
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsj : s + j + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hQ := Q_succ_mul k j s
  have hQ' : Q k (j + 1) s = ((j : ℂ) + 1) * Q k j s / (s + j + 1) := by
    rw [eq_div_iff hsj, hQ]
  rw [hQ', show (s : ℂ) + ((j + 1 : ℕ) : ℂ) = s + j + 1 by push_cast; ring]
  field_simp

/-- Continuity of `y ↦ J_j^{(σ)}(y)` on `(0, ∞)`. -/
theorem continuousOn_Jc {σ : ℝ} (hA : -(j : ℝ) ≤ σ) (hB : σ ≤ (k : ℝ) - 1)
    (hσj : (k : ℝ) - 1 - 2 * σ - j < -1) :
    ContinuousOn (fun y => Jc k j σ y) (Ioi 0) := by
  obtain ⟨K, hK0, hK⟩ := jint_bound k j hA hB
  intro y₀ hy₀
  simp only [Set.mem_Ioi] at hy₀
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun y => ∫ t : ℝ, jint k j σ y t) y₀ := by
    have hnhds : Ioo (y₀ / 2) (2 * y₀) ∈ 𝓝 y₀ := Ioo_mem_nhds (by linarith) (by linarith)
    refine continuousAt_of_dominated (bound := fun t => ((y₀ / 2) ^ (σ + j) + (2 * y₀) ^ (σ + j)) *
      (K * (1 + |t|) ^ ((k : ℝ) - 1 - 2 * σ - j))) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy
      exact (continuous_jint k j (by linarith) (by linarith [hy.1])).aestronglyMeasurable
    · filter_upwards [hnhds] with y hy
      refine Eventually.of_forall fun t => (hK y (by linarith [hy.1]) t).trans ?_
      have hy0 : 0 < y := by linarith [hy.1]
      have hyp : y ^ (σ + j) ≤ (y₀ / 2) ^ (σ + j) + (2 * y₀) ^ (σ + j) := by
        have : y ^ (σ + j) ≤ (2 * y₀) ^ (σ + j) :=
          Real.rpow_le_rpow hy0.le hy.2.le (by linarith)
        linarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ y₀ / 2) (σ + j)]
      gcongr
    · have := (integrable_rpow_line (p := -((k : ℝ) - 1 - 2 * σ - j)) (by linarith) K).const_mul
        ((y₀ / 2) ^ (σ + j) + (2 * y₀) ^ (σ + j))
      simpa using this
    · refine Eventually.of_forall fun t => ?_
      simp only [jint]
      refine ContinuousAt.mul ?_ continuousAt_const
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const
        (Or.inl (by simpa using hy₀))
  exact continuousAt_const.mul hc

end RamanujanTau.TauPartialSumsSharp
