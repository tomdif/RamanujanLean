/-
# The argument principle for `Λ(f,s)` on `[k−σ₁, σ₁] × [−T, T]`, reduced to the right half

Only the functional equation `Λ(k−s) = i^k Λ(s)` is used: `φ = Λ'/Λ` satisfies `φ(k−s) = −φ(s)`
whatever the root number (`k ≡ 0` or `2 mod 4`); no conjugation symmetry (real coefficients) is
needed.  With `V = ∫_{−T}^{T} φ(σ₁+iy) dy` and `H(t) = ∫_{k/2}^{σ₁} φ(x+it) dx`
(`rectInt_phi_symm_gen`):

  `∮ φ = 2iV − 2H(T) + 2H(−T)`,

and, the zeros being symmetric under `ρ ↦ k − ρ` (`ord_reflect`), the count in the rectangle is
`2 N_f(T) + N_f⁰` with `N_f⁰` the (constant) number of real zeros (`pi_count_eq_gen`):

  `π (2 N_f(T) + N_f⁰) = Re V − Im H(T) + Im H(−T)`.
-/
import RamanujanTau.GeneralZeros.Count

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.ZeroCountRvM
open scoped ComplexConjugate Real Interval MatrixGroups

/-! ### An abstract entire function with `F(κ₂ − s) = c F(s)` -/

section Abstract

variable {F : ℂ → ℂ} {κ₂ : ℝ} {c : ℂ}

lemma deriv_reflect (hF : Differentiable ℂ F) (hfe : ∀ s, F ((κ₂ : ℂ) - s) = c * F s) (s : ℂ) :
    deriv F ((κ₂ : ℂ) - s) = -(c * deriv F s) := by
  have h1 : HasDerivAt (fun w => F ((κ₂ : ℂ) - w)) (deriv F ((κ₂ : ℂ) - s) * (-1)) s := by
    have := (hF ((κ₂ : ℂ) - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub (κ₂ : ℂ))
    simpa using this
  have h2 : (fun w => F ((κ₂ : ℂ) - w)) = fun w => c * F w := funext hfe
  rw [h2] at h1
  have h3 := ((hF s).hasDerivAt.const_mul c).unique h1
  linear_combination h3

lemma logDeriv_reflect (hF : Differentiable ℂ F) (hfe : ∀ s, F ((κ₂ : ℂ) - s) = c * F s)
    (hc : c ≠ 0) (s : ℂ) : logDeriv F ((κ₂ : ℂ) - s) = -logDeriv F s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_reflect hF hfe, hfe]
  by_cases h : F s = 0
  · simp [h]
  · field_simp

lemma continuousAt_logDeriv (hF : Differentiable ℂ F) {s : ℂ} (hs : F s ≠ 0) :
    ContinuousAt (logDeriv F) s := by
  have hd : Continuous (deriv F) := by
    rw [continuous_iff_continuousAt]; intro z; exact (hF.analyticAt z).deriv.continuousAt
  show ContinuousAt (fun z => deriv F z / F z) s
  exact hd.continuousAt.div hF.continuous.continuousAt hs

/-- **Symmetry reduction** of the rectangle integral of `φ = F'/F`. -/
theorem rectInt_phi_symm_gen (hF : Differentiable ℂ F) (hfe : ∀ s, F ((κ₂ : ℂ) - s) = c * F s)
    (hc : c ≠ 0) {σ₁ T : ℝ} (hT : ∀ x : ℝ, F (x + T * I) ≠ 0) :
    rectInt (logDeriv F) (κ₂ - σ₁) σ₁ (-T) T =
      2 * I * (∫ y in (-T)..T, logDeriv F (σ₁ + y * I)) -
        2 * (∫ x in (κ₂ / 2)..σ₁, logDeriv F (x + T * I)) +
        2 * (∫ x in (κ₂ / 2)..σ₁, logDeriv F (x + (-T) * I)) := by
  set φ := logDeriv F with hφ
  have hrefl : ∀ s, φ ((κ₂ : ℂ) - s) = -φ s := logDeriv_reflect hF hfe hc
  have hcont : Continuous fun x : ℝ => φ (x + T * I) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ContinuousAt.comp (g := φ) (continuousAt_logDeriv hF (hT x))
      (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x)
  -- left side
  have hleft : ∫ y in (-T)..T, φ (↑(κ₂ - σ₁) + ↑y * I) = -∫ y in (-T)..T, φ (σ₁ + y * I) := by
    have h1 : ∫ y in (-T)..T, φ (↑(κ₂ - σ₁) + ↑y * I) =
        ∫ y in (-T)..T, -φ (σ₁ + ((-y : ℝ) : ℂ) * I) := by
      apply integral_congr; intro y _
      simp only []
      have : (↑(κ₂ - σ₁) + ↑y * I : ℂ) = (κ₂ : ℂ) - ((σ₁ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        push_cast; ring
      rw [this, hrefl]
    rw [h1, intervalIntegral.integral_neg]
    congr 1
    have h2 := intervalIntegral.integral_comp_neg (a := -T) (b := T)
      (fun y : ℝ => φ (σ₁ + y * I))
    simp only [neg_neg] at h2
    exact h2
  -- bottom side
  have hbot : ∫ x in (κ₂ - σ₁)..σ₁, φ (↑x + ↑(-T) * I) =
      -∫ x in (κ₂ - σ₁)..σ₁, φ (↑x + ↑T * I) := by
    have h1 : ∫ x in (κ₂ - σ₁)..σ₁, φ (↑x + ↑(-T) * I) =
        ∫ x in (κ₂ - σ₁)..σ₁, -φ (((κ₂ - x : ℝ) : ℂ) + T * I) := by
      apply integral_congr; intro x _
      simp only []
      have : (↑x + ↑(-T) * I : ℂ) = (κ₂ : ℂ) - (((κ₂ - x : ℝ) : ℂ) + T * I) := by
        push_cast; ring
      rw [this, hrefl]
    rw [h1, intervalIntegral.integral_neg]
    congr 1
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => φ ((x : ℂ) + T * I)) κ₂]
    simp
  -- top side split
  have htop : ∫ x in (κ₂ - σ₁)..σ₁, φ (↑x + ↑T * I) =
      (∫ x in (κ₂ / 2)..σ₁, φ (x + T * I)) - ∫ x in (κ₂ / 2)..σ₁, φ (x + (-T) * I) := by
    rw [← integral_add_adjacent_intervals (b := κ₂ / 2) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have h1 : ∫ x in (κ₂ - σ₁)..κ₂ / 2, φ (↑x + ↑T * I) =
        ∫ x in (κ₂ - σ₁)..κ₂ / 2, -φ (((κ₂ - x : ℝ) : ℂ) + (-T : ℝ) * I) := by
      apply integral_congr; intro x _
      simp only []
      have : (↑x + ↑T * I : ℂ) = (κ₂ : ℂ) - (((κ₂ - x : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) := by
        push_cast; ring
      rw [this, hrefl]
    have h2 : ∫ x in (κ₂ - σ₁)..κ₂ / 2, φ (((κ₂ - x : ℝ) : ℂ) + (-T : ℝ) * I) =
        ∫ x in (κ₂ / 2)..σ₁, φ (x + (-T) * I) := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => φ ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) κ₂]
      have e1 : κ₂ - κ₂ / 2 = κ₂ / 2 := by ring
      have e2 : κ₂ - (κ₂ - σ₁) = σ₁ := by ring
      rw [e1, e2]
      push_cast; rfl
    rw [h1, intervalIntegral.integral_neg, h2]
    ring
  unfold rectInt
  rw [hbot, hleft, htop]
  simp only [smul_eq_mul]
  ring

end Abstract

/-! ### Application to `Λ(f,s)` -/

variable {k : ℕ}

/-- The number `N_f⁰` of real zeros of `Λ(f,·)`, with multiplicity. -/
noncomputable def realCount (f : CuspForm 𝒮ℒ (k : ℤ)) : ℕ :=
  ∑ᶠ u ∈ {u : ℂ | heckeLambda f u = 0 ∧ u.im = 0}, ord f u

lemma realSet_finite (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    {u : ℂ | heckeLambda f u = 0 ∧ u.im = 0}.Finite :=
  (zeroSet_finite f hf (-1) 0).subset fun u hu => ⟨hu.1, by rw [hu.2]; norm_num, hu.2.le⟩

/-- **Argument principle for `Λ(f,·)`, right-half form.** -/
theorem pi_count_eq_gen (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (D : NormData f) {T : ℝ}
    (hT0 : 0 < T) (hnon : ∀ u : ℂ, heckeLambda f u = 0 → u.im ≠ T) :
    π * (2 * (zeroCount f T : ℝ) + realCount f) =
      (∫ y in (-T)..T, logDeriv (heckeLambda f) (D.σ₁ + y * I)).re -
        (∫ x in ((k : ℝ) / 2)..D.σ₁, logDeriv (heckeLambda f) (x + T * I)).im +
        (∫ x in ((k : ℝ) / 2)..D.σ₁, logDeriv (heckeLambda f) (x + (-T) * I)).im := by
  classical
  have hk := weight_ge f hf
  have hk1 : 1 ≤ k := by omega
  set Λ := heckeLambda f with hΛ
  have hΛd : Differentiable ℂ Λ := heckeLambda_entire f hk1
  have hfe : ∀ s, Λ ((k : ℝ) - s) = I ^ k * Λ s := by
    intro s; have := heckeLambda_functional_equation f hk1 s; simpa using this
  have hc : I ^ k ≠ 0 := pow_ne_zero _ I_ne_zero
  set σ₁ := D.σ₁
  have hσ₁ : ((k : ℝ) + 1) / 2 + 1 ≤ σ₁ := D.hσ₁
  -- non-vanishing on the horizontal sides
  have hnon' : ∀ u : ℂ, Λ u = 0 → u.im ≠ -T := by
    intro u h0 h
    apply hnon ((k : ℂ) - u) (Lam_reflect_zero f hk1 h0)
    simp [h]
  have hT : ∀ x : ℝ, Λ (x + T * I) ≠ 0 := fun x h => hnon _ h (by simp)
  have hT' : ∀ x : ℝ, Λ (x + (-T) * I) ≠ 0 := fun x h => hnon' _ h (by simp)
  have hB : ∀ z ∈ ZeroCountRvM.rectBd ((k : ℝ) - σ₁) σ₁ (-T) T, Λ z ≠ 0 := by
    intro z hz
    rcases hz with ⟨_, h | h⟩ | ⟨_, h | h⟩
    · have hz : z = (z.re : ℂ) + ((-T : ℝ) : ℂ) * I := by apply Complex.ext <;> simp [h]
      rw [hz]; exact_mod_cast hT' _
    · have hz : z = (z.re : ℂ) + T * I := by apply Complex.ext <;> simp [h]
      rw [hz]; exact hT _
    · exact D.Lam_ne_zero_left hk1 (by rw [h])
    · exact D.Lam_ne_zero_right (by rw [h])
  obtain ⟨S, hS, hInt⟩ := ZeroCountRvM.arg_principle_rect hΛd
    ⟨σ₁, D.Lam_ne_zero_right (by simp only [ofReal_re]; exact le_rfl)⟩ (by linarith : (k : ℝ) - σ₁ < σ₁)
    (by linarith : -T < T) hB
  have hsym := rectInt_phi_symm_gen (κ₂ := (k : ℝ)) hΛd hfe hc (σ₁ := σ₁) hT
  rw [hsym] at hInt
  -- the count
  have hre_lt : ∀ u, Λ u = 0 → u.re < σ₁ := by
    intro u hu; by_contra h; push Not at h; exact D.Lam_ne_zero_right h hu
  have hre_gt : ∀ u, Λ u = 0 → (k : ℝ) - σ₁ < u.re := by
    intro u hu; by_contra h; push Not at h; exact D.Lam_ne_zero_left hk1 h hu
  have hcount : ∑ u ∈ S, ord f u = 2 * zeroCount f T + realCount f := by
    set Sp := S.filter (fun u => 0 < u.im)
    set Sn := S.filter (fun u => u.im < 0)
    set S0 := S.filter (fun u => u.im = 0)
    have hsplit : ∑ u ∈ S, ord f u = ∑ u ∈ Sp, ord f u + ∑ u ∈ Sn, ord f u + ∑ u ∈ S0, ord f u := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun u => 0 < u.im),
        ← Finset.sum_filter_add_sum_filter_not (S.filter fun u => ¬ 0 < u.im) (fun u => u.im < 0),
        Finset.filter_filter, Finset.filter_filter]
      have e1 : S.filter (fun u => ¬ 0 < u.im ∧ u.im < 0) = Sn := by
        apply Finset.filter_congr; intro u _; constructor
        · exact fun h => h.2
        · intro h; exact ⟨by linarith, h⟩
      have e2 : S.filter (fun u => ¬ 0 < u.im ∧ ¬ u.im < 0) = S0 := by
        apply Finset.filter_congr; intro u _; constructor
        · intro h; push Not at h; linarith [h.1, h.2]
        · intro h; constructor <;> linarith
      rw [e1, e2]; ring
    have hp : ∑ u ∈ Sp, ord f u = zeroCount f T := by
      unfold zeroCount
      rw [zeroCountAB_eq f hf]
      congr 1
      ext u
      simp only [Sp, Finset.mem_filter, hS, Set.Finite.mem_toFinset, zeroSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h0, -, -, -, h4⟩, h5⟩; exact ⟨h0, h5, h4.le⟩
      · rintro ⟨h0, h3, h4⟩
        exact ⟨⟨h0, hre_gt u h0, hre_lt u h0, by linarith, lt_of_le_of_ne h4 (hnon u h0)⟩, h3⟩
    have hn : ∑ u ∈ Sn, ord f u = ∑ u ∈ Sp, ord f u := by
      set g : ℂ → ℂ := fun u => (k : ℂ) - u
      have hginj : Set.InjOn g Sn := by intro x _ y _ h; simpa [g] using h
      have himg : Sn.image g = Sp := by
        ext w
        simp only [Finset.mem_image, Sn, Sp, Finset.mem_filter, hS]
        constructor
        · rintro ⟨u, ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩, rfl⟩
          have hz := Lam_reflect_zero f hk1 h0
          refine ⟨⟨hz, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [g] <;>
            linarith [hre_gt _ hz, hre_lt _ hz]
        · rintro ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩
          refine ⟨(k : ℂ) - w, ⟨⟨Lam_reflect_zero f hk1 h0, ?_, ?_, ?_, ?_⟩, ?_⟩, by simp [g]⟩ <;>
            simp <;> linarith
      rw [← himg, Finset.sum_image hginj]
      exact Finset.sum_congr rfl fun u _ => (ord_reflect f hk1 u).symm
    have h0 : ∑ u ∈ S0, ord f u = realCount f := by
      unfold realCount
      rw [finsum_mem_eq_finite_toFinset_sum _ (realSet_finite f hf)]
      congr 1
      ext u
      simp only [S0, Finset.mem_filter, hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h0, -⟩, h5⟩; exact ⟨h0, h5⟩
      · rintro ⟨h0, h5⟩
        exact ⟨⟨h0, hre_gt u h0, hre_lt u h0, by linarith, by linarith⟩, h5⟩
    rw [hsplit, hn, hp, h0]; ring
  have hcountC : (∑ u ∈ S, (analyticOrderNatAt Λ u : ℂ)) =
      ((2 * zeroCount f T + realCount f : ℕ) : ℂ) := by
    rw [← hcount]; push_cast; rfl
  rw [hcountC] at hInt
  -- take imaginary parts
  set V := ∫ y in (-T)..T, logDeriv Λ (σ₁ + y * I)
  set H₁ := ∫ x in ((k : ℝ) / 2)..σ₁, logDeriv Λ (x + T * I)
  set H₂ := ∫ x in ((k : ℝ) / 2)..σ₁, logDeriv Λ (x + (-T) * I)
  rw [← Complex.ofReal_natCast] at hInt
  have hIm := congrArg Complex.im hInt
  simp only [sub_im, add_im, mul_im, mul_re, I_re, I_im, re_ofNat, im_ofNat, ofReal_re,
    ofReal_im] at hIm
  push_cast at hIm
  linarith

end RamanujanTau.GeneralZeros
