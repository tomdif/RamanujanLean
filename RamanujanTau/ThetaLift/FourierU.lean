import RamanujanTau.ThetaLift.HalfExpansion

/-!
# The Fourier coefficient in `u`

The function `𝔽(z) = F₀(Nz)` has an expansion in `e(N(24m-j)z/24)`, with polynomially bounded
coefficients. Integrating against `e(x²u/24)` over a period picks out the term with `x² = N(24m-j)`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open ModularForm Filter Complex Function
open UpperHalfPlane hiding I
open scoped MatrixGroups Real ComplexConjugate

noncomputable section

local notation "𝕢" => Periodic.qParam

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j N : ℕ)

/-- The point `Nz`. -/
def nP {N : ℕ} (hN : 0 < N) (z : ℍ) : ℍ := ⟨(N : ℂ) * z, by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  simpa using mul_pos this z.im_pos⟩

/-- The function `𝔽(z) = F₀(Nz)`. -/
def fF {N : ℕ} (hN : 0 < N) (z : ℍ) : ℂ := G (nP hN z) / η ((nP hN z : ℍ) : ℂ) ^ j

/-- The exponent `N(24m-j)/24`. -/
def eX (j N m : ℕ) : ℝ := N * (24 * m - j) / 24

/-- The `m`-th term of the expansion. -/
lemma exp_term_eq {N : ℕ} (hN : 0 < N) (z : ℍ) (m : ℕ) :
    (𝕢 (24 : ℝ) (nP hN z : ℂ))⁻¹ ^ j * 𝕢 (1 : ℝ) (nP hN z : ℂ) ^ m =
      cexp (2 * π * I * (eX j N m) * z) := by
  simp only [Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_neg, ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  simp only [nP, eX]
  push_cast
  ring

/-- **The expansion of `𝔽`.** -/
theorem hasSum_fF {N : ℕ} (hN : 0 < N) (z : ℍ) :
    HasSum (fun m : ℕ => cA G j m * cexp (2 * π * I * (eX j N m) * z)) (fF G j hN z) := by
  have h := (hasSum_hP G j (nP hN z)).mul_left ((𝕢 (24 : ℝ) (nP hN z : ℂ))⁻¹ ^ j)
  have e : fF G j hN z = (𝕢 (24 : ℝ) (nP hN z : ℂ))⁻¹ ^ j * hP G j (nP hN z) := cusp_div_eta G j _
  rw [e]
  convert h using 2 with m
  rw [← exp_term_eq j hN]
  ring

lemma norm_term (m : ℕ) (N : ℕ) (z : ℂ) :
    ‖cexp (2 * π * I * (eX j N m) * z)‖ = Real.exp (-(2 * π * eX j N m * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have e : 2 * (π : ℂ) * I * (eX j N m) * z = I * ((2 * π * eX j N m : ℝ) : ℂ) * z := by
    push_cast
    ring
  rw [e]
  simp

/-- The coefficients are summable against the exponentials. -/
theorem summable_coef {hj : j < 24} {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) :
    Summable fun m : ℕ => ‖cA G j m‖ * Real.exp (-(2 * π * eX j N m * v)) := by
  obtain ⟨C, hC0, hC⟩ := norm_cA_le G hj
  obtain ⟨K, hK⟩ := exists_nat_ge ((k' : ℝ) / 2 - j / 4)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set r : ℝ := Real.exp (-(2 * π * N * v)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
    have := Real.pi_pos
    have : 0 < 2 * π * N * v := by positivity
    linarith)
  have hbase := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) K
    (r := r) (by rwa [Real.norm_of_nonneg hr0.le])).mul_left
    (C * Real.exp (2 * π * (N * j / 24) * v))
  refine Summable.of_norm_bounded_eventually_nat hbase ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 := hC m hm
  have h2 : (m : ℝ) ^ ((k' : ℝ) / 2 - j / 4) ≤ (m : ℝ) ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hmR hK
  have h3 : Real.exp (-(2 * π * eX j N m * v)) =
      Real.exp (2 * π * (N * j / 24) * v) * r ^ m := by
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold eX
    ring
  rw [Real.norm_of_nonneg (by positivity), h3]
  calc _ ≤ (C * (m : ℝ) ^ K) * (Real.exp (2 * π * (N * j / 24) * v) * r ^ m) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = _ := by ring

/-- The orthogonality of exponentials on a period. -/
lemma integral_exp_int (D : ℤ) :
    ∫ u in (0 : ℝ)..1, cexp (2 * π * I * D * u) = if D = 0 then 1 else 0 := by
  by_cases hD : D = 0
  · simp [hD]
  · have hc : 2 * (π : ℂ) * I * D ≠ 0 := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
      simp [hπ, hD', I_ne_zero]
    rw [if_neg hD, integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * D * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I D
      rw [← this]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

/-- The point `u + iv`. -/
def zUV (u : ℝ) {v : ℝ} (hv : 0 < v) : ℍ := ⟨(u : ℂ) + v * I, by simpa using hv⟩

open Classical in
/-- The coefficient selected by `x`. -/
def cX (x : ℤ) : ℂ :=
  if h : ∃ m : ℕ, x ^ 2 = (N : ℤ) * (24 * m - j) then conj (cA G j h.choose) else 0

/-- The integer frequency. -/
lemma freq_int {N : ℕ} {x : ℤ} (hx : (24 : ℤ) ∣ x ^ 2 - 1) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1)
    (m : ℕ) : ∃ D : ℤ, ((x : ℝ) ^ 2 - N * (24 * m - j)) / 24 = D ∧
      (D = 0 ↔ x ^ 2 = (N : ℤ) * (24 * m - j)) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hNj
  refine ⟨a + b - N * m, ?_, ?_⟩
  · have hax : (x : ℝ) ^ 2 = 24 * a + 1 := by exact_mod_cast (by linarith : x ^ 2 = 24 * a + 1)
    have hbx : (N : ℝ) * j = 24 * b - 1 := by exact_mod_cast (by linarith : (N : ℤ) * j = 24 * b - 1)
    push_cast
    rw [hax]
    linear_combination hbx / 24
  · constructor
    · intro h
      linear_combination ha + hb + 24 * h
    · intro h
      have h24 : 24 * (a + b - N * m) = 0 := by linear_combination h - ha - hb
      simpa using h24

/-- The `m`-th term of the conjugate expansion, integrated against a character. -/
def fTerm {v : ℝ} (x : ℤ) (m : ℕ) : C(ℝ, ℂ) where
  toFun u := conj (cA G j m) * conj (cexp (2 * π * I * (eX j N m) * ((u : ℂ) + v * I))) *
    cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u)
  continuous_toFun := by
    have h1 : Continuous fun u : ℝ => cexp (2 * π * I * (eX j N m) * ((u : ℂ) + v * I)) := by fun_prop
    have h2 : Continuous fun u : ℝ => conj (cexp (2 * π * I * (eX j N m) * ((u : ℂ) + v * I))) :=
      continuous_conj.comp h1
    fun_prop

lemma fTerm_apply {v : ℝ} (x : ℤ) (m : ℕ) (u : ℝ) :
    (fTerm G j N (v := v) x m) u = conj (cA G j m) *
      ((Real.exp (-(2 * π * eX j N m * v)) : ℝ) : ℂ) *
        cexp (2 * π * I * ((((x : ℝ) ^ 2 - N * (24 * m - j)) / 24 : ℝ) : ℂ) * u) := by
  change conj (cA G j m) * conj (cexp (2 * π * I * (eX j N m) * ((u : ℂ) + v * I))) *
    cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) = _
  rw [← Complex.exp_conj, ofReal_exp, mul_assoc, mul_assoc (conj (cA G j m)), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  simp only [map_mul, map_add, conj_I, conj_ofReal, map_ofNat]
  simp only [eX]
  push_cast
  linear_combination (2 * (π : ℂ) * (N * (24 * m - j) / 24) * v) * Complex.I_sq

/-- The value of the integral of a term. -/
lemma integral_fTerm {v : ℝ} {x : ℤ} (hx : (24 : ℤ) ∣ x ^ 2 - 1) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1)
    (m : ℕ) : ∫ u in (0 : ℝ)..1, (fTerm G j N (v := v) x m) u =
      if x ^ 2 = (N : ℤ) * (24 * m - j) then
        conj (cA G j m) * ((Real.exp (-(2 * π * eX j N m * v)) : ℝ) : ℂ) else 0 := by
  obtain ⟨D, hD, hiff⟩ := freq_int (N := N) (j := j) hx hNj m
  simp only [fTerm_apply, hD]
  rw [intervalIntegral.integral_const_mul]
  have h := integral_exp_int D
  simp only [ofReal_intCast]
  rw [h]
  by_cases h0 : D = 0
  · rw [if_pos h0, if_pos (hiff.mp h0), mul_one]
  · rw [if_neg h0, if_neg (fun h' => h0 (hiff.mpr h')), mul_zero]

/-- **The Fourier coefficient in `u`.** -/
theorem fourier_u {hj : j < 24} {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 0 < v) {x : ℤ}
    (hx : (24 : ℤ) ∣ x ^ 2 - 1) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) :
    ∫ u in (0 : ℝ)..1, conj (fF G j hN (zUV u hv)) * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) =
      cX G j N x * ((Real.exp (-(2 * π * ((x : ℝ) ^ 2 / 24) * v)) : ℝ) : ℂ) := by
  have hS := summable_coef G j (hj := hj) hN hv
  have hnorm : Summable fun m : ℕ => ‖(fTerm G j N (v := v) x m).restrict
      (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hS
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun u => ?_
    rw [ContinuousMap.restrict_apply, fTerm_apply, norm_mul, norm_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have : ‖cexp (2 * π * I * ((((x : ℝ) ^ 2 - N * (24 * m - j)) / 24 : ℝ) : ℂ) * (u : ℝ))‖ = 1 := by
      have e : 2 * (π : ℂ) * I * ((((x : ℝ) ^ 2 - N * (24 * m - j)) / 24 : ℝ) : ℂ) * ((u : ℝ) : ℂ) =
          ((2 * π * (((x : ℝ) ^ 2 - N * (24 * m - j)) / 24) * u : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [e, Complex.norm_exp_ofReal_mul_I]
    rw [this, mul_one]
  have hsum := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hnorm
  have hpt : ∀ u : ℝ, ∑' m : ℕ, (fTerm G j N (v := v) x m) u =
      conj (fF G j hN (zUV u hv)) * cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u) := by
    intro u
    have h := (hasSum_fF G j hN (zUV u hv))
    have hc := (Complex.hasSum_conj'.mpr h).mul_right
      (cexp (2 * π * I * ((x : ℂ) ^ 2 / 24) * u))
    refine HasSum.tsum_eq ?_
    convert hc using 2 with m
    rw [map_mul]
    rfl
  rw [funext hpt] at hsum
  simp only [integral_fTerm G j N hx hNj] at hsum
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hsum.tsum_eq]
  by_cases hex : ∃ m : ℕ, x ^ 2 = (N : ℤ) * (24 * m - j)
  · have huniq : ∀ m : ℕ, x ^ 2 = (N : ℤ) * (24 * m - j) → m = hex.choose := by
      intro m hm
      have h2 := hex.choose_spec
      have h3 := mul_left_cancel₀ hNZ (hm.symm.trans h2)
      have h4 : (24 : ℤ) * m = 24 * hex.choose := by linarith
      have h5 : (m : ℤ) = hex.choose := by linarith
      exact_mod_cast h5
    have hsingle := hasSum_single (f := fun m : ℕ => if x ^ 2 = (N : ℤ) * (24 * m - j) then
        conj (cA G j m) * ((Real.exp (-(2 * π * eX j N m * v)) : ℝ) : ℂ) else 0) hex.choose
      (fun m hm => if_neg fun h => hm (huniq m h))
    rw [hsingle.tsum_eq, if_pos hex.choose_spec, cX, dif_pos hex]
    have hval : eX j N hex.choose = (x : ℝ) ^ 2 / 24 := by
      have h2 : (x : ℝ) ^ 2 = N * (24 * hex.choose - j) := by exact_mod_cast hex.choose_spec
      unfold eX
      rw [h2]
    rw [hval]
  · have hz : ∀ m : ℕ, ¬ x ^ 2 = (N : ℤ) * (24 * m - j) := fun m h => hex ⟨m, h⟩
    simp only [if_neg (hz _), tsum_zero, cX, dif_neg hex, zero_mul]

/-- The Hecke bound and exponential decay for `F₀`. -/
theorem norm_F0_le {hj : j < 24} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℍ, ‖G t / η (t : ℂ) ^ j‖ ≤
      C * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) * Real.exp (-(2 * π / 24 * t.im)) := by
  have hπ := Real.pi_pos
  obtain ⟨C₁, hC₁0, hC₁⟩ := hecke_half G hj
  have hO := CuspFormClass.exp_decay_atImInfty (h := 1) G one_pos one_mem_strictPeriods_SL
  obtain ⟨C₂, hC₂, hO'⟩ := hO.exists_pos
  have hev := hO'.bound.and eP_bounds
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  set A' := max A 1 with hA'
  have hA'pos : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c := 2 * π / 24 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨C₁ * Real.exp (c * A') + C₂ * 2 ^ j, by positivity, fun t => ?_⟩
  have hv := t.im_pos
  have hE : 0 < Real.exp (-(c * t.im)) := Real.exp_pos _
  have hPw : 0 ≤ t.im ^ (-((k' : ℝ) / 2 - j / 4)) := by positivity
  by_cases hlarge : A' ≤ t.im
  · obtain ⟨h1, -, h2⟩ := hA t (le_trans (le_max_left _ _) hlarge)
    have hq : ‖(𝕢 (24 : ℝ) (t : ℂ))⁻¹‖ ^ j = Real.exp (j * (2 * π * t.im / 24)) := by
      rw [norm_inv, norm_qParam24, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    have hPi : ‖hP G j t‖ ≤ ‖G t‖ * 2 ^ j := by
      simp only [hP, Pi.mul_apply, Pi.pow_apply, ePi, norm_mul, norm_pow]
      gcongr
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have h3 : ‖G t / η (t : ℂ) ^ j‖ ≤ C₂ * 2 ^ j * Real.exp (-(c * t.im)) := by
      rw [cusp_div_eta, norm_mul, norm_pow, hq]
      have h4 : Real.exp (j * (2 * π * t.im / 24)) * Real.exp (-2 * π * t.im / (1 : ℝ)) ≤
          Real.exp (-(c * t.im)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hjR : (j : ℝ) ≤ 23 := by exact_mod_cast Nat.lt_succ_iff.mp hj
        have hv2 : 0 < 2 * π * t.im / 24 := by positivity
        have e : -(c * t.im) = -(2 * π * t.im / 24) := by rw [hc]; ring
        rw [e, div_one]
        nlinarith
      calc _ ≤ Real.exp (j * (2 * π * t.im / 24)) *
            ((C₂ * Real.exp (-2 * π * t.im / (1 : ℝ))) * 2 ^ j) := by
            gcongr
            exact hPi.trans (by gcongr)
        _ = C₂ * 2 ^ j * (Real.exp (j * (2 * π * t.im / 24)) *
            Real.exp (-2 * π * t.im / (1 : ℝ))) := by ring
        _ ≤ _ := by gcongr
    calc _ ≤ C₂ * 2 ^ j * Real.exp (-(c * t.im)) := h3
      _ ≤ (C₁ * Real.exp (c * A') + C₂ * 2 ^ j) * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) *
          Real.exp (-(c * t.im)) := by
        have hp : 0 ≤ C₁ * Real.exp (c * A') := by positivity
        have hb : 0 ≤ C₂ * 2 ^ j := by positivity
        have h5 : C₂ * 2 ^ j ≤ (C₁ * Real.exp (c * A') + C₂ * 2 ^ j) *
            (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) := by
          nlinarith [mul_nonneg hp hPw, mul_nonneg hb hPw]
        exact mul_le_mul_of_nonneg_right h5 hE.le
  · have hsmall : t.im < A' := not_le.mp hlarge
    have h1 := hC₁ t
    have h2 : 1 ≤ Real.exp (c * A') * Real.exp (-(c * t.im)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc _ ≤ C₁ * t.im ^ (-((k' : ℝ) / 2 - j / 4)) := h1
      _ ≤ C₁ * t.im ^ (-((k' : ℝ) / 2 - j / 4)) * (Real.exp (c * A') * Real.exp (-(c * t.im))) :=
        le_mul_of_one_le_right (by positivity) h2
      _ ≤ _ := by
        have hp := mul_nonneg (by positivity : 0 ≤ C₁ * Real.exp (c * A')) hPw
        have hp2 : 0 ≤ C₂ * 2 ^ j * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) := by positivity
        have hp3 : 0 ≤ C₁ * Real.exp (c * A') := by positivity
        have e : (C₁ * Real.exp (c * A') + C₂ * 2 ^ j) * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) *
            Real.exp (-(c * t.im)) = C₁ * t.im ^ (-((k' : ℝ) / 2 - j / 4)) *
              (Real.exp (c * A') * Real.exp (-(c * t.im))) +
            (C₁ * Real.exp (c * A') + C₂ * 2 ^ j * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1)) *
              Real.exp (-(c * t.im)) := by ring
        rw [e]
        have : 0 ≤ (C₁ * Real.exp (c * A') + C₂ * 2 ^ j * (t.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1)) *
            Real.exp (-(c * t.im)) := by positivity
        linarith

lemma continuous_nP {N : ℕ} (hN : 0 < N) : Continuous (nP hN) := by
  refine isEmbedding_coe.continuous_iff.mpr ?_
  change Continuous fun z : ℍ => (N : ℂ) * (z : ℂ)
  fun_prop

/-- `𝔽` is continuous on `ℍ`. -/
lemma continuous_fF {N : ℕ} (hN : 0 < N) : Continuous (fF G j hN) := by
  have hG : Continuous G := (CuspFormClass.holo G).continuous
  have hE : Continuous fun t : ℍ => η (t : ℂ) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have h := (differentiableAt_eta_of_mem_upperHalfPlaneSet t.2).continuousAt
    exact h.comp UpperHalfPlane.continuous_coe.continuousAt
  have hne : ∀ t : ℍ, η (t : ℂ) ^ j ≠ 0 := fun t => pow_ne_zero j (eta_ne_zero t.2)
  unfold fF
  exact (hG.comp (continuous_nP hN)).div ((hE.comp (continuous_nP hN)).pow j)
    fun z => hne (nP hN z)

/-- The bound for `𝔽` on `ℍ`. -/
theorem norm_fF_le {hj : j < 24} {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℍ, ‖fF G j hN z‖ ≤
      C * (z.im ^ (-((k' : ℝ) / 2 - j / 4)) + 1) * Real.exp (-(2 * π / 24 * z.im)) := by
  obtain ⟨C, hC0, hC⟩ := norm_F0_le G j (hj := hj)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set e := (k' : ℝ) / 2 - j / 4
  refine ⟨C * ((N : ℝ) ^ (-e) + 1), by positivity, fun z => ?_⟩
  have hv := z.im_pos
  have him : (nP hN z).im = N * z.im := by
    change ((N : ℂ) * (z : ℂ)).im = (N : ℝ) * z.im
    simp
  have h := hC (nP hN z)
  rw [him, Real.mul_rpow hNpos.le hv.le] at h
  have hπ := Real.pi_pos
  have hE : Real.exp (-(2 * π / 24 * (N * z.im))) ≤ Real.exp (-(2 * π / 24 * z.im)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ 2 * π / 24 * z.im := by positivity
    nlinarith
  have hp1 : 0 ≤ (N : ℝ) ^ (-e) := by positivity
  have hp2 : 0 ≤ z.im ^ (-e) := by positivity
  calc _ ≤ _ := h
    _ ≤ C * ((N : ℝ) ^ (-e) * z.im ^ (-e) + 1) * Real.exp (-(2 * π / 24 * z.im)) := by gcongr
    _ ≤ _ := by
      have h3 : (N : ℝ) ^ (-e) * z.im ^ (-e) + 1 ≤ ((N : ℝ) ^ (-e) + 1) * (z.im ^ (-e) + 1) := by
        nlinarith
      have hc : 0 ≤ C * Real.exp (-(2 * π / 24 * z.im)) := by positivity
      have := mul_le_mul_of_nonneg_left h3 hc
      calc _ = C * Real.exp (-(2 * π / 24 * z.im)) * ((N : ℝ) ^ (-e) * z.im ^ (-e) + 1) := by ring
        _ ≤ _ := this
        _ = _ := by ring

end

end RamanujanTau.ThetaLift
