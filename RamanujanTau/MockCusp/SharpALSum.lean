/-
# The key lemma with the non-uniform denominator bound

`fourier_kern_le'`: the Mordell-integral bound of `fourier_kern_le`, keeping the denominator inside the integral:
`|𝓕kern(ξ)| ≤ e^{kC(y)+2πξy} ∫ e^{−P(x−x₀)²}/|kD(x+iy)| dx`, `P = A Re α T²`.

`kern_sharp`: with `bad_integral_le` and the optimal `η` (`opt_eta`),
`|𝓕kern(ξ)| ≤ e^{kC(y)+2πξy} · Jb`, `Jb = 2a + 2√(ab)`, `a = 3√(π/P)`, `b = (2/(m|β|))(1 + 16|β|²/(π²P))`,
`|β| = |α|DT`. Compared with `fourier_kern_le` (`Jb = √(π/P)/m`) the uniform bound `m` enters only as `m^{−1/2}`.

`al_sum_le'`: the anti-periodic Appell–Lerch sum with a *per-class* lower bound `m(ρ)` for the denominators:
`|S| ≤ Σ_{ρ<T} Jb(m ρ) · e^{A Y₀²|α|²/Re α + B² Re α/(4A)} / sinh(πY₀/T)`.
-/
import RamanujanTau.MockCusp.ALSum
import RamanujanTau.MockCusp.BadSet

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set
open scoped Topology Real FourierTransform

noncomputable section

variable {α : ℂ} {A B D E : ℝ} {T : ℕ} {ρ : ℤ} {w : ℂ}

lemma norm_kG_eq (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) (ξ x y : ℝ) :
    ‖kG α A B D E T ρ w ξ (x + y * I)‖ =
      Real.exp (kC α A B T y + 2 * π * ξ * y) *
        (Real.exp (-(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2) / ‖kD α D E T ρ w (x + y * I)‖) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold kG kern
  rw [norm_mul, norm_div, norm_phase, Complex.norm_exp, re_expo hα.ne' hA.ne' hT', Real.exp_add,
    Real.exp_add]
  ring

/-- **Fourier bound for the class kernel, denominator kept inside the integral.** -/
theorem fourier_kern_le' (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {m : ℝ} (hm : 0 < m) (y : ℝ)
    (hden : ∀ x y' : ℝ, y' ∈ uIcc 0 y → m ≤ ‖kD α D E T ρ w (x + y' * I)‖) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => kern α A B D E T ρ w x) ξ‖ ≤
      Real.exp (kC α A B T y + 2 * π * ξ * y) *
        ∫ x : ℝ, Real.exp (-(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2) /
          ‖kD α D E T ρ w (x + y * I)‖ := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : 0 < A * α.re * T ^ 2 := by positivity
  set P := A * α.re * T ^ 2 with hPdef
  have hne : ∀ x y' : ℝ, y' ∈ uIcc 0 y → kD α D E T ρ w (x + y' * I) ≠ 0 := fun x y' hy' h => by
    have := hden x y' hy'; rw [h, norm_zero] at this; linarith
  have hF : 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) ξ = ∫ x : ℝ, kG α A B D E T ρ w ξ x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [kG, smul_eq_mul]
    congr 2
    push_cast; ring
  have h0mem : (0 : ℝ) ∈ uIcc 0 y := left_mem_uIcc
  have hymem : y ∈ uIcc 0 y := right_mem_uIcc
  set X0 : ℝ := (|2 * A * α.im * T| * |y| / |2 * A * α.re| + |B * α.re| / |2 * A * α.re| + |(ρ : ℝ)|) / T
  set C1 : ℝ := A * (T * |y|) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) + π * |y| +
    2 * π * |ξ| * |y|
  have hx0 : ∀ y' ∈ uIcc 0 y, |kx0 α A B T ρ y'| ≤ X0 := by
    intro y' hy'
    have hy'' : |y'| ≤ |y| := abs_le_of_mem_uIcc0 hy'
    unfold kx0
    rw [abs_div, abs_of_pos hT']
    refine div_le_div_of_nonneg_right ?_ hT'.le
    calc |(2 * A * α.im * (T * y') - B * α.re) / (2 * A * α.re) - ρ|
        ≤ |(2 * A * α.im * (T * y') - B * α.re) / (2 * A * α.re)| + |(ρ : ℝ)| := abs_sub _ _
      _ ≤ |2 * A * α.im * T| * |y| / |2 * A * α.re| + |B * α.re| / |2 * A * α.re| + |(ρ : ℝ)| := by
          gcongr
          rw [abs_div]
          rw [← add_div]
          gcongr
          calc |2 * A * α.im * (T * y') - B * α.re| ≤ |2 * A * α.im * (T * y')| + |B * α.re| :=
                abs_sub _ _
            _ ≤ _ := by
                rw [show 2 * A * α.im * (T * y') = (2 * A * α.im * T) * y' by ring, abs_mul]
                gcongr
  have hC1 : ∀ y' ∈ uIcc 0 y, kC α A B T y' + 2 * π * ξ * y' ≤ C1 := by
    intro y' hy'
    have hy'' : |y'| ≤ |y| := abs_le_of_mem_uIcc0 hy'
    unfold kC
    have e1 : (T * y') ^ 2 ≤ (T * |y|) ^ 2 := by
      rw [mul_pow, mul_pow, ← sq_abs y']; gcongr
    have e2 : -(π * y') ≤ π * |y| := by
      have := neg_abs_le y'; nlinarith [Real.pi_pos, abs_nonneg y']
    have e3 : 2 * π * ξ * y' ≤ 2 * π * |ξ| * |y| := by
      have : ξ * y' ≤ |ξ| * |y| := by
        calc ξ * y' ≤ |ξ * y'| := le_abs_self _
          _ = |ξ| * |y'| := abs_mul _ _
          _ ≤ |ξ| * |y| := by gcongr
      nlinarith [Real.pi_pos]
    have e4 : A * (T * y') ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re ≤
        A * (T * |y|) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re := by gcongr
    linarith
  set Bf : ℝ → ℝ := fun x => (1 / m) * Real.exp (C1 + P * X0 ^ 2) * Real.exp (-(P / 2) * x ^ 2)
  have hBf : ∀ x y' : ℝ, y' ∈ uIcc 0 y → ‖kG α A B D E T ρ w ξ (x + y' * I)‖ ≤ Bf x := by
    intro x y' hy'
    refine (norm_kG_le hα hA hT hm ξ x y' (hden x y' hy')).trans ?_
    simp only [Bf, mul_assoc]
    gcongr
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := hC1 y' hy'
    have h2 := hx0 y' hy'
    have h3 : x ^ 2 / 2 - X0 ^ 2 ≤ (x - kx0 α A B T ρ y') ^ 2 := by
      have : |kx0 α A B T ρ y'| ^ 2 ≤ X0 ^ 2 := by
        have := abs_nonneg (kx0 α A B T ρ y'); nlinarith
      rw [sq_abs] at this
      nlinarith [sq_nonneg (x - 2 * kx0 α A B T ρ y')]
    have hPe : A * (α.re * (T : ℝ) ^ 2) = P := by rw [hPdef]; ring
    have h4 := mul_le_mul_of_nonneg_left h3 hP.le
    nlinarith
  have hBt : ∀ {l : Filter ℝ}, Tendsto (fun x : ℝ => x ^ 2) l atTop → Tendsto Bf l (𝓝 0) := by
    intro l hl
    have : Tendsto (fun x : ℝ => Real.exp (-(P / 2) * x ^ 2)) l (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_nhds.neg_mul_atTop (by linarith) hl))
    simpa [Bf] using this.const_mul ((1 / m) * Real.exp (C1 + P * X0 ^ 2))
  have hsqt : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hsqb : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
    simpa using (tendsto_pow_atTop (two_ne_zero)).comp tendsto_neg_atBot_atTop |>.congr
      (fun x => by simp [neg_sq])
  have hint : ∀ y' ∈ uIcc 0 y, Integrable (fun x : ℝ => kG α A B D E T ρ w ξ (x + y' * I)) := by
    intro y' hy'
    refine Integrable.mono' ((integrable_gauss P (kx0 α A B T ρ y') (kC α A B T y' + 2 * π * ξ * y')
      hP).const_mul (1 / m)) ?_ (Eventually.of_forall fun x => norm_kG_le hα hA hT hm ξ x y' (hden x y' hy'))
    refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.2 fun x => ?_)
    exact ContinuousAt.comp (g := kG α A B D E T ρ w ξ) (f := fun x : ℝ => (x : ℂ) + y' * I)
      (kG_differentiableAt ξ (hne x y' hy')).continuousAt (by fun_prop)
  have hshift := integral_shift (G := kG α A B D E T ρ w ξ) (c := y)
    (fun x y' hy' => kG_differentiableAt ξ (hne x y' hy')) Bf (hBt hsqt) (hBt hsqb) hBf
    (by simpa using hint 0 h0mem) (hint y hymem)
  rw [hF, hshift]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [norm_kG_eq hα hA hT ξ _ y]
  rw [integral_const_mul]

/-- the per-class constant `Jb = 2a + 2√(ab)`. -/
def Jb (α : ℂ) (A D : ℝ) (T : ℕ) (m : ℝ) : ℝ :=
  2 * (3 * √(π / (A * α.re * T ^ 2))) + 2 * √(3 * √(π / (A * α.re * T ^ 2)) *
    (1 / m * (2 / (‖α‖ * D * T) * (1 + 16 * (‖α‖ * D * T) ^ 2 / (π ^ 2 * (A * α.re * T ^ 2))))))

/-- **Sharp Fourier bound for the class kernel.** -/
theorem kern_sharp (hα : 0 < α.re) (hA : 0 < A) (hD : 0 < D) (hT : 0 < T) (hw : w ≠ 0) {m : ℝ} (hm : 0 < m)
    (y : ℝ) (hden : ∀ x y' : ℝ, y' ∈ uIcc 0 y → m ≤ ‖kD α D E T ρ w (x + y' * I)‖) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => kern α A B D E T ρ w x) ξ‖ ≤
      Real.exp (kC α A B T y + 2 * π * ξ * y) * Jb α A D T m := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : 0 < A * α.re * T ^ 2 := by positivity
  have hα0 : α ≠ 0 := fun h => by rw [h] at hα; simp at hα
  set v₀ : ℂ := Complex.log w + -(α * (D * ((ρ : ℂ) + T * (y * I)) + E))
  set β : ℂ := -(α * D * T)
  have hβ : β ≠ 0 := by
    simp only [β, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero hα0 (by exact_mod_cast hD.ne')) (by exact_mod_cast hT.ne')
  have hβn : ‖β‖ = ‖α‖ * D * T := by
    simp only [β, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD,
      Complex.norm_natCast]
  have hkD : ∀ x : ℝ, kD α D E T ρ w (x + y * I) = 1 - cexp (v₀ + β * x) := by
    intro x
    unfold kD
    rw [show v₀ + β * x = Complex.log w + -(α * (D * ((ρ : ℂ) + T * ((x : ℂ) + y * I)) + E)) by
      simp only [v₀, β]; ring, Complex.exp_add, Complex.exp_log hw]
  have hden' : ∀ x : ℝ, m ≤ ‖1 - cexp (v₀ + β * x)‖ := fun x => by
    rw [← hkD]; exact hden x y right_mem_uIcc
  set a := 3 * √(π / (A * α.re * T ^ 2))
  set b := 1 / m * (2 / ‖β‖ * (1 + 16 * ‖β‖ ^ 2 / (π ^ 2 * (A * α.re * T ^ 2))))
  have ha : 0 < a := by positivity
  have hb : 0 < b := by have := norm_pos_iff.mpr hβ; positivity
  obtain ⟨η, hη, hη1, hopt⟩ := opt_eta ha hb
  obtain ⟨-, hI⟩ := bad_integral_le (x0 := kx0 α A B T ρ y) hP hβ hm hη hη1 hden'
  refine (fourier_kern_le' hα hA hT hm y hden ξ).trans ?_
  gcongr
  simp_rw [hkD]
  refine hI.trans (le_trans (le_of_eq ?_) (hopt.trans (le_of_eq ?_)))
  · simp only [a, b]; field_simp
  · simp only [Jb, a, b, hβn]

/-! ### one residue class and the whole sum -/

theorem class_sum' (hα : 0 < α.re) (hA : 0 < A) (hD : 0 < D) (hT : 0 < T) (hw : w ≠ 0) {m : ℝ} (hm : 0 < m)
    {y0 : ℝ} (hy0 : 0 < y0) (hden : ∀ x y' : ℝ, |y'| ≤ y0 → m ≤ ‖kD α D E T ρ w (x + y' * I)‖) :
    HasSum (fun k : ℤ => kern α A B D E T ρ w k) (∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) l) ∧
    ‖∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) l‖ ≤
      Real.exp (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) *
        Jb α A D T m * (1 / Real.sinh (π * y0)) := by
  have hJ : 0 ≤ Jb α A D T m := by unfold Jb; positivity
  set f : ℝ → ℂ := fun x => kern α A B D E T ρ w x with hfdef
  set K0 : ℝ := A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)
  set Mc : ℝ := Real.exp K0 * Jb α A D T m
  have hlam : 0 < π * y0 := by positivity
  have hF : ∀ l : ℤ, ‖𝓕 f l‖ ≤ Mc * Real.exp (-(π * y0) * |2 * (l : ℝ) - 1|) := by
    intro l
    rcases le_or_gt 1 l with hl | hl
    · have hb := kern_sharp (B := B) hα hA hD hT hw hm (-y0) (fun x y' hy' => hden x y' (by
        have := abs_le_of_mem_uIcc0 hy'; rwa [abs_neg, abs_of_pos hy0] at this)) l
      refine hb.trans (le_of_eq ?_)
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      rw [abs_of_nonneg (by linarith)]
      simp only [Mc, K0, kC]
      rw [show A * (T * -y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) - π * -y0 +
          2 * π * l * -y0 = (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) +
          (-(π * y0) * (2 * l - 1)) by ring, Real.exp_add]
      ring
    · have hb := kern_sharp (B := B) hα hA hD hT hw hm y0 (fun x y' hy' => hden x y' (by
        have := abs_le_of_mem_uIcc0 hy'; rwa [abs_of_pos hy0] at this)) l
      refine hb.trans (le_of_eq ?_)
      have hl' : (l : ℝ) ≤ 0 := by exact_mod_cast (by omega : l ≤ 0)
      rw [abs_of_nonpos (by linarith)]
      simp only [Mc, K0, kC]
      rw [show A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) - π * y0 +
          2 * π * l * y0 = (A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) +
          (-(π * y0) * -(2 * l - 1)) by ring, Real.exp_add]
      ring
  have hsum := hasSum_odd hlam
  have hFs : Summable fun l : ℤ => 𝓕 f l :=
    Summable.of_norm_bounded (hsum.summable.mul_left Mc) hF
  refine ⟨(class_sum (B := B) hα hA hT hm hy0 hden).1, ?_⟩
  refine (tsum_of_norm_bounded (hsum.mul_left Mc) hF).trans (le_of_eq ?_)
  rw [odd_sum_eq hlam]

/-- **Key lemma, sharp form**: per-class denominator bounds `m(ρ)`. -/
theorem al_sum_le' (hα : 0 < α.re) (hA : 0 < A) (hD : 0 < D) (hT : 0 < T) {c ω : ℤ → ℂ}
    (hc : ∀ n, c (n + T) = -c n) (hc1 : ∀ n, ‖c n‖ ≤ 1) (hω : ∀ n, ω (n + T) = ω n) (hω0 : ∀ n, ω n ≠ 0)
    {m : ℤ → ℝ} {Y0 : ℝ} (hm : ∀ n, 0 < m n) (hY0 : 0 < Y0)
    (hden : ∀ n : ℤ, ∀ x y : ℝ, |y| ≤ Y0 → m n ≤ ‖1 - ω n * cexp (-(α * (D * ((x : ℂ) + y * I) + E)))‖) :
    Summable (alTerm α A B D E c ω) ∧
    ‖∑' n, alTerm α A B D E c ω n‖ ≤
      Real.exp (A * Y0 ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)) *
        (∑ ρ ∈ Finset.range T, Jb α A D T (m ρ)) * (1 / Real.sinh (π * Y0 / T)) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set y0 := Y0 / T
  have hy0 : 0 < y0 := by positivity
  have hdc : ∀ ρ : ℤ, ∀ x y' : ℝ, |y'| ≤ y0 → m ρ ≤ ‖kD α D E T ρ (ω ρ) (x + y' * I)‖ := by
    intro ρ x y' hy'
    have h := hden ρ (ρ + T * x) (T * y') (by
      rw [abs_mul, abs_of_pos hT']
      calc T * |y'| ≤ T * y0 := by gcongr
        _ = Y0 := by simp only [y0]; field_simp)
    unfold kD
    convert h using 6
    push_cast; ring
  -- the uniform bound needed for summability: the minimum of `m` over one period
  set S : ℤ → ℂ := fun ρ => ∑' l : ℤ, 𝓕 (fun x : ℝ => kern α A B D E T ρ (ω ρ) x) l
  have hcls : ∀ ρ : ℤ, HasSum (fun k : ℤ => alTerm α A B D E c ω (ρ + T * k)) (c ρ * S ρ) := by
    intro ρ
    have := ((class_sum (B := B) hα hA hT (hm ρ) hy0 (hdc ρ)).1).mul_left (c ρ)
    exact this.congr_fun fun k => alTerm_class hc hω ρ k
  set Fc : ℕ → ℤ → ℂ := fun ρ n => if n % (T : ℤ) = ρ then alTerm α A B D E c ω n else 0
  have hTz : (0 : ℤ) < T := by exact_mod_cast hT
  have hFc : ∀ ρ ∈ Finset.range T, HasSum (Fc ρ) (c ρ * S ρ) := by
    intro ρ hρ
    have hρT : (ρ : ℤ) < T := by exact_mod_cast Finset.mem_range.mp hρ
    set g : ℤ → ℤ := fun k => (ρ : ℤ) + T * k
    have hg : Function.Injective g := fun a b h => by
      simp only [g] at h
      exact (mul_right_injective₀ hTz.ne').eq_iff.mp (by linarith)
    have hmod : ∀ k, (g k) % (T : ℤ) = ρ := fun k => by
      simp only [g]; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by positivity) hρT
    refine (hg.hasSum_iff fun n hn => ?_).mp ?_
    · simp only [Fc]
      rw [if_neg]
      intro h
      apply hn
      refine ⟨n / T, ?_⟩
      simp only [g]
      have := Int.emod_add_mul_ediv n T
      rw [h] at this; exact this
    · refine (hcls ρ).congr_fun fun k => ?_
      simp only [Function.comp, Fc, hmod k, if_true]
      rfl
  have hall := hasSum_sum hFc
  have hsumF : ∀ n : ℤ, ∑ ρ ∈ Finset.range T, Fc ρ n = alTerm α A B D E c ω n := by
    intro n
    have h0 : 0 ≤ n % (T : ℤ) := Int.emod_nonneg _ hTz.ne'
    have h1 : n % (T : ℤ) < T := Int.emod_lt_of_pos _ hTz
    have hc' : ∀ ρ : ℕ, (n % (T : ℤ) = ρ) ↔ ((n % (T : ℤ)).toNat = ρ) := fun ρ => by omega
    simp only [Fc, hc']
    rw [Finset.sum_ite_eq (Finset.range T) ((n % (T : ℤ)).toNat)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hfull : HasSum (alTerm α A B D E c ω) (∑ ρ ∈ Finset.range T, c ρ * S ρ) :=
    hall.congr_fun fun n => (hsumF n).symm
  refine ⟨hfull.summable, ?_⟩
  rw [hfull.tsum_eq]
  set K0 : ℝ := A * (T * y0) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A)
  have hb : ∀ ρ ∈ Finset.range T, ‖c ρ * S ρ‖ ≤
      Real.exp K0 * Jb α A D T (m ρ) * (1 / Real.sinh (π * y0)) := by
    intro ρ _
    rw [norm_mul]
    have := (class_sum' (B := B) hα hA hD hT (hω0 ρ) (hm ρ) hy0 (hdc ρ)).2
    have hn := hc1 ρ
    calc ‖c ρ‖ * ‖S ρ‖ ≤ 1 * (Real.exp K0 * Jb α A D T (m ρ) * (1 / Real.sinh (π * y0))) := by
          gcongr
      _ = _ := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [K0, y0]
  rw [show (T : ℝ) * (Y0 / T) = Y0 by field_simp, show π * (Y0 / T) = π * Y0 / T by ring]

end

end MockCusp
