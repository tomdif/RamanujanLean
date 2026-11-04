/-
# The Appell–Lerch kernel of one residue class and its Fourier transform

For a residue class `ρ` modulo `T`, the terms `n = ρ + Tm` of an Appell–Lerch sum
`Σ c(n) e^{−α(An²+Bn)}/(1 − ω(n)e^{−α(Dn+E)})`, with the sign `(−1)^m = e^{iπm}` coming from the
anti-periodicity `c(n+T) = −c(n)`, are the values at integers `m` of the entire-up-to-poles function

  `kern(X) = e^{iπX − α(A(ρ+TX)² + B(ρ+TX))} / (1 − w e^{−α(D(ρ+TX)+E)})`.

`fourier_kern_le`: if the denominator stays `≥ m > 0` on the strip between `Im X = 0` and `Im X = y`, then
for every real `ξ`

  `|𝓕kern(ξ)| ≤ (1/m) · e^{A T² y² |α|²/Re α + B² Re α/(4A) − πy + 2πξy} · √(π/(A Re α T²))`.

This is the Mordell-integral bound: shift the Fourier integral to the line `Im X = y` (`integral_shift`) and
integrate the modulus, which is an explicit Gaussian (`re_expo`).
-/
import RamanujanTau.MockCusp.Strip

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set
open scoped Topology Real FourierTransform

noncomputable section

variable (α : ℂ) (A B D E : ℝ) (T : ℕ) (ρ : ℤ) (w : ℂ)

/-- the exponent of the numerator. -/
def kE (X : ℂ) : ℂ := π * I * X - α * (A * ((ρ : ℂ) + T * X) ^ 2 + B * ((ρ : ℂ) + T * X))

/-- the denominator. -/
def kD (X : ℂ) : ℂ := 1 - w * cexp (-(α * (D * ((ρ : ℂ) + T * X) + E)))

/-- the kernel of the residue class `ρ`. -/
def kern (X : ℂ) : ℂ := cexp (kE α A B T ρ X) / kD α D E T ρ w X

/-- the Fourier integrand. -/
def kG (ξ : ℝ) (X : ℂ) : ℂ := cexp (-(2 * π * I * X * ξ)) * kern α A B D E T ρ w X

/-- centre of the Gaussian on the line `Im X = y`. -/
def kx0 (y : ℝ) : ℝ := ((2 * A * α.im * (T * y) - B * α.re) / (2 * A * α.re) - ρ) / T

/-- constant of the Gaussian on the line `Im X = y`. -/
def kC (y : ℝ) : ℝ := A * (T * y) ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re + B ^ 2 * α.re / (4 * A) - π * y

variable {α A B D E T ρ w}

lemma re_expo (hα : α.re ≠ 0) (hA : A ≠ 0) (hT : (T : ℝ) ≠ 0) (x y : ℝ) :
    (kE α A B T ρ (x + y * I)).re = -(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2 + kC α A B T y := by
  simp only [kE, kx0, kC, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    pow_two, intCast_re, intCast_im, natCast_re, natCast_im]
  field_simp
  ring

lemma norm_phase (ξ x y : ℝ) : ‖cexp (-(2 * π * I * (x + y * I) * ξ))‖ = Real.exp (2 * π * ξ * y) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

lemma abs_le_of_mem_uIcc0 {y y' : ℝ} (h : y' ∈ uIcc 0 y) : |y'| ≤ |y| := by
  rcases le_total 0 y with hy | hy
  · rw [uIcc_of_le hy] at h
    rw [abs_of_nonneg h.1, abs_of_nonneg hy]; exact h.2
  · rw [uIcc_of_ge hy] at h
    rw [abs_of_nonpos h.2, abs_of_nonpos hy]; linarith [h.1]

/-- the Gaussian integral of the majorant. -/
lemma integral_gauss (P x0 c : ℝ) (hP : 0 < P) :
    ∫ x : ℝ, Real.exp (-P * (x - x0) ^ 2 + c) = Real.exp c * √(π / P) := by
  have h1 : (fun x : ℝ => Real.exp (-P * (x - x0) ^ 2 + c)) =
      fun x => Real.exp c * Real.exp (-P * (x - x0) ^ 2) := by
    funext x; rw [Real.exp_add, mul_comm]
  rw [h1, integral_const_mul, integral_sub_right_eq_self (fun x => Real.exp (-P * x ^ 2)) x0,
    integral_gaussian]

lemma integrable_gauss (P x0 c : ℝ) (hP : 0 < P) :
    Integrable (fun x : ℝ => Real.exp (-P * (x - x0) ^ 2 + c)) := by
  have h1 : (fun x : ℝ => Real.exp (-P * (x - x0) ^ 2 + c)) =
      fun x => Real.exp c * Real.exp (-P * (x - x0) ^ 2) := by
    funext x; rw [Real.exp_add, mul_comm]
  rw [h1]
  exact ((integrable_exp_neg_mul_sq hP).comp_sub_right x0).const_mul _

lemma kD_cont : Continuous (kD α D E T ρ w) := by unfold kD; fun_prop

lemma kE_cont : Continuous (kE α A B T ρ) := by unfold kE; fun_prop

lemma kG_differentiableAt (ξ : ℝ) {X : ℂ} (hX : kD α D E T ρ w X ≠ 0) :
    DifferentiableAt ℂ (kG α A B D E T ρ w ξ) X := by
  unfold kG kern
  have h1 : DifferentiableAt ℂ (kE α A B T ρ) X := by unfold kE; fun_prop
  have h2 : DifferentiableAt ℂ (kD α D E T ρ w) X := by unfold kD; fun_prop
  exact (by fun_prop : DifferentiableAt ℂ (fun X : ℂ => cexp (-(2 * π * I * X * ξ))) X).mul
    (h1.cexp.div h2 hX)

/-- pointwise majorant on the line `Im X = y`. -/
lemma norm_kG_le (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {m : ℝ} (hm : 0 < m) (ξ x y : ℝ)
    (hd : m ≤ ‖kD α D E T ρ w (x + y * I)‖) :
    ‖kG α A B D E T ρ w ξ (x + y * I)‖ ≤
      (1 / m) * Real.exp (-(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2 +
        (kC α A B T y + 2 * π * ξ * y)) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  set Q := -(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2 + kC α A B T y
  have hd0 : 0 < ‖kD α D E T ρ w (x + y * I)‖ := hm.trans_le hd
  have key : ‖kG α A B D E T ρ w ξ (x + y * I)‖ =
      Real.exp (2 * π * ξ * y) * Real.exp Q / ‖kD α D E T ρ w (x + y * I)‖ := by
    unfold kG kern
    rw [norm_mul, norm_div, norm_phase, Complex.norm_exp, re_expo hα.ne' hA.ne' hT']
    ring
  have hr : (1 / m) * Real.exp (-(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2 +
      (kC α A B T y + 2 * π * ξ * y)) = Real.exp (2 * π * ξ * y) * Real.exp Q / m := by
    have e : -(A * α.re * T ^ 2) * (x - kx0 α A B T ρ y) ^ 2 + (kC α A B T y + 2 * π * ξ * y) =
        2 * π * ξ * y + Q := by simp only [Q]; ring
    rw [e, Real.exp_add]; ring
  rw [key, hr]
  exact div_le_div_of_nonneg_left (by positivity) hm hd

/-- **Fourier bound for the class kernel** (Mordell-integral bound). -/
theorem fourier_kern_le (hα : 0 < α.re) (hA : 0 < A) (hT : 0 < T) {m : ℝ} (hm : 0 < m) (y : ℝ)
    (hden : ∀ x y' : ℝ, y' ∈ uIcc 0 y → m ≤ ‖kD α D E T ρ w (x + y' * I)‖) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => kern α A B D E T ρ w x) ξ‖ ≤
      (1 / m) * (Real.exp (kC α A B T y + 2 * π * ξ * y) * √(π / (A * α.re * T ^ 2))) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : 0 < A * α.re * T ^ 2 := by positivity
  set P := A * α.re * T ^ 2 with hPdef
  have hne : ∀ x y' : ℝ, y' ∈ uIcc 0 y → kD α D E T ρ w (x + y' * I) ≠ 0 := fun x y' hy' h => by
    have := hden x y' hy'; rw [h, norm_zero] at this; linarith
  -- the Fourier transform as an integral of `kG`
  have hF : 𝓕 (fun x : ℝ => kern α A B D E T ρ w x) ξ = ∫ x : ℝ, kG α A B D E T ρ w ξ x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [kG, smul_eq_mul]
    congr 2
    push_cast; ring
  -- uniform majorant on the strip
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
  -- integrability on the two lines
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
  calc ‖∫ x : ℝ, kG α A B D E T ρ w ξ (x + y * I)‖
      ≤ ∫ x : ℝ, (1 / m) * Real.exp (-P * (x - kx0 α A B T ρ y) ^ 2 + (kC α A B T y + 2 * π * ξ * y)) := by
        refine norm_integral_le_of_norm_le ((integrable_gauss P _ _ hP).const_mul _)
          (Eventually.of_forall fun x => ?_)
        have := norm_kG_le (B := B) hα hA hT hm ξ x y (hden x y hymem)
        rw [hPdef]; exact this
    _ = (1 / m) * (Real.exp (kC α A B T y + 2 * π * ξ * y) * √(π / (A * α.re * T ^ 2))) := by
        rw [integral_const_mul, integral_gauss P _ _ hP]

end

end MockCusp
