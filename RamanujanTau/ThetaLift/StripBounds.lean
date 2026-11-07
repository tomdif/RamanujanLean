import RamanujanTau.ThetaLift.KernelGen
import RamanujanTau.ThetaLift.FourierU
import RamanujanTau.ThetaLift.StripMeasure
import RamanujanTau.ThetaLift.VIntegral

/-!
# Bounds for the integrand on the strip

The Hermite theta series is dominated by Gaussians in `x` and in `g`, with constants depending on `v`
only through powers of `v`. The factor `exp(-b g²/v)` controls `v → 0`, since `g ≠ 0`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

/-- The real factor of the Hermite term. -/
def rR (lam : ℕ) (g : ℤ) (y v : ℝ) (x : ℤ) : ℝ :=
  √(3 / (π * v)) ^ lam * ev (hermite lam) ((x + 6 * g * y / v) / √(3 / (π * v)))

lemma sB_term (lam : ℕ) (y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) :
    sB z ^ lam * aeval (sA y g z x / sB z) (hermite lam) = ((rR lam g y z.im x : ℝ) : ℂ) := by
  have hc : ∀ r : ℝ, aeval (r : ℂ) (hermite lam) = ((ev (hermite lam) r : ℝ) : ℂ) := fun r =>
    Polynomial.aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℤ) r (hermite lam)
  have e : sA y g z x / sB z = (((x + 6 * g * y / z.im) / √(3 / (π * z.im)) : ℝ) : ℂ) := by
    unfold sA sB
    push_cast
    rfl
  rw [e, hc]
  unfold sB rR
  push_cast
  rfl

/-- The Hermite theta series. -/
theorem hasSum_hF (ξ y : ℝ) (lam : ℕ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun x : ℤ => sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ))
      (iteratedDeriv lam (seed ξ y g z) 0) := by
  have h := seed_iteratedDeriv ξ y g hz lam
  simpa only [sB_term] using h

/-- The Gaussian bound on the real factor. -/
lemma rR_bound (lam : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℤ) (y : ℝ) {v : ℝ} (_ : 0 < v) (x : ℤ),
    |rR lam g y v x| ≤ C * √(3 / (π * v)) ^ lam *
      Real.exp (π * v * (x : ℝ) ^ 2 / 24 + 3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * v)) := by
  obtain ⟨C, hC0, hC⟩ := ev_gauss_bound (hermite lam)
  refine ⟨C, hC0, fun g y v hv x => ?_⟩
  have hπ := Real.pi_pos
  set b := √(3 / (π * v)) with hb
  have hb2 : b ^ 2 = 3 / (π * v) := Real.sq_sqrt (by positivity)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hr := hC ((x + 6 * g * y / v) / b)
  have hsq : ((x + 6 * g * y / v) / b) ^ 2 / 16 ≤
      π * v * (x : ℝ) ^ 2 / 24 + 3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * v) := by
    rw [div_pow, hb2]
    have e : ((x : ℝ) + 6 * g * y / v) ^ 2 / (3 / (π * v)) / 16 =
        π * v * ((x : ℝ) + 6 * g * y / v) ^ 2 / 48 := by
      field_simp
      ring
    have e2 : π * v * (x : ℝ) ^ 2 / 24 + 3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * v) =
        π * v * (2 * ((x : ℝ) ^ 2 + (6 * g * y / v) ^ 2)) / 48 := by
      field_simp
      ring
    rw [e, e2]
    have h1 : ((x : ℝ) + 6 * g * y / v) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + (6 * g * y / v) ^ 2) := by
      nlinarith [sq_nonneg ((x : ℝ) - 6 * g * y / v)]
    have hc : 0 ≤ π * v / 48 := by positivity
    have := mul_le_mul_of_nonneg_left h1 hc
    calc _ = π * v / 48 * ((x : ℝ) + 6 * g * y / v) ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  unfold rR
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ lam)]
  calc _ ≤ b ^ lam * (C * Real.exp (((x + 6 * g * y / v) / b) ^ 2 / 16)) := by gcongr
    _ ≤ b ^ lam * (C * Real.exp (π * v * (x : ℝ) ^ 2 / 24 +
          3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * v))) := by gcongr
    _ = _ := by ring

/-- The norm of the exponential factor of the seed. -/
lemma norm_sv_le (ξ y : ℝ) (g : ℤ) (z : ℂ) (x : ℤ) :
    ‖sv ξ y g z x‖ ≤ Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im)) *
      (if x = 0 then 0 else Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2)) := by
  by_cases hx : x = 0
  · subst hx
    simp [sv, chiZ]
  rw [if_neg hx]
  unfold sv
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have he1 : (-(6 * π * g ^ 2 * y ^ 2 / z.im : ℂ)).re = -(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im) := by
    have : (-(6 * π * g ^ 2 * y ^ 2 / z.im : ℂ)) =
        ((-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im) : ℝ) : ℂ) := by push_cast; ring
    rw [this, ofReal_re]
  have he2 : (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ)) : ℂ).re =
      -(π * z.im / 12) * (x : ℝ) ^ 2 := by
    have : (2 * π * I * (x ^ 2 * z / 24 + x * (g * ξ)) : ℂ) =
        I * ((2 * π * (x ^ 2 / 24) : ℝ) : ℂ) * z + I * ((2 * π * (x * (g * ξ)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this]
    simp only [add_re, mul_re, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im, mul_im]
    ring
  rw [he1, he2]
  have hχ : ‖(chiZ x : ℂ)‖ ≤ 1 := by
    have := chiZ_abs_le x
    simpa [Complex.norm_intCast] using this
  have hp1 := Real.exp_pos (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im))
  have hp2 := Real.exp_pos (-(π * z.im / 12) * (x : ℝ) ^ 2)
  calc _ ≤ Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im)) * 1 *
        Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

/-- The bound on a term of the Hermite theta series. -/
lemma norm_term_le (lam : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ y : ℝ) (g : ℤ) {z : ℂ} (_ : 0 < z.im) (x : ℤ),
    ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖ ≤
      C * √(3 / (π * z.im)) ^ lam * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im)) *
        (if x = 0 then 0 else Real.exp (-(π * z.im / 24) * (x : ℝ) ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := rR_bound lam
  refine ⟨C, hC0, fun ξ y g z hz x => ?_⟩
  have hb := hC g y hz x
  have hs := norm_sv_le ξ y g z x
  have hπ := Real.pi_pos
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : x = 0
  · subst hx
    simp only [if_true] at hs ⊢
    have h0 : ‖sv ξ y g z 0‖ = 0 := by
      have := norm_nonneg (sv ξ y g z 0)
      simp only [mul_zero] at hs
      linarith
    simp [h0]
  rw [if_neg hx] at hs ⊢
  have hr0 : 0 ≤ C * √(3 / (π * z.im)) ^ lam := by positivity
  calc _ ≤ (Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im)) *
        Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2)) *
        (C * √(3 / (π * z.im)) ^ lam * Real.exp (π * z.im * (x : ℝ) ^ 2 / 24 +
          3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * z.im))) := by gcongr
    _ = _ := by
      have e : -(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im) + -(π * z.im / 24) * (x : ℝ) ^ 2 =
          -(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im) + -(π * z.im / 12) * (x : ℝ) ^ 2 +
            (π * z.im * (x : ℝ) ^ 2 / 24 + 3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * z.im)) := by
        field_simp
        ring
      have e2 := congrArg Real.exp e
      rw [Real.exp_add, Real.exp_add, Real.exp_add] at e2
      calc _ = C * √(3 / (π * z.im)) ^ lam * (Real.exp (-(6 * π * (g : ℝ) ^ 2 * y ^ 2 / z.im)) *
            Real.exp (-(π * z.im / 12) * (x : ℝ) ^ 2) * Real.exp (π * z.im * (x : ℝ) ^ 2 / 24 +
              3 * π * (g : ℝ) ^ 2 * y ^ 2 / (2 * z.im))) := by ring
        _ = _ := by rw [← e2]; ring

/-- The bound on the Hermite theta series. -/
theorem norm_hF_le (lam : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ y : ℝ) (g : ℤ) {z : ℂ} (_ : 0 < z.im),
    (∑' x : ℤ, ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖) ≤
      C * √(3 / (π * z.im)) ^ lam * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im)) *
        (48 / (π * z.im)) ∧
    Summable fun x : ℤ => ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_term_le lam
  refine ⟨C, hC0, fun ξ y g z hz => ?_⟩
  have hπ := Real.pi_pos
  have ha : 0 < π * z.im / 24 := by positivity
  obtain ⟨hS, hb⟩ := gauss_ne_zero_bound ha
  set K := C * √(3 / (π * z.im)) ^ lam * Real.exp (-(9 * π * y ^ 2 / 2 * (g : ℝ) ^ 2 / z.im)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hle : ∀ x : ℤ, ‖sv ξ y g z x * ((rR lam g y z.im x : ℝ) : ℂ)‖ ≤
      K * (if x = 0 then 0 else Real.exp (-(π * z.im / 24) * (x : ℝ) ^ 2)) := fun x => hC ξ y g hz x
  have hSK := hS.mul_left K
  have hS2 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSK
  refine ⟨?_, hS2⟩
  calc _ ≤ ∑' x : ℤ, K * (if x = 0 then 0 else Real.exp (-(π * z.im / 24) * (x : ℝ) ^ 2)) :=
        hS2.tsum_le_tsum hle hSK
    _ = K * ∑' x : ℤ, (if x = 0 then 0 else Real.exp (-(π * z.im / 24) * (x : ℝ) ^ 2)) := tsum_mul_left
    _ ≤ K * (2 / (π * z.im / 24)) := by gcongr
    _ = _ := by
      congr 1
      field_simp
      norm_num

/-- The measurable structure of the point map. -/
lemma measurable_ofComplex' : Measurable (ofComplex : ℂ → ℍ) := by
  refine measurable_of_restrict_of_restrict_compl (s := {z : ℂ | 0 < z.im})
    (measurableSet_lt measurable_const Complex.continuous_im.measurable) ?_ ?_
  · refine (measurableEmbedding_coe.measurable_comp_iff).mp ?_
    have : UpperHalfPlane.coe ∘ ({z : ℂ | 0 < z.im}.restrict ofComplex) = Subtype.val := by
      funext z
      simp [ofComplex_apply_of_im_pos z.2]
    rw [this]
    exact measurable_subtype_coe
  · have : ({z : ℂ | 0 < z.im}ᶜ.restrict ofComplex) = fun _ => ofComplex 0 := by
      funext z
      have hz : z.1.im ≤ 0 := not_lt.mp z.2
      simp only [Set.restrict_apply]
      rw [ofComplex_apply_of_im_nonpos hz, ofComplex_apply_of_im_nonpos (by simp)]
    rw [this]
    exact measurable_const

lemma measurable_pt : Measurable pt := by
  unfold pt
  refine measurable_ofComplex'.comp ?_
  fun_prop

end

end RamanujanTau.ThetaLift
