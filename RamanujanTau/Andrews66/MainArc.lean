/-
# Andrews 1966, the `k = 1` term: exact evaluation of the major-arc main term

Dragonette's circle method (`RamanujanTau/Dragonette/`) reduces `α(n)` to the major-arc integral
`∫_{−t}^{t} M(θ) dθ`, `M(θ) = (z/π)^{−1/2} e^{π²/(24z) − z/24 + nz}`, `z = t + iθ`, and evaluates it only
asymptotically (Laplace's method). Here it is evaluated **exactly up to an error `O(e^{3A/2})`**, where
`e^{2A} = e^{π√(n/6)}` is the size of the main term:

* substitute `ζ = a/z` (`a = π²/24`): `M(θ) dθ = i√(πa) · h(ζ) dζ` with `h(ζ) = ζ^{−3/2} e^{ζ + Y/ζ}`,
  `Y = a(n − 1/24)`; the segment `Re z = t, |θ| ≤ t` becomes an arc of the circle `|ζ − A/2| = A/2`;
* the arc is replaced by its chord `Re ζ = A/2` (a primitive of `h` on a disc, `DifferentiableOn.isExactOn_ball`);
* the chord is completed to the full line `Re ζ = A/2`; on the two tails `|h| ≤ |v|^{−3/2} e^{3A/2}`;
* the full line integral is the order-3/2 Bessel integral (`Andrews66.bessel_line`), in closed form
  `2π · 2 sinh(x)/(√π x)`, `x = 2√Y = π√(24n−1)/12` (`Andrews66.tsum_bco`).

The result is `∫_{−t}^{t} M = 2π · √24/√(24n−1) · sinh(π√(24n−1)/12) + O(e^{3A/2}/√A)`, i.e. exactly Andrews'
`k = 1` term `π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/12)`.
-/
import RamanujanTau.Andrews66.Bessel
import RamanujanTau.Dragonette.Main
import RamanujanTau.Rademacher.Chord

set_option autoImplicit false

namespace Andrews66
open Complex Filter Metric MeasureTheory Set intervalIntegral HardyRamanujan
open scoped Real Topology

noncomputable section

/-- `a = π²/24`. -/
def aa : ℝ := π ^ 2 / 24

lemma aa_pos : 0 < aa := by unfold aa; positivity

/-- `Y = a(n − 1/24) = π²(24n − 1)/576`. -/
def YY (n : ℕ) : ℝ := aa * ((n : ℝ) - 1 / 24)

/-- the Bessel integrand `h(ζ) = ζ^{−3/2} e^{ζ + Y/ζ}`. -/
def hfun (Y : ℝ) (ζ : ℂ) : ℂ := ζ ^ (-(3 / 2 : ℂ)) * cexp (ζ + Y / ζ)

/-- the arc `ζ(θ) = a/(t + iθ)`. -/
def zeta (t θ : ℝ) : ℂ := (aa : ℂ) / zt t θ

lemma hasDerivAt_zeta {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    HasDerivAt (zeta t) (-(aa : ℂ) * I / zt t θ ^ 2) θ := by
  have hz : ∀ θ : ℝ, zt t θ ≠ 0 := fun θ => zt_ne_zero ht
  have h1 : HasDerivAt (fun θ : ℝ => (t : ℂ) + θ * I) I θ := by
    have := ((hasDerivAt_id (θ : ℂ)).comp_ofReal).mul_const I
    have h2 := this.const_add (t : ℂ)
    simpa using h2
  have h3 := (hasDerivAt_inv (hz θ)).comp θ h1
  have h4 := h3.const_mul (aa : ℂ)
  convert h4 using 1
  ring

lemma arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ π := by
  intro h
  have := Complex.arg_eq_pi_iff.mp h
  linarith [this.1]

lemma sqrt_cexp {x : ℝ} (hx : 0 < x) : ((√x : ℝ) : ℂ) = cexp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
  push_cast; ring_nf

/-- **the substitution `ζ = a/z`**: `M(θ) = i√(πa) · h(ζ(θ)) ζ'(θ)`. -/
lemma MD_eq (n : ℕ) {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    Dragonette.MD n t θ =
      (I * ((√(π * aa) : ℝ) : ℂ)) * (hfun (YY n) (zeta t θ) * (-(aa : ℂ) * I / zt t θ ^ 2)) := by
  set z := zt t θ with hzdef
  have hz0 : z ≠ 0 := zt_ne_zero ht
  have hzre : 0 < z.re := by simp [hzdef, zt]; exact ht
  have ha := aa_pos
  have hLz : z = cexp (log z) := (exp_log hz0).symm
  have hLa : ((aa : ℝ) : ℂ) = cexp (Real.log aa) := by rw [← ofReal_exp, Real.exp_log ha]
  have hlogζ : log ((aa : ℂ) / z) = Real.log aa - log z := by
    rw [div_eq_mul_inv, log_ofReal_mul ha (inv_ne_zero hz0), log_inv _ (arg_ne_pi_of_re_pos hzre)]
    ring
  have hlogzπ : log (z / π) = log z - Real.log π := by
    rw [div_eq_mul_inv, mul_comm, show ((π : ℂ))⁻¹ = ((π⁻¹ : ℝ) : ℂ) by push_cast; ring,
      log_ofReal_mul (inv_pos.mpr Real.pi_pos) hz0, Real.log_inv]
    push_cast; ring
  have hζ0 : (aa : ℂ) / z ≠ 0 := div_ne_zero (by exact_mod_cast ha.ne') hz0
  have hsq : ((√(π * aa) : ℝ) : ℂ) = cexp ((Real.log π + Real.log aa) / 2) := by
    rw [sqrt_cexp (by positivity), Real.log_mul Real.pi_ne_zero ha.ne']; push_cast; ring
  -- exponents
  have hE : (π : ℂ) ^ 2 / (24 * z) - z / 24 + n * z = (aa : ℂ) / z + (YY n : ℂ) / ((aa : ℂ) / z) := by
    unfold YY aa; push_cast; field_simp; ring
  have hR : (-(aa : ℂ) * I / z ^ 2) = -I * cexp (Real.log aa - 2 * log z) := by
    rw [Complex.exp_sub, ← hLa, show (2 : ℂ) * log z = log z + log z by ring, Complex.exp_add, ← hLz]
    field_simp
  unfold Dragonette.MD hfun zeta
  rw [← hzdef, hR, cpow_def_of_ne_zero hζ0, hlogζ, hlogzπ, hsq, mul_assoc (cexp _) (cexp _) (cexp (n * z)),
    ← Complex.exp_add, show π ^ 2 / (24 * z) - z / 24 + n * z = (π : ℂ) ^ 2 / (24 * z) - z / 24 + n * z by rfl]
  rw [show (π : ℂ) ^ 2 / (24 * z) - z / 24 + ↑n * z = π ^ 2 / (24 * z) - z / 24 + n * z by rfl] at hE
  rw [hE]
  have e : I * cexp ((Real.log π + Real.log aa) / 2) *
      (cexp ((Real.log aa - log z) * -(3 / 2)) * cexp ((aa : ℂ) / z + (YY n : ℂ) / ((aa : ℂ) / z)) *
        (-I * cexp (Real.log aa - 2 * log z))) =
      (I * -I) * cexp ((Real.log π + Real.log aa) / 2 + (Real.log aa - log z) * -(3 / 2) +
        (Real.log aa - 2 * log z) + ((aa : ℂ) / z + (YY n : ℂ) / ((aa : ℂ) / z))) := by
    set P : ℂ := (Real.log π + Real.log aa) / 2
    set Q : ℂ := (Real.log aa - log z) * -(3 / 2)
    set R : ℂ := (aa : ℂ) / z + (YY n : ℂ) / ((aa : ℂ) / z)
    set S : ℂ := Real.log aa - 2 * log z
    conv_rhs => rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
    ring
  rw [e, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul, ← Complex.exp_add]
  congr 1
  ring

/-! ### arc → chord -/

lemma zeta_re (t θ : ℝ) : (zeta t θ).re = aa * t / (t ^ 2 + θ ^ 2) := re_div_zt aa t θ

lemma zeta_im (t θ : ℝ) : (zeta t θ).im = -(aa * θ) / (t ^ 2 + θ ^ 2) := by
  unfold zeta; rw [div_im, normSq_zt]; simp [zt]; ring

/-- the disc `|ζ − 3A/4| < 3A/5`, `A = a/t`. -/
lemma zeta_mem {t : ℝ} (ht : 0 < t) {θ : ℝ} (hθ : |θ| ≤ t) :
    zeta t θ ∈ ball (((3 / 4) * (aa / t) : ℝ) : ℂ) ((3 / 5) * (aa / t)) := by
  have ha := aa_pos
  have hD : 0 < t ^ 2 + θ ^ 2 := by positivity
  have hθ2 : θ ^ 2 ≤ t ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  rw [mem_ball, dist_eq_norm]
  have hr : 0 < (3 / 5) * (aa / t) := by positivity
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, zeta_re, zeta_im]
  -- `= a²(9/(16t²) − 1/(2D))`
  have e : (aa * t / (t ^ 2 + θ ^ 2) - 3 / 4 * (aa / t)) * (aa * t / (t ^ 2 + θ ^ 2) - 3 / 4 * (aa / t)) +
      -(aa * θ) / (t ^ 2 + θ ^ 2) * (-(aa * θ) / (t ^ 2 + θ ^ 2)) =
      aa ^ 2 * (9 / (16 * t ^ 2) - 1 / (2 * (t ^ 2 + θ ^ 2))) := by
    field_simp; ring
  rw [e]
  have h1 : 1 / (4 * t ^ 2) ≤ 1 / (2 * (t ^ 2 + θ ^ 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : aa ^ 2 * (9 / (16 * t ^ 2) - 1 / (4 * t ^ 2)) < ((3 / 5) * (aa / t)) ^ 2 := by
    have : 0 < aa ^ 2 / t ^ 2 := by positivity
    have e2 : aa ^ 2 * (9 / (16 * t ^ 2) - 1 / (4 * t ^ 2)) = (5 / 16) * (aa ^ 2 / t ^ 2) := by
      field_simp; ring
    rw [e2, show ((3 : ℝ) / 5 * (aa / t)) ^ 2 = 9 / 25 * (aa ^ 2 / t ^ 2) by rw [mul_pow, div_pow aa t]; norm_num]
    linarith
  have h3 : aa ^ 2 * (9 / (16 * t ^ 2) - 1 / (2 * (t ^ 2 + θ ^ 2))) ≤
      aa ^ 2 * (9 / (16 * t ^ 2) - 1 / (4 * t ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  linarith

lemma chord_mem {t c : ℝ} (ht : 0 < t) (hc : c = aa / (2 * t)) {v : ℝ} (hv : |v| ≤ c) :
    (c : ℂ) + v * I ∈ ball (((3 / 4) * (aa / t) : ℝ) : ℂ) ((3 / 5) * (aa / t)) := by
  have ha := aa_pos
  rw [mem_ball, dist_eq_norm]
  have hr : 0 < (3 / 5) * (aa / t) := by positivity
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
    sub_im, add_im, mul_im, zero_add, add_zero]
  have hv2 : v ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have e : (c - 3 / 4 * (aa / t)) * (c - 3 / 4 * (aa / t)) = (1 / 16) * (aa / t) ^ 2 := by
    rw [hc]; field_simp; ring
  have e2 : c ^ 2 = (1 / 4) * (aa / t) ^ 2 := by rw [hc]; field_simp; ring
  have : 0 < (aa / t) ^ 2 := by positivity
  rw [e]; nlinarith

lemma re_pos_of_mem {t : ℝ} (ht : 0 < t) {ζ : ℂ} (hζ : ζ ∈ ball (((3 / 4) * (aa / t) : ℝ) : ℂ) ((3 / 5) * (aa / t))) :
    0 < ζ.re := by
  rw [mem_ball, dist_eq_norm] at hζ
  have h := Complex.abs_re_le_norm (ζ - (((3 / 4) * (aa / t) : ℝ) : ℂ))
  rw [sub_re, ofReal_re] at h
  have : 0 < aa / t := div_pos aa_pos ht
  have := neg_abs_le (ζ.re - 3 / 4 * (aa / t))
  linarith

lemma differentiableAt_hfun (Y : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) : DifferentiableAt ℂ (hfun Y) ζ := by
  have hne : ζ ≠ 0 := fun h => by rw [h] at hζ; simp at hζ
  have hs : ζ ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hζ)
  unfold hfun
  refine DifferentiableAt.mul ?_ ?_
  · exact differentiableAt_id.cpow (differentiableAt_const _) hs
  · exact (differentiableAt_id.add ((differentiableAt_const _).div differentiableAt_id hne)).cexp

/-- **arc → chord**: `∫_{−t}^{t} M(θ) dθ = √(πa) ∫_{−c}^{c} h(c + iv) dv`, `c = a/(2t)`. -/
theorem major_chord (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ θ in (-t)..t, Dragonette.MD n t θ =
      ((√(π * aa) : ℝ) : ℂ) * ∫ v in (-(aa / (2 * t)))..(aa / (2 * t)),
        hfun (YY n) (((aa / (2 * t) : ℝ) : ℂ) + v * I) := by
  set U := ball (((3 / 4) * (aa / t) : ℝ) : ℂ) ((3 / 5) * (aa / t))
  set c := aa / (2 * t) with hc
  have ha := aa_pos
  have hc0 : 0 < c := by positivity
  have hdiff : DifferentiableOn ℂ (hfun (YY n)) U := fun ζ hζ =>
    (differentiableAt_hfun _ (re_pos_of_mem ht hζ)).differentiableWithinAt
  obtain ⟨P, hP⟩ := hdiff.isExactOn_ball
  -- the arc
  have hMc := Dragonette.MD_cont n ht
  have hK : (I * ((√(π * aa) : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne')
  have h1 : ∫ θ in (-t)..t, hfun (YY n) (zeta t θ) * (-(aa : ℂ) * I / zt t θ ^ 2) =
      P (zeta t t) - P (zeta t (-t)) := by
    refine Rademacher.integral_eq_of_primitive hP (by linarith) (hasDerivAt_zeta ht) (fun θ hθ => ?_) ?_
    · exact zeta_mem ht (abs_le.mpr ⟨hθ.1, hθ.2⟩)
    · have : (fun θ => hfun (YY n) (zeta t θ) * (-(aa : ℂ) * I / zt t θ ^ 2)) =
          fun θ => Dragonette.MD n t θ / (I * ((√(π * aa) : ℝ) : ℂ)) := by
        have hs0 : ((√(π * aa) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
        funext θ; rw [MD_eq n ht θ]; field_simp
      rw [this]; exact (hMc.div_const _).continuousOn
  -- the chord
  have hγ : ∀ v : ℝ, HasDerivAt (fun v : ℝ => ((c : ℝ) : ℂ) + v * I) I v := by
    intro v
    have := ((hasDerivAt_id (v : ℂ)).comp_ofReal).mul_const I
    simpa using this.const_add ((c : ℝ) : ℂ)
  have h2 : ∫ v in (-c)..c, hfun (YY n) (((c : ℝ) : ℂ) + v * I) * I =
      P ((c : ℂ) + (c : ℂ) * I) - P ((c : ℂ) + ((-c : ℝ) : ℂ) * I) := by
    refine Rademacher.integral_eq_of_primitive (γ := fun v : ℝ => ((c : ℝ) : ℂ) + v * I) hP (by linarith) hγ
      (fun v hv => chord_mem ht hc (abs_le.mpr ⟨hv.1, hv.2⟩)) ?_
    refine ContinuousOn.mul (fun v _ => ?_) continuousOn_const
    refine ((differentiableAt_hfun _ ?_).continuousAt.comp (by fun_prop : Continuous fun v : ℝ =>
      ((c : ℝ) : ℂ) + v * I).continuousAt).continuousWithinAt
    simpa using hc0
  have hct : (c : ℂ) * t = aa / 2 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [hc]; push_cast; field_simp
  have hz1 : zeta t t = (c : ℂ) + ((-c : ℝ) : ℂ) * I := by
    have h2 : (t : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    unfold zeta zt
    rw [div_eq_iff h2]; push_cast
    linear_combination ((c : ℂ) * t) * I_sq - 2 * hct
  have hz2 : zeta t (-t) = (c : ℂ) + (c : ℂ) * I := by
    have h2 : (t : ℂ) + ((-t : ℝ) : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    unfold zeta zt
    rw [div_eq_iff h2]; push_cast
    linear_combination ((c : ℂ) * t) * I_sq - 2 * hct
  have hM : ∫ θ in (-t)..t, Dragonette.MD n t θ = (I * ((√(π * aa) : ℝ) : ℂ)) *
      ∫ θ in (-t)..t, hfun (YY n) (zeta t θ) * (-(aa : ℂ) * I / zt t θ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => MD_eq n ht θ
  rw [hM, h1, hz1, hz2]
  rw [intervalIntegral.integral_mul_const] at h2
  have h3 : P ((c : ℂ) + ((-c : ℝ) : ℂ) * I) - P ((c : ℂ) + (c : ℂ) * I) =
      -((∫ v in (-c)..c, hfun (YY n) (((c : ℝ) : ℂ) + v * I)) * I) := by rw [h2]; ring
  rw [h3]
  ring_nf
  rw [I_sq]; ring

end

end Andrews66
