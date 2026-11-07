/-
# Weighted Parseval and the weighted asymptotic for a cusp form of weight `k = 2p + 2`

For `f ∈ S_k(SL₂(ℤ))`, `k = 2p+2`, `0 ≤ β < π/2`:

    ∫ |Λ(f, k/2+it)|² e^{2βt} dt = 2π ∫_ℝ |e^{(k/2)w} f(i e^w)|² du,    w = u + iβ
                                                                    (`weighted_parseval_f`)

(Plancherel `CriticalMeanSquare.parseval` for `F(t) = Λ(f,k/2+it)e^{βt}`, whose Fourier
transform is `Φ(2πξ+iβ) = 2π G(2πξ+iβ)` by `HardyZerosGeneral.Phi_eq_strip`; integrability via
`|Φ(−w)| = |Φ(w)|` (root number `i^k`) and the majorant `CriticalMeanSquare.maj`).
Then the abstract ray asymptotic (`Ray.ray_tendsto`, with `D = f` and the horocycle limit
`RankinSelbergGeneral.horocycle_tendsto`) on both rays gives

    κ^k ∫ |Λ(f,k/2+it)|² e^{2βt} dt / log(1/κ) → 12 ‖f‖²,   κ = cot β → 0⁺
                                                              (`weighted_asymptotic_f`).
-/
import RamanujanTau.GeneralCuspMoments.Ray
import RamanujanTau.HardyZerosGeneral.Cusp
import RamanujanTau.CriticalMeanSquare.Parseval

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex ModularForm MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
open scoped MatrixGroups Real FourierTransform

variable {p : ℕ}

lemma half_k (p : ℕ) : ((2 * p + 2 : ℕ) : ℝ) / 2 = (p : ℝ) + 1 := by push_cast; ring

/-- **Cusp bound** `|f(z)| (Im z)^{p+1} ≤ M e^{−π Im z}` on all of `ℍ`. -/
lemma exists_cusp_bound (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ z : ℂ, 0 < z.im → ‖Fc f z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)) := by
  obtain ⟨G, hG0, hG⟩ := RankinSelbergGeneral.exists_Gf_le f
  obtain ⟨A, Y, hA, hY, hcusp⟩ := cusp_bound f
  set B := Real.sqrt G with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨A * ((p + 1).factorial : ℝ) + B * Real.exp (π * Y), by positivity, fun z hz => ?_⟩
  rw [Fc_of_im_pos f hz]
  set q : ℍ := ⟨z, hz⟩ with hq
  have him : q.im = z.im := rfl
  set y := z.im with hy
  have hfB : ‖f q‖ * y ^ (p + 1) ≤ B := by
    rw [hB]
    apply Real.le_sqrt_of_sq_le
    have h := hG q
    unfold RankinSelbergGeneral.Gf at h
    rw [him] at h
    calc (‖f q‖ * y ^ (p + 1)) ^ 2 = ‖f q‖ ^ 2 * y ^ (2 * p + 2) := by ring
      _ ≤ G := by exact_mod_cast h
  have hE : Real.exp (π * y) * Real.exp (-(π * y)) = 1 := by rw [← Real.exp_add]; simp
  rcases le_or_gt Y y with hYy | hYy
  · have hc := hcusp q (by rw [him]; exact hYy)
    rw [him] at hc
    have hpow : y ^ (p + 1) ≤ ((p + 1).factorial : ℝ) * Real.exp (π * y) := by
      have h1 := Real.pow_div_factorial_le_exp y hz.le (p + 1)
      have h2 : Real.exp y ≤ Real.exp (π * y) := Real.exp_le_exp.mpr (by
        nlinarith [Real.pi_gt_three])
      rw [div_le_iff₀ (by positivity)] at h1
      nlinarith [Real.exp_pos y]
    have he2 : Real.exp (-(2 * π) * y) * Real.exp (π * y) = Real.exp (-(π * y)) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖f q‖ * y ^ (p + 1) ≤ (A * Real.exp (-(2 * π) * y)) *
          (((p + 1).factorial : ℝ) * Real.exp (π * y)) := by gcongr
      _ = A * ((p + 1).factorial : ℝ) * (Real.exp (-(2 * π) * y) * Real.exp (π * y)) := by ring
      _ = A * ((p + 1).factorial : ℝ) * Real.exp (-(π * y)) := by rw [he2]
      _ ≤ _ := by
        have : 0 ≤ B * Real.exp (π * Y) * Real.exp (-(π * y)) := by positivity
        nlinarith [Real.exp_pos (-(π * y))]
  · have h1 : 1 ≤ Real.exp (π * Y) * Real.exp (-(π * y)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [Real.pi_pos]
    calc ‖f q‖ * y ^ (p + 1) ≤ B := hfB
      _ ≤ B * (Real.exp (π * Y) * Real.exp (-(π * y))) := le_mul_of_one_le_right hB0 h1
      _ ≤ _ := by
        have : 0 ≤ A * ((p + 1).factorial : ℝ) * Real.exp (-(π * y)) := by positivity
        nlinarith

/-! ### Evenness of `Φ` up to the root number -/

lemma Phi_neg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (w : ℂ) :
    Phi f (-w) = I ^ (2 * p + 2) * Phi f w := by
  unfold Phi
  rw [← integral_neg_eq_self, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [Zc_neg f (by omega)]
  have e : -((((-t : ℝ)) : ℂ) * I * -w) = -((t : ℂ) * I * w) := by push_cast; ring
  rw [e]; ring

lemma norm_Phi_neg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (w : ℂ) :
    ‖Phi f (-w)‖ = ‖Phi f w‖ := by
  rw [Phi_neg, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]

lemma norm_two_pi_C : ‖(2 * π : ℂ)‖ = 2 * π := by
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma norm_Gc_eq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {w : ℂ}
    (hw : w ∈ strip) : ‖Gc f w‖ = ‖Phi f w‖ / (2 * π) := by
  rw [Phi_eq_strip f hk hw, norm_mul, norm_two_pi_C]
  field_simp

/-- `‖G(u+iβ)‖ ≤ M c^{−(p+1)} e^{−π c e^u}`, `c = cos β`. -/
lemma norm_Gc_le (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {M : ℝ}
    (hM : ∀ z : ℂ, 0 < z.im → ‖Fc f z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    {u β : ℝ} (hβ : |β| < π / 2) :
    ‖Gc f ((u : ℂ) + β * I)‖ ≤
      M / Real.cos β ^ (p + 1) * Real.exp (-(π * Real.cos β * Real.exp u)) := by
  set w : ℂ := (u : ℂ) + β * I with hwdef
  have hwim : w.im = β := by simp [hwdef]
  have hwre : w.re = u := by simp [hwdef]
  have hw : w ∈ strip := by show |w.im| < π / 2; rw [hwim]; exact hβ
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le β], by linarith [le_abs_self β]⟩
  have hz := im_exp_mul_I_pos hw
  have e : (cexp w * I).im = Real.exp u * Real.cos β := by
    rw [← hwre, ← hwim]; simp [Complex.exp_re]
  have h := hM _ hz
  rw [e] at h
  rw [Gc, norm_mul, Complex.norm_exp]
  have hre : ((((2 * p + 2 : ℕ) : ℝ) / 2 : ℝ) * w : ℂ).re = ((p : ℝ) + 1) * u := by
    rw [half_k]; rw [hwdef]; simp
  rw [hre]
  set Dn := ‖Fc f (cexp w * I)‖ with hDn
  set v := Real.exp u * Real.cos β with hv
  have hvpos : 0 < v := by positivity
  have hE1 : Real.exp (((p : ℝ) + 1) * u) = Real.exp u ^ (p + 1) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hcos : 0 < Real.cos β ^ (p + 1) := by positivity
  rw [hE1, div_mul_eq_mul_div, le_div_iff₀ hcos]
  calc Real.exp u ^ (p + 1) * Dn * Real.cos β ^ (p + 1) = Dn * v ^ (p + 1) := by
        rw [hv, mul_pow]; ring
    _ ≤ M * Real.exp (-(π * v)) := h
    _ = M * Real.exp (-(π * Real.cos β * Real.exp u)) := by rw [hv]; ring_nf

/-- The Fourier-side density `ξ ↦ Φ(−2πξ + iβ)`. -/
noncomputable def gF (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β ξ : ℝ) : ℂ :=
  Phi f (((-2 * π * ξ : ℝ) : ℂ) + β * I)

lemma norm_gF_le (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, 0 < z.im → ‖Fc f z‖ * z.im ^ (p + 1) ≤ M * Real.exp (-(π * z.im)))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) (ξ : ℝ) :
    ‖gF f β ξ‖ ≤ 2 * π * (M / Real.cos β ^ (p + 1)) *
      min (Real.exp (-(π * Real.cos β * Real.exp (-2 * π * ξ))))
        (Real.exp (-(π * Real.cos β * Real.exp (2 * π * ξ)))) := by
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have hβabs' : |-β| < π / 2 := by rw [abs_neg]; exact hβabs
  have hs1 : (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hs2 : (((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) ∈ strip := by
    show |(((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I).im| < π / 2; simpa using hβabs
  have hK0 : 0 ≤ 2 * π * (M / Real.cos β ^ (p + 1)) := by
    have := Real.cos_pos_of_mem_Ioo (x := β) ⟨by linarith [Real.pi_pos], hβ⟩
    positivity
  rw [mul_min_of_nonneg _ _ hK0]
  refine le_min ?_ ?_
  · rw [gF, Phi_eq_strip f hk hs1, norm_mul, norm_two_pi_C]
    have hG := norm_Gc_le f hM (u := -2 * π * ξ) hβabs
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  · have e : (((-2 * π * ξ : ℝ) : ℂ) + β * I) =
        -(((2 * π * ξ : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) := by push_cast; ring
    rw [gF, e, norm_Phi_neg, Phi_eq_strip f hk hs2, norm_mul, norm_two_pi_C]
    have hG := norm_Gc_le f hM (u := 2 * π * ξ) hβabs'
    rw [Real.cos_neg] at hG
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith

lemma continuous_gF (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Continuous (gF f β) := by
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have hstrip : ∀ ξ : ℝ, (((-2 * π * ξ : ℝ) : ℂ) + β * I) ∈ strip := by
    intro ξ; show |(((-2 * π * ξ : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβabs
  unfold gF
  exact (differentiableOn_Phi f hk).continuousOn.comp_continuous (by fun_prop) hstrip

lemma integrable_gF (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (gF f β) := by
  obtain ⟨M, hM0, hM⟩ := exists_cusp_bound f
  have hc0 : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  refine ((RamanujanTau.CriticalMeanSquare.integrable_maj (Real.cos β)).const_mul
    (2 * π * (M / Real.cos β ^ (p + 1)))).mono' (continuous_gF f hk hβ0 hβ).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  refine (norm_gF_le f hk hM0 hM hβ0 hβ ξ).trans ?_
  have : 0 ≤ 2 * π * (M / Real.cos β ^ (p + 1)) := by positivity
  exact mul_le_mul_of_nonneg_left (RamanujanTau.CriticalMeanSquare.min_le_maj hc0 ξ) this

/-! ### Plancherel -/

/-- `F(t) = Λ(f, k/2+it) e^{βt}`. -/
noncomputable def Ff (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β t : ℝ) : ℂ := Zc f t * cexp (β * t)

lemma continuous_Ff (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β : ℝ) : Continuous (Ff f β) :=
  (continuous_Zc f (by omega)).mul (by fun_prop)

lemma integrable_Ff (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (Ff f β) := by
  refine (integrable_heckeLambda_line f hk hβ).mono' (continuous_Ff f β).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Ff, norm_mul, Complex.norm_exp]
  have e : (((β : ℂ) * (t : ℂ))).re = β * t := by simp
  rw [e]
  change ‖Zc f t‖ * _ ≤ ‖Zc f t‖ * (1 + |t|) * Real.exp (β * |t|)
  have h1 : ‖Zc f t‖ ≤ ‖Zc f t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  have h2 : Real.exp (β * t) ≤ Real.exp (β * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hβ0)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

lemma fourier_Ff (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β ξ : ℝ) :
    𝓕 (Ff f β) ξ = Phi f (((2 * π * ξ : ℝ) : ℂ) + β * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Phi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Ff, smul_eq_mul]
  rw [mul_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- The ray integrand `|G(u+iβ)|²`. -/
noncomputable def Ru (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β u : ℝ) : ℝ :=
  ‖Gc f ((u : ℂ) + β * I)‖ ^ 2

lemma Ru_nonneg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β u : ℝ) : 0 ≤ Ru f β u := by
  unfold Ru; positivity

/-- **Exact weighted Parseval identity for `f`.** -/
theorem weighted_parseval_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ t : ℝ, ‖heckeLambda f (sc (2 * p + 2) t)‖ ^ 2 * Real.exp (2 * β * t) =
      2 * π * ∫ u : ℝ, Ru f β u := by
  have hgi := integrable_gF f hk hβ0 hβ
  have hFi : Integrable (𝓕 (Ff f β)) := by
    have : 𝓕 (Ff f β) = fun ξ => gF f β (-ξ) := by
      funext ξ; rw [fourier_Ff, gF]; congr 3; ring
    rw [this]; exact hgi.comp_neg
  have hP := RamanujanTau.CriticalMeanSquare.parseval (continuous_Ff f β)
    (integrable_Ff f hk hβ0 hβ) hFi
  have hL : ∀ t : ℝ, ‖Ff f β t‖ ^ 2 =
      ‖heckeLambda f (sc (2 * p + 2) t)‖ ^ 2 * Real.exp (2 * β * t) := by
    intro t
    have e : (((β : ℂ) * (t : ℂ))).re = β * t := by simp
    rw [Ff, Zc, norm_mul, Complex.norm_exp, mul_pow, e, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  simp only [hL] at hP
  rw [← hP]
  have hstrip : ∀ u : ℝ, ((u : ℂ) + β * I) ∈ strip := by
    have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
    intro u; show |((u : ℂ) + β * I).im| < π / 2; simpa using hβabs
  have hR : ∀ ξ : ℝ, ‖𝓕 (Ff f β) ξ‖ ^ 2 = 4 * π ^ 2 * Ru f β (2 * π * ξ) := by
    intro ξ
    rw [fourier_Ff, Phi_eq_strip f hk (hstrip _), norm_mul, mul_pow, Ru, norm_two_pi_C]
    ring
  simp only [hR]
  rw [integral_const_mul, Measure.integral_comp_mul_left (Ru f β) (2 * π), smul_eq_mul]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  field_simp
  ring

/-- `Ru β` is integrable. -/
lemma integrable_Ru (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (Ru f β) := by
  obtain ⟨M, hM0, hM⟩ := exists_cusp_bound f
  have hc0 : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  set Bd : ℝ := 2 * π * (M / Real.cos β ^ (p + 1)) * 7 with hBd
  have hbd : ∀ ξ, ‖gF f β ξ‖ ≤ Bd := by
    intro ξ
    refine (norm_gF_le f hk hM0 hM hβ0 hβ ξ).trans ?_
    rw [hBd]
    have : 0 ≤ 2 * π * (M / Real.cos β ^ (p + 1)) := by positivity
    exact mul_le_mul_of_nonneg_left ((RamanujanTau.CriticalMeanSquare.min_le_maj hc0 ξ).trans
      (RamanujanTau.CriticalMeanSquare.maj_le_seven _ _)) this
  set R : ℝ := -1 / (2 * π) with hR
  have hR0 : R ≠ 0 := by rw [hR]; have := Real.pi_pos; positivity
  have hgi := (integrable_gF f hk hβ0 hβ).comp_mul_left' hR0
  have heq : Ru f β = fun u => ‖gF f β (R * u)‖ ^ 2 / (2 * π) ^ 2 := by
    funext u
    have hu : ((-2 * π * (R * u) : ℝ) : ℂ) = (u : ℂ) := by
      congr 1; rw [hR]; field_simp
    have hstrip : ((u : ℂ) + β * I) ∈ strip := by
      show |((u : ℂ) + β * I).im| < π / 2; simpa using hβabs
    rw [gF, hu, Phi_eq_strip f hk hstrip, Ru, norm_mul, mul_pow, norm_two_pi_C]
    have hπ : (2 * π) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [heq]
  refine (hgi.norm.const_mul (Bd / (2 * π) ^ 2)).mono'
    (((hgi.aestronglyMeasurable.aemeasurable.norm).pow_const 2).div_const _).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  have h1 := hbd (R * u)
  have h0 := norm_nonneg (gF f β (R * u))
  rw [div_le_iff₀ (by positivity)]
  have : ‖gF f β (R * u)‖ ^ 2 ≤ Bd * ‖gF f β (R * u)‖ := by nlinarith
  calc ‖gF f β (R * u)‖ ^ 2 ≤ Bd * ‖gF f β (R * u)‖ := this
    _ = Bd / (2 * π) ^ 2 * ‖gF f β (R * u)‖ * (2 * π) ^ 2 := by field_simp

/-- **Evenness** up to `β ↦ −β`. -/
lemma Ru_even (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ : |β| < π / 2) (u : ℝ) : Ru f β (-u) = Ru f (-β) u := by
  have h1 : (((-u : ℝ) : ℂ) + β * I) ∈ strip := by
    show |(((-u : ℝ) : ℂ) + β * I).im| < π / 2; simpa using hβ
  have h2 : (((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) ∈ strip := by
    show |(((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I).im| < π / 2; simpa using hβ
  unfold Ru
  rw [norm_Gc_eq f hk h1, norm_Gc_eq f hk h2]
  have e : (((-u : ℝ) : ℂ) + β * I) = -(((u : ℝ) : ℂ) + ((-β : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [e, norm_Phi_neg]

lemma integral_Ru_split (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    ∫ u, Ru f β u = (∫ u in Ioi 0, Ru f β u) + ∫ u in Ioi 0, Ru f (-β) u := by
  have hi := integrable_Ru f hk hβ0 hβ
  have habs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have h1 : ∫ u in Iic 0, Ru f β u = ∫ u in Ioi 0, Ru f (-β) u := by
    have e : ∀ u, Ru f β u = Ru f (-β) (-u) := fun u => by
      rw [← Ru_even f hk habs, neg_neg]
    simp_rw [e]
    rw [integral_comp_neg_Iic, neg_zero]
  rw [h1, add_comm]

lemma integrable_Ru_neg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (Ru f (-β)) := by
  have habs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  have e : Ru f (-β) = fun u => Ru f β (-u) := funext fun u => (Ru_even f hk habs u).symm
  rw [e]
  exact (integrable_Ru f hk hβ0 hβ).comp_neg

/-! ### The two rays -/

lemma ray_point_pos (β u : ℝ) (hs : 0 < Real.sin β) :
    cexp ((u : ℂ) + (β : ℂ) * I) * I =
      pz (-1 * (Real.sin β * Real.exp u)) (Real.cos β / Real.sin β * (Real.sin β * Real.exp u)) := by
  rw [Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  unfold pz
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    field_simp
    ring

lemma ray_point_neg (β u : ℝ) (hs : 0 < Real.sin β) :
    cexp ((u : ℂ) + ((-β : ℝ) : ℂ) * I) * I =
      pz (1 * (Real.sin β * Real.exp u)) (Real.cos β / Real.sin β * (Real.sin β * Real.exp u)) := by
  rw [Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  unfold pz
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    field_simp
    ring

lemma Ru_eq_gen (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {β' σ s κ : ℝ} (hs : 0 < s)
    (hpt : ∀ u : ℝ, cexp ((u : ℂ) + (β' : ℂ) * I) * I = pz (σ * (s * Real.exp u)) (κ * (s * Real.exp u)))
    (u : ℝ) : Ru f β' u =
      Gsig p (Fc f) σ κ (s * Real.exp u) / s ^ (2 * p + 2) * (s * Real.exp u) := by
  unfold Ru Gsig Gc
  rw [hpt u, norm_mul, mul_pow, Complex.norm_exp]
  have hre : ((((2 * p + 2 : ℕ) : ℝ) / 2 : ℝ) * ((u : ℂ) + β' * I) : ℂ).re = ((p : ℝ) + 1) * u := by
    rw [half_k]; simp
  rw [hre]
  have he : Real.exp (((p : ℝ) + 1) * u) ^ 2 = Real.exp u ^ (2 * p + 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]
  have hu := Real.exp_pos u
  have hs' : s ^ (2 * p + 2) = s ^ (2 * p + 1) * s := pow_succ s (2 * p + 1)
  have he' : Real.exp u ^ (2 * p + 2) = Real.exp u ^ (2 * p + 1) * Real.exp u :=
    pow_succ _ (2 * p + 1)
  rw [hs', he', mul_pow]
  field_simp

/-! ### The ray hypotheses for `D = f` -/

lemma hD_eq_horoMean (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {y : ℝ} (hy : 0 < y) :
    hD p (Fc f) y = RankinSelbergGeneral.horoMean f y := by
  unfold hD HhD RankinSelbergGeneral.horoMean
  rw [dif_pos hy, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [RankinSelbergGeneral.Gf]
  have him : 0 < (pz x y).im := by rw [pz_im]; exact hy
  rw [Fc_of_im_pos f him, RankinSelberg.hp_im hy x]
  have : (⟨pz x y, him⟩ : ℍ) = RankinSelberg.hp hy x := rfl
  rw [this]; push_cast; ring

/-- The horocycle constant `c₀ = (3/π)‖f‖²`. -/
noncomputable def c0f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) : ℝ :=
  3 / π * RankinSelbergGeneral.petNormSqF f

lemma rayHyp_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) : RayHyp p (Fc f) (c0f f) where
  diff := Fc_differentiableOn f
  per := Fc_add_one f
  bound := exists_cusp_bound f
  horo := by
    refine (RankinSelbergGeneral.horocycle_tendsto f).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hD_eq_horoMean f hy).symm

/-- **The weighted asymptotic for `f`.** As `β → π/2⁻`, with `κ = cot β`,
`κ^k ∫ |Λ(f,k/2+it)|² e^{2βt} dt / log(1/κ) → 12‖f‖²`. -/
theorem weighted_asymptotic_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    Tendsto (fun β => (Real.cos β / Real.sin β) ^ (2 * p + 2) *
      (∫ t : ℝ, ‖heckeLambda f (sc (2 * p + 2) t)‖ ^ 2 * Real.exp (2 * β * t)) /
        Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2))
      (𝓝 (12 * RankinSelbergGeneral.petNormSqF f)) := by
  have hR := rayHyp_f f
  have hp : Tendsto (fun β => (Real.cos β / Real.sin β) ^ (2 * p + 2) * (∫ u in Ioi 0, Ru f β u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 (c0f f)) :=
    ray_tendsto hR (σ := -1) (Or.inr rfl) (R := Ru f)
      (fun β hs u => Ru_eq_gen f hs (ray_point_pos β · hs) u)
      (fun β hβ0 hβ => integrable_Ru f hk hβ0.le hβ)
  have hn : Tendsto (fun β => (Real.cos β / Real.sin β) ^ (2 * p + 2) *
      (∫ u in Ioi 0, Ru f (-β) u) /
      Real.log (1 / (Real.cos β / Real.sin β))) (𝓝[<] (π / 2)) (𝓝 (c0f f)) :=
    ray_tendsto hR (σ := 1) (Or.inl rfl) (R := fun β => Ru f (-β))
      (fun β hs u => Ru_eq_gen f hs (ray_point_neg β · hs) u)
      (fun β hβ0 hβ => integrable_Ru_neg f hk hβ0.le hβ)
  have hsum := ((hp.add hn).const_mul (2 * π))
  have hc : 2 * π * (c0f f + c0f f) = 12 * RankinSelbergGeneral.petNormSqF f := by
    unfold c0f; field_simp; ring
  rw [hc] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show 0 < π / 2 by positivity)] with β hβ
  rw [weighted_parseval_f f hk hβ.1.le hβ.2, integral_Ru_split f hk hβ.1.le hβ.2]
  ring

end RamanujanTau.GeneralCuspMoments
