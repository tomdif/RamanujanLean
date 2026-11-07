/-
# The lattice theta function `Θ(z,t)` and its functional equation

For `z ∈ ℍ` and `t > 0` put

    Θ(z,t) = ∑_{(a,c) ∈ ℤ²} exp(−π t |a − c z|² / Im z).

Two applications of the one-dimensional Poisson summation formula for a shifted Gaussian
(Mathlib's `Complex.tsum_exp_neg_quadratic`) give

    Θ(z, 1/t) = t · Θ(z, t)                                   (`theta_inv`).

This is the two-dimensional Poisson summation formula for the unimodular lattice `ℤ + zℤ`
(scaled by `Im z^{-1/2}`).
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergFE

open Real Complex Filter Topology
open UpperHalfPlane hiding I

/-! ### One-dimensional Gaussian sums -/

/-- `n ↦ exp(−π c n²)` is summable over `ℤ` for `c > 0`. -/
lemma summable_gauss {c : ℝ} (hc : 0 < c) : Summable fun n : ℤ => Real.exp (-π * c * n ^ 2) := by
  have h := ((summable_jacobiTheta₂_term_iff 0 ((c : ℂ) * I)).2 (by simpa using hc)).norm
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term]
  congr 1
  simp; ring

/-- The shifted Gaussian `n ↦ exp(−π u (n − w)²)` is summable over `ℤ` for `u > 0`. -/
lemma summable_gauss_shift {u : ℝ} (hu : 0 < u) (w : ℝ) :
    Summable fun n : ℤ => Real.exp (-π * u * (n - w) ^ 2) := by
  have h := ((summable_jacobiTheta₂_term_iff (-((u * w : ℝ) : ℂ) * I) ((u : ℂ) * I)).2
    (by simpa using hu)).norm.mul_left (Real.exp (-π * u * w ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp; ring

/-- **Poisson summation for a shifted Gaussian** (real form): for `u > 0`,
`∑ₙ exp(−π u (n − w)²) = u^{-1/2} ∑ₖ exp(−π k²/u) cos(2π k w)`. -/
theorem tsum_gauss_shift {u : ℝ} (hu : 0 < u) (w : ℝ) :
    ∑' n : ℤ, Real.exp (-π * u * (n - w) ^ 2) =
      1 / Real.sqrt u * ∑' k : ℤ, Real.exp (-π / u * k ^ 2) * Real.cos (2 * π * k * w) := by
  have hu' : 0 < ((u : ℂ)).re := by simpa using hu
  have P := Complex.tsum_exp_neg_quadratic hu' ((u * w : ℝ) : ℂ)
  -- multiply both sides by `exp(−π u w²)`
  have P2 := congrArg (fun X => Complex.exp (-(π * u * w ^ 2 : ℝ)) * X) P
  simp only at P2
  rw [← tsum_mul_left, ← mul_left_comm, ← tsum_mul_left] at P2
  have hL : ∀ n : ℤ, Complex.exp (-(π * u * w ^ 2 : ℝ)) *
      Complex.exp (-π * u * n ^ 2 + 2 * π * ((u * w : ℝ) : ℂ) * n) =
      ((Real.exp (-π * u * (n - w) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hR : ∀ n : ℤ, Complex.exp (-(π * u * w ^ 2 : ℝ)) *
      Complex.exp (-π / u * (n + I * ((u * w : ℝ) : ℂ)) ^ 2) =
      ((Real.exp (-π / u * n ^ 2) : ℝ) : ℂ) * Complex.exp (-(2 * π * n * w : ℝ) * I) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    congr 1
    have hI : I ^ 2 = -1 := Complex.I_sq
    have hinv : (u : ℂ) * (u : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hu0
    push_cast
    rw [div_eq_mul_inv]
    linear_combination (-(π * w ^ 2 * u * u * (u : ℂ)⁻¹)) * hI + (π * w ^ 2 * u - 2 * π * w * n * I) * hinv
  simp_rw [hL, hR] at P2
  -- take real parts
  have hsR : Summable fun n : ℤ =>
      ((Real.exp (-π / u * n ^ 2) : ℝ) : ℂ) * Complex.exp (-(2 * π * n * w : ℝ) * I) := by
    refine Summable.of_norm_bounded (summable_gauss (c := 1 / u) (by positivity)) fun n => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq; congr 1; ring
  have hre := congrArg Complex.re P2
  rw [← Complex.ofReal_tsum, Complex.ofReal_re] at hre
  rw [hre]
  have hsqrt : ((u : ℂ) ^ (1 / 2 : ℂ)) = ((Real.sqrt u : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]; push_cast; rfl
  rw [hsqrt, show (1 : ℂ) / ((Real.sqrt u : ℝ) : ℂ) = ((1 / Real.sqrt u : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_tsum hsR]
  congr 1
  refine tsum_congr fun k => ?_
  rw [Complex.re_ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-! ### The lattice theta function -/

/-- The quadratic form `Q_z(a,c) = |a − c z|² / Im z = (a − c x)²/y + c² y`. -/
noncomputable def lq (z : ℍ) (p : ℤ × ℤ) : ℝ :=
  ((p.1 : ℝ) - p.2 * z.re) ^ 2 / z.im + (p.2 : ℝ) ^ 2 * z.im

lemma lq_nonneg (z : ℍ) (p : ℤ × ℤ) : 0 ≤ lq z p := by
  unfold lq; have := z.im_pos; positivity

/-- `a² + c² ≤ K_z · Q_z(a,c)` with `K_z = 2y + (2x²+1)/y`. -/
lemma sq_add_sq_le_lq (z : ℍ) (p : ℤ × ℤ) :
    ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ (2 * z.im + (2 * z.re ^ 2 + 1) / z.im) * lq z p := by
  have hy := z.im_pos
  set a : ℝ := (p.1 : ℝ); set c : ℝ := (p.2 : ℝ); set x := z.re; set y := z.im
  have h1 : a ^ 2 ≤ 2 * (a - c * x) ^ 2 + 2 * c ^ 2 * x ^ 2 := by nlinarith [sq_nonneg (a - 2 * c * x)]
  have e : (2 * y + (2 * x ^ 2 + 1) / y) * ((a - c * x) ^ 2 / y + c ^ 2 * y) =
      2 * (a - c * x) ^ 2 + (2 * x ^ 2 + 1) * c ^ 2 +
        (2 * y ^ 2 * c ^ 2 + (2 * x ^ 2 + 1) * (a - c * x) ^ 2 / y ^ 2) := by
    field_simp; ring
  unfold lq
  rw [e]
  have : 0 ≤ 2 * y ^ 2 * c ^ 2 + (2 * x ^ 2 + 1) * (a - c * x) ^ 2 / y ^ 2 := by positivity
  nlinarith

lemma Kz_pos (z : ℍ) : 0 < 2 * z.im + (2 * z.re ^ 2 + 1) / z.im := by
  have := z.im_pos; positivity

/-- The summand `exp(−π t Q_z(a,c))`. -/
noncomputable def thetaTerm (z : ℍ) (t : ℝ) (p : ℤ × ℤ) : ℝ := Real.exp (-π * t * lq z p)

lemma thetaTerm_pos (z : ℍ) (t : ℝ) (p : ℤ × ℤ) : 0 < thetaTerm z t p := Real.exp_pos _

lemma summable_thetaTerm (z : ℍ) {t : ℝ} (ht : 0 < t) : Summable (thetaTerm z t) := by
  set K := 2 * z.im + (2 * z.re ^ 2 + 1) / z.im
  have hK : 0 < K := Kz_pos z
  have hs := (summable_gauss (c := t / K) (by positivity)).mul_of_nonneg
    (summable_gauss (c := t / K) (by positivity)) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun p => (thetaTerm_pos z t p).le) (fun p => ?_) hs
  rw [thetaTerm, ← Real.exp_add, Real.exp_le_exp]
  have h := sq_add_sq_le_lq z p
  have : t / K * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ t * lq z p := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]; nlinarith
  nlinarith [Real.pi_pos]

/-- **The lattice theta function** `Θ(z,t) = ∑_{(a,c) ∈ ℤ²} exp(−π t |a − c z|²/Im z)`. -/
noncomputable def Theta (z : ℍ) (t : ℝ) : ℝ := ∑' p : ℤ × ℤ, thetaTerm z t p

lemma thetaTerm_split (z : ℍ) (t : ℝ) (p : ℤ × ℤ) :
    thetaTerm z t p = Real.exp (-π * (t * z.im) * (p.2 : ℝ) ^ 2) *
      Real.exp (-π * (t / z.im) * ((p.1 : ℝ) - p.2 * z.re) ^ 2) := by
  rw [thetaTerm, ← Real.exp_add, lq]; congr 1; ring

/-- `Θ(z,t) = ∑_c ∑_a exp(−π t Q_z(a,c))`. -/
lemma Theta_eq_iter (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Theta z t = ∑' c : ℤ, ∑' a : ℤ, thetaTerm z t (a, c) := by
  have hs := summable_thetaTerm z ht
  rw [Theta, ← (Equiv.prodComm ℤ ℤ).symm.tsum_eq]
  refine (hs.comp_injective (Equiv.prodComm ℤ ℤ).symm.injective).tsum_prod' (fun c => ?_)
  have hy := z.im_pos
  refine ((summable_gauss_shift (u := t / z.im) (by positivity) (c * z.re)).mul_left
    (Real.exp (-π * (t * z.im) * (c : ℝ) ^ 2))).congr fun a => ?_
  simp only [Function.comp, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [thetaTerm_split]

/-- **Functional equation of the lattice theta function** (two-dimensional Poisson summation):
`Θ(z, 1/t) = t Θ(z, t)` for `t > 0`. -/
theorem theta_inv (z : ℍ) {t : ℝ} (ht : 0 < t) : Theta z (1 / t) = t * Theta z t := by
  have hy := z.im_pos
  set x := z.re; set y := z.im
  -- Step 1–2: Poisson in `a`.
  have step1 : Theta z t = 1 / Real.sqrt (t / y) * ∑' c : ℤ, ∑' k : ℤ,
      Real.exp (-π * (t * y) * (c : ℝ) ^ 2) *
        (Real.exp (-π / (t / y) * (k : ℝ) ^ 2) * Real.cos (2 * π * k * (c * x))) := by
    rw [Theta_eq_iter z ht, ← tsum_mul_left]
    refine tsum_congr fun c => ?_
    simp_rw [thetaTerm_split]
    rw [tsum_mul_left, tsum_gauss_shift (by positivity : 0 < t / y), tsum_mul_left]
    ring
  -- Step 3: swap.
  have hF : Summable (Function.uncurry fun (c k : ℤ) =>
      Real.exp (-π * (t * y) * (c : ℝ) ^ 2) *
        (Real.exp (-π / (t / y) * (k : ℝ) ^ 2) * Real.cos (2 * π * k * (c * x)))) := by
    have hs := (summable_gauss (c := t * y) (by positivity)).mul_of_nonneg
      (summable_gauss (c := 1 / (t / y)) (by positivity)) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
    refine Summable.of_norm_bounded hs fun ⟨c, k⟩ => ?_
    simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc]
    refine mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _) |>.trans (le_of_eq ?_)
    congr 2; ring
  have step2 : Theta z t = 1 / Real.sqrt (t / y) * ∑' k : ℤ,
      Real.exp (-π / (t / y) * (k : ℝ) ^ 2) * ∑' c : ℤ,
        Real.exp (-π * (t * y) * (c : ℝ) ^ 2) * Real.cos (2 * π * c * (k * x)) := by
    rw [step1, ← hF.tsum_comm']
    · congr 1
      refine tsum_congr fun k => ?_
      rw [← tsum_mul_left]
      refine tsum_congr fun c => ?_
      rw [show 2 * π * (k : ℝ) * (c * x) = 2 * π * c * (k * x) by ring]
      ring
    · exact fun c => hF.prod_factor c
    · exact fun k => hF.prod_symm.prod_factor k
  -- Step 4: Poisson in `c` (read backwards).
  have step3 : ∀ k : ℤ, ∑' c : ℤ, Real.exp (-π * (t * y) * (c : ℝ) ^ 2) *
      Real.cos (2 * π * c * (k * x)) =
      Real.sqrt (1 / (t * y)) * ∑' n : ℤ, Real.exp (-π * (1 / (t * y)) * ((n : ℝ) - k * x) ^ 2) := by
    intro k
    have hu : 0 < 1 / (t * y) := by positivity
    rw [tsum_gauss_shift hu, ← mul_assoc (Real.sqrt _), mul_one_div_cancel (Real.sqrt_pos.2 hu).ne',
      one_mul]
    refine tsum_congr fun c => ?_
    congr 2
    field_simp
  rw [Theta_eq_iter z (by positivity : 0 < 1 / t), step2]
  simp_rw [step3]
  have hc : t * (1 / Real.sqrt (t / y)) * Real.sqrt (1 / (t * y)) = 1 := by
    rw [Real.sqrt_div' 1 (by positivity : 0 ≤ t * y), Real.sqrt_one]
    have h1 : 0 < Real.sqrt (t / y) := Real.sqrt_pos.2 (by positivity)
    have h2 : 0 < Real.sqrt (t * y) := Real.sqrt_pos.2 (by positivity)
    have : Real.sqrt (t / y) * Real.sqrt (t * y) = t := by
      rw [← Real.sqrt_mul (by positivity), show t / y * (t * y) = t * t by field_simp,
        Real.sqrt_mul_self ht.le]
    field_simp
    linarith
  rw [← mul_assoc, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have e1 : -π / (t / y) * (k : ℝ) ^ 2 = -π * (1 / t * y) * (k : ℝ) ^ 2 := by field_simp
  have e2 : ∀ n : ℤ, -π * (1 / (t * y)) * ((n : ℝ) - k * x) ^ 2 =
      -π * (1 / t / y) * ((n : ℝ) - k * x) ^ 2 := fun n => by field_simp
  simp_rw [e1, e2]
  calc ∑' a : ℤ, thetaTerm z (1 / t) (a, k)
      = ∑' n : ℤ, (t * (1 / Real.sqrt (t / y)) * Real.sqrt (1 / (t * y))) *
          (Real.exp (-π * (1 / t * y) * (k : ℝ) ^ 2) *
            Real.exp (-π * (1 / t / y) * ((n : ℝ) - k * x) ^ 2)) := by
        refine tsum_congr fun n => ?_
        rw [hc, one_mul, thetaTerm_split]
    _ = _ := by
        rw [tsum_mul_left, tsum_mul_left]
        ring

end RamanujanTau.RankinSelbergFE
