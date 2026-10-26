/-
# Ramanujan's value of the Rogers–Ramanujan continued fraction at `q = e^{−2π}`

From Ramanujan's first letter to Hardy (16 January 1913):

  `R(e^{−2π}) = √((5+√5)/2) − (√5+1)/2`,   `R(q) = q^{1/5} (q;q⁵)_∞(q⁴;q⁵)_∞ / ((q²;q⁵)_∞(q³;q⁵)_∞)`.

(`R(q)` is the product side of the continued fraction `q^{1/5}/(1 + q/(1 + q²/(1 + ⋯)))`; see
`RRContinuedFraction` for the formal identity.)

Proof.
* **Formal**: the 5-dissection of Euler's product (`qfacInf_dissection`) with `α = v/u`, `β = u/v`
  (`J5_relations`) gives, in `x = q^{1/5}`,
  `(x;x)_∞ · u(x⁵) v(x⁵) = (x²⁵;x²⁵)_∞ (v(x⁵)² − x u(x⁵)v(x⁵) − x² u(x⁵)²)`, i.e.
  `1/R − 1 − R = (x;x)_∞/(x (x²⁵;x²⁵)_∞) = η(τ/5)/η(5τ)`.
* **Analytic**: the formal identity is a numerical one for `|x| < 1` (`Realize`), and Mathlib's transformation
  `η(−1/z) = √z η(z)/√i` at `z = 5i` gives `η(i/5) = √5 η(5i)`, i.e. `1/R − 1 − R = √5` at `q = e^{−2π}`.
* `R > 0` picks the positive root of `R² + (1+√5)R − 1 = 0`.
-/
import RamanujanTau.Realize
import RamanujanTau.RamanujanR5
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option autoImplicit false

namespace RRValue
open Complex Filter Metric Realize
open MockTheta5.JTP (qfacInf eQ alphaQ betaQ E5 qfacInf_dissection)
open RankProof (Pinf)
open scoped Real

/-! ### the formal identity -/

lemma E5_Pinf (b : ℕ) (hb : 1 ≤ b) : E5 (Pinf b 5) = Pinf (5 * b) 25 :=
  RankProof.Ea_Pinf 5 b 5 (by norm_num) hb (by norm_num)

/-- `(x;x)_∞ · u(x⁵) v(x⁵) = (x²⁵;x²⁵)_∞ (v(x⁵)² − x u(x⁵) v(x⁵) − x² u(x⁵)²)`. -/
theorem rr_formal :
    Pinf 1 1 * (Pinf 5 25 * Pinf 20 25) * (Pinf 10 25 * Pinf 15 25)
      = Pinf 25 25 * ((Pinf 10 25 * Pinf 15 25) ^ 2 - PowerSeries.X * (Pinf 5 25 * Pinf 20 25) * (Pinf 10 25 * Pinf 15 25)
        - PowerSeries.X ^ 2 * (Pinf 5 25 * Pinf 20 25) ^ 2) := by
  have hJ := CrankProof.J5_relations.2
  have hJ' := CrankProof.betaQ_eq
  simp only [CrankProof.Jab, show (5 : ℕ) - 2 = 3 from rfl, show (5 : ℕ) - 1 = 4 from rfl] at hJ hJ'
  have hP5 : IsUnit (Pinf 5 5) := by
    rw [RankProof.Pinf_aa 5 (by norm_num)]
    exact MockTheta5.JTP.isUnit_qfacInf.map _
  have hv : Pinf 2 5 * Pinf 3 5 = alphaQ * (Pinf 1 5 * Pinf 4 5) := by
    apply hP5.mul_right_cancel; linear_combination hJ
  have hu : Pinf 1 5 * Pinf 4 5 = betaQ * (Pinf 2 5 * Pinf 3 5) := by
    apply hP5.mul_right_cancel; linear_combination hJ'
  have hv5 := congrArg E5 hv
  have hu5 := congrArg E5 hu
  simp only [map_mul, E5_Pinf 1 le_rfl, E5_Pinf 2 (by norm_num), E5_Pinf 3 (by norm_num),
    E5_Pinf 4 (by norm_num)] at hv5 hu5
  norm_num at hv5 hu5
  have he : E5 eQ = Pinf 25 25 := by
    rw [show eQ = Pinf 5 5 from (RankProof.Pinf_aa 5 (by norm_num)).symm, E5_Pinf 5 (by norm_num)]
  have hq : qfacInf = Pinf 1 1 := RankProof.Pinf_one_one.symm
  have hD := qfacInf_dissection
  rw [he, hq] at hD
  rw [hD]
  linear_combination (-(Pinf 25 25) * (Pinf 10 25 * Pinf 15 25)) * hv5
    + (Pinf 25 25 * PowerSeries.X ^ 2 * (Pinf 5 25 * Pinf 20 25)) * hu5

/-! ### real positivity of the products -/

lemma Pfun_real (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    ∃ r : ℝ, 0 < r ∧ Pfun b a (y : ℂ) = r := by
  set g : ℕ → ℝ := fun n => -y ^ (b + a * n)
  have hgs : Summable g := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one h0 h1) fun n => ?_
    simp only [g, norm_neg, norm_pow, Real.norm_eq_abs, abs_of_nonneg h0]
    exact pow_le_pow_of_le_one h0 h1.le (by nlinarith)
  have hpos : ∀ n, 0 < 1 + g n := fun n => by
    have : y ^ (b + a * n) < 1 := pow_lt_one₀ h0 h1 (by omega)
    simp only [g]; linarith
  have hlog := Real.summable_log_one_add_of_summable hgs
  have hP := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  refine ⟨rexp (∑' i, Real.log (1 + g i)), Real.exp_pos _, ?_⟩
  have hC := hP.map Complex.ofRealHom Complex.continuous_ofReal
  rw [Pfun]
  convert hC.tprod_eq using 2 with n
  simp [g, sub_eq_add_neg]

lemma Pfun_pow (b a c : ℕ) (z : ℂ) : Pfun b a (z ^ c) = Pfun (c * b) (c * a) z := by
  simp only [Pfun, ← pow_mul]
  congr 1; funext n; congr 2; ring

/-! ### the point `x = e^{−2π/5}` -/

/-- `x = q^{1/5}` with `q = e^{−2π}`. -/
noncomputable def xr : ℝ := Real.exp (-(2 * π / 5))

lemma xr_pos : 0 < xr := Real.exp_pos _

lemma xr_lt_one : xr < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; linarith)

lemma x_mem : ((xr : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos xr_pos]; exact xr_lt_one

lemma cexp_x : cexp (-(2 * π / 5 : ℂ)) = (xr : ℂ) := by
  rw [xr, Complex.ofReal_exp]; push_cast; ring_nf

/-- **`η(i/5) = √5 η(5i)`**, in product form: `(x;x)_∞ = √5 · x · (x²⁵;x²⁵)_∞`. -/
lemma eta_step : Pfun 1 1 (xr : ℂ) = (Real.sqrt 5 : ℂ) * (xr : ℂ) * Pfun 25 25 (xr : ℂ) := by
  have hmem : (5 * I : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    show 0 < (5 * I : ℂ).im; simp
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hmem
  simp only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have h15 : (-1 : ℂ) / (5 * I) = I / 5 := by
    rw [div_eq_div_iff (by simp) (by norm_num)]; ring_nf; rw [I_sq]; ring
  rw [h15] at h
  simp only [ModularForm.eta, ModularForm.eta_q_eq_pow, Function.Periodic.qParam] at h
  push_cast at h
  have e1 : cexp (2 * π * I * (I / 5)) = (xr : ℂ) := by
    rw [← cexp_x]; congr 1; ring_nf; rw [I_sq]; ring
  have e2 : cexp (2 * π * I * (5 * I)) = (xr : ℂ) ^ 25 := by
    rw [← cexp_x, ← Complex.exp_nat_mul]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  have e3 : cexp (2 * π * I * (I / 5) / 24) = cexp (-(π / 60 : ℂ)) := by
    congr 1; ring_nf; rw [I_sq]; ring
  have e4 : cexp (2 * π * I * (5 * I) / 24) = cexp (-(π / 60 : ℂ)) * (xr : ℂ) := by
    rw [← cexp_x, ← Complex.exp_add]; congr 1; ring_nf; rw [I_sq]; ring
  have p1 : (∏' n : ℕ, (1 - (xr : ℂ) ^ (n + 1))) = Pfun 1 1 (xr : ℂ) := by
    rw [Pfun]; congr 1; funext n; congr 2; ring
  have p2 : (∏' n : ℕ, (1 - ((xr : ℂ) ^ 25) ^ (n + 1))) = Pfun 25 25 (xr : ℂ) := by
    rw [Pfun]; congr 1; funext n; rw [← pow_mul]; congr 2; ring
  rw [e1, e2, e3, e4, p1, p2] at h
  have hs5 : Complex.sqrt (5 * I) = (Real.sqrt 5 : ℂ) * Complex.sqrt I := by
    rw [_root_.sqrt_eq_exp (by simp), _root_.sqrt_eq_exp I_ne_zero,
      show (5 * I : ℂ) = ((5 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.log_ofReal_mul (by norm_num) I_ne_zero, add_div, Complex.exp_add]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp]
    push_cast; ring_nf
  rw [hs5] at h
  have hI : Complex.sqrt I ≠ 0 := by rw [_root_.sqrt_eq_exp I_ne_zero]; exact Complex.exp_ne_zero _
  have hE : cexp (-(π / 60 : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ hE
  rw [h]; field_simp

/-! ### assembling -/

lemma realizes_lhs : Realizes (fun z => Pfun 1 1 z * (Pfun 5 25 z * Pfun 20 25 z) * (Pfun 10 25 z * Pfun 15 25 z))
    (Pinf 1 1 * (Pinf 5 25 * Pinf 20 25) * (Pinf 10 25 * Pinf 15 25)) :=
  ((realizes_Pinf 1 1 le_rfl le_rfl).mul ((realizes_Pinf 5 25 (by norm_num) (by norm_num)).mul
    (realizes_Pinf 20 25 (by norm_num) (by norm_num)))).mul
    ((realizes_Pinf 10 25 (by norm_num) (by norm_num)).mul (realizes_Pinf 15 25 (by norm_num) (by norm_num)))

lemma realizes_rhs : Realizes (fun z => Pfun 25 25 z * ((Pfun 10 25 z * Pfun 15 25 z) ^ 2
      - z * (Pfun 5 25 z * Pfun 20 25 z) * (Pfun 10 25 z * Pfun 15 25 z) - z ^ 2 * (Pfun 5 25 z * Pfun 20 25 z) ^ 2))
    (Pinf 25 25 * ((Pinf 10 25 * Pinf 15 25) ^ 2 - PowerSeries.X * (Pinf 5 25 * Pinf 20 25) * (Pinf 10 25 * Pinf 15 25)
        - PowerSeries.X ^ 2 * (Pinf 5 25 * Pinf 20 25) ^ 2)) := by
  have hu := (realizes_Pinf 5 25 (by norm_num) (by norm_num)).mul (realizes_Pinf 20 25 (by norm_num) (by norm_num))
  have hv := (realizes_Pinf 10 25 (by norm_num) (by norm_num)).mul (realizes_Pinf 15 25 (by norm_num) (by norm_num))
  exact (realizes_Pinf 25 25 (by norm_num) (by norm_num)).mul
    (((hv.pow 2).sub ((realizes_X.mul hu).mul hv)).sub ((realizes_X.pow 2).mul (hu.pow 2)))

/-- **Ramanujan (1913)**: `R(e^{−2π}) = √((5+√5)/2) − (√5+1)/2`, where
`R(q) = q^{1/5}(q;q⁵)_∞(q⁴;q⁵)_∞/((q²;q⁵)_∞(q³;q⁵)_∞)` and `q^{1/5} = e^{−2π/5}`. -/
theorem rogers_ramanujan_value :
    (Real.exp (-(2 * π / 5)) : ℂ) * Pfun 1 5 (Real.exp (-(2 * π))) * Pfun 4 5 (Real.exp (-(2 * π)))
      / (Pfun 2 5 (Real.exp (-(2 * π))) * Pfun 3 5 (Real.exp (-(2 * π))))
      = ((Real.sqrt ((5 + Real.sqrt 5) / 2) - (1 + Real.sqrt 5) / 2 : ℝ) : ℂ) := by
  have hq : ((Real.exp (-(2 * π)) : ℝ) : ℂ) = (xr : ℂ) ^ 5 := by
    rw [xr, ← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [hq, Pfun_pow, Pfun_pow, Pfun_pow, Pfun_pow, show Real.exp (-(2 * π / 5)) = xr from rfl]
  simp only [show 5 * 1 = 5 from rfl, show 5 * 4 = 20 from rfl, show 5 * 2 = 10 from rfl,
    show 5 * 3 = 15 from rfl, show 5 * 5 = 25 from rfl]
  have hid := realizes_lhs.eq realizes_rhs rr_formal x_mem
  simp only at hid
  rw [eta_step] at hid
  obtain ⟨a1, ha1, e1⟩ := Pfun_real 5 25 (by norm_num) (by norm_num) xr_pos.le xr_lt_one
  obtain ⟨a2, ha2, e2⟩ := Pfun_real 20 25 (by norm_num) (by norm_num) xr_pos.le xr_lt_one
  obtain ⟨b1, hb1, f1⟩ := Pfun_real 10 25 (by norm_num) (by norm_num) xr_pos.le xr_lt_one
  obtain ⟨b2, hb2, f2⟩ := Pfun_real 15 25 (by norm_num) (by norm_num) xr_pos.le xr_lt_one
  obtain ⟨c, hc, g1⟩ := Pfun_real 25 25 (by norm_num) (by norm_num) xr_pos.le xr_lt_one
  simp only [e1, e2, f1, f2, g1] at hid ⊢
  have hid' : (Real.sqrt 5 * xr * c) * (a1 * a2) * (b1 * b2)
      = c * ((b1 * b2) ^ 2 - xr * (a1 * a2) * (b1 * b2) - xr ^ 2 * (a1 * a2) ^ 2) := by
    exact_mod_cast hid
  rw [show (xr : ℂ) * a1 * a2 / (b1 * b2) = ((xr * a1 * a2 / (b1 * b2) : ℝ) : ℂ) by push_cast; ring]
  congr 1
  -- `R = x a₁a₂/(b₁b₂)` is the positive root of `R² + (1+√5)R − 1 = 0`
  set R := xr * a1 * a2 / (b1 * b2) with hR
  have hb : 0 < b1 * b2 := mul_pos hb1 hb2
  have hRpos : 0 < R := by rw [hR]; have := xr_pos; positivity
  have hquad : R ^ 2 + (1 + Real.sqrt 5) * R - 1 = 0 := by
    rw [hR]; field_simp
    have := hc.ne'
    apply mul_left_cancel₀ this
    linear_combination hid'
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  set s := Real.sqrt ((5 + Real.sqrt 5) / 2) with hs
  have hs2 : s ^ 2 = (5 + Real.sqrt 5) / 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hfac : (R - (s - (1 + Real.sqrt 5) / 2)) * (R + s + (1 + Real.sqrt 5) / 2) = 0 := by
    linear_combination hquad - hs2 + (1/4 : ℝ) * h5
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · nlinarith

end RRValue
