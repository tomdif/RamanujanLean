/-
# The von Mangoldt identity for the Rankin–Selberg coefficients

`R(s) = Σ λ(n)² n^{−s} = ζ(2s)⁻¹ · exp(Σ cR(n) n^{−s})` (`TauPNTUncond.HH_exp`, `HH_eq`), so

    −R'/R (s) = Σ vR(n) n^{−s} − 2 Σ Λ(m) m^{−2s} = Σ ΛR(n) n^{−s},
    ΛR(n) = vR(n) − 2·Λ(√n)·[n is a square].

Comparing Dirichlet coefficients of `−R' = R · (−R'/R)` (Mathlib's L-series uniqueness):

* `rsb_mul_log`: `λ(n)² log n = Σ_{dm = n} ΛR(d) λ(m)²` for all `n` (unconditional),
  i.e. `rsbA.pmul log = ΛRA * rsbA` as arithmetic functions (`pmul_log_eq`).
-/
import RamanujanTau.TauPNTUncond.Main
import RamanujanTau.RankinError.Tau

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs2

open Complex Filter Topology LSeries ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.vonMangoldt
open RamanujanTau.EdgeNonvanishing (rsb rsB RS rs_summable rsb_nonneg rsb_zero)
open RamanujanTau.TauPNTUncond (vR cR vR_nonneg vR_eq_logMul LSeriesSummable_vR abscissa_cR_le
  abscissa_vR_le HH HH_exp HH_eq differentiableAt_HH)

noncomputable section

/-- `Λ(√n)` on squares, `0` elsewhere. -/
def sqL (n : ℕ) : ℝ := if Nat.sqrt n ^ 2 = n then vonMangoldt (Nat.sqrt n) else 0

lemma sqL_sq (m : ℕ) : sqL (m ^ 2) = vonMangoldt m := by
  simp [sqL, Nat.sqrt_eq']

lemma sqL_nonneg (n : ℕ) : 0 ≤ sqL n := by
  unfold sqL; split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

lemma sqL_zero_of_not {n : ℕ} (h : n ∉ Set.range (fun m : ℕ => m ^ 2)) : sqL n = 0 := by
  unfold sqL
  rw [if_neg]
  exact fun h' => h ⟨_, h'⟩

/-- **`ΛR = vR − 2·sqL`**, the von Mangoldt function of `R(s)`. -/
def LamR (n : ℕ) : ℝ := vR n - 2 * sqL n

lemma LamR_zero : LamR 0 = 0 := by
  have h1 : vR 0 = 0 := TauPNTUncond.vR_of_not (by simp [IsPrimePow])
  simp [LamR, h1, sqL]

/-- `L(sqL, s) = L(Λ, 2s)`. -/
lemma LSeries_sqL (s : ℂ) :
    LSeries (fun n => (sqL n : ℂ)) s = LSeries (fun n => (vonMangoldt n : ℂ)) (2 * s) := by
  unfold LSeries
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective two_ne_zero
  rw [← hinj.tsum_eq (f := term (fun n => (sqL n : ℂ)) s)]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rw [term_of_ne_zero (pow_ne_zero _ hm), term_of_ne_zero hm, sqL_sq]
    congr 1
    rw [Nat.cast_pow, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, natCast_cpow_natCast_mul]
  · intro n hn
    by_contra h
    exact hn (by rw [term_def]; simp [sqL_zero_of_not h])

lemma LSeriesSummable_sqL {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun n => (sqL n : ℂ)) s := by
  have hΛ : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) (2 * s) :=
    LSeriesSummable_vonMangoldt (by simp; linarith)
  unfold LSeriesSummable at hΛ ⊢
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective two_ne_zero
  refine (hinj.summable_iff (f := term (fun n => (sqL n : ℂ)) s) ?_).mp ?_
  · intro n hn
    rw [term_def]; simp [sqL_zero_of_not hn]
  · refine hΛ.congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    simp only [Function.comp_apply]
    rw [term_of_ne_zero (pow_ne_zero _ hm), term_of_ne_zero hm, sqL_sq]
    congr 1
    rw [Nat.cast_pow, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, natCast_cpow_natCast_mul]

lemma abscissa_le_of {f : ℕ → ℂ} (h : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s) :
    abscissaOfAbsConv f ≤ 1 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => h y (by simpa using hy)

lemma abscissa_rsB_le : abscissaOfAbsConv rsB ≤ 1 := abscissa_le_of fun _ hs => rs_summable hs

lemma lt_of_one_lt {s : ℂ} (hs : 1 < s.re) {f : ℕ → ℂ} (h : abscissaOfAbsConv f ≤ 1) :
    abscissaOfAbsConv f < s.re := h.trans_lt (by exact_mod_cast hs)

/-- The complex coefficients of `ΛR`. -/
def LamRc (n : ℕ) : ℂ := (LamR n : ℂ)

lemma LamRc_eq : LamRc = (fun n => (vR n : ℂ)) - (2 : ℂ) • (fun n => (sqL n : ℂ)) := by
  funext n; simp [LamRc, LamR]

lemma LSeriesSummable_LamRc {s : ℂ} (hs : 1 < s.re) : LSeriesSummable LamRc s := by
  rw [LamRc_eq]
  exact (LSeriesSummable_vR hs).sub ((LSeriesSummable_sqL (by linarith)).smul 2)

/-- `L(ΛR, s) = −R'(s)/R(s)` in the form used below. -/
lemma LSeries_LamRc {s : ℂ} (hs : 1 < s.re) :
    LSeries LamRc s = LSeries (fun n => (vR n : ℂ)) s +
      2 * (deriv riemannZeta (2 * s) / riemannZeta (2 * s)) := by
  rw [LamRc_eq, LSeries_sub (LSeriesSummable_vR hs) ((LSeriesSummable_sqL (by linarith)).smul 2),
    LSeries_smul, LSeries_sqL, LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp; linarith)]
  ring

/-- Derivative of `HH = exp(L cR)` on `Re s > 1`. -/
lemma hasDerivAt_HH {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt HH (HH s * -LSeries (fun n => (vR n : ℂ)) s) s := by
  have hL := LSeries_hasDerivAt (lt_of_one_lt hs abscissa_cR_le)
  have hE := hL.cexp
  rw [← vR_eq_logMul, ← HH_exp hs] at hE
  have hU : ∀ᶠ z in 𝓝 s, HH z = cexp (LSeries (fun n => (cR n : ℂ)) z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact HH_exp hz
  exact hE.congr_of_eventuallyEq hU

/-- **`L(log·λ², s) = L(ΛR ⍟ λ², s)`** on `Re s > 1`. -/
lemma LSeries_logMul_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (logMul rsB) s = LSeries (LamRc ⍟ rsB) s := by
  have h2s : 1 < (2 * s).re := by simp; linarith
  have hz : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2s
  have hz1 : 2 * s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  -- derivative of `RS` two ways
  have hR := LSeries_hasDerivAt (lt_of_one_lt hs abscissa_rsB_le)
  have hζ : HasDerivAt (fun z => riemannZeta (2 * z)) (deriv riemannZeta (2 * s) * 2) s := by
    have h1 := (differentiableAt_riemannZeta hz1).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 s := by
      simpa using (hasDerivAt_id s).const_mul (2 : ℂ)
    exact h1.comp s h2
  have hQ := (hasDerivAt_HH hs).div hζ hz
  have hU : ∀ᶠ z in 𝓝 s, LSeries rsB z = HH z / riemannZeta (2 * z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz'
    have hz2 : riemannZeta (2 * z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [HH_eq hz', RS]; field_simp
  have huniq := hR.unique (hQ.congr_of_eventuallyEq hU)
  have hRs : LSeries rsB s = HH s / riemannZeta (2 * s) := hU.self_of_nhds
  rw [LSeries_convolution (lt_of_one_lt hs (abscissa_le_of fun _ h => LSeriesSummable_LamRc h))
    (lt_of_one_lt hs abscissa_rsB_le), LSeries_LamRc hs, hRs]
  have : LSeries (logMul rsB) s = -((HH s * -LSeries (fun n => (vR n : ℂ)) s * riemannZeta (2 * s) -
      HH s * (deriv riemannZeta (2 * s) * 2)) / riemannZeta (2 * s) ^ 2) := by
    rw [← huniq]; ring
  rw [this]
  field_simp
  ring

/-- **The identity `λ(n)² log n = Σ_{dm=n} ΛR(d) λ(m)²`** (complex form, `n ≠ 0`). -/
lemma logMul_rsB_eq {n : ℕ} (hn : n ≠ 0) : logMul rsB n = (LamRc ⍟ rsB) n := by
  have hf : abscissaOfAbsConv (logMul rsB) < ⊤ :=
    (abscissa_le_of fun s hs => LSeriesSummable_logMul_of_lt_re
      (lt_of_one_lt hs abscissa_rsB_le)).trans_lt (by exact_mod_cast EReal.coe_lt_top 1)
  have hg : abscissaOfAbsConv (LamRc ⍟ rsB) < ⊤ :=
    (abscissa_le_of fun s hs => (LSeriesSummable_LamRc hs).convolution (rs_summable hs)).trans_lt
      (by exact_mod_cast EReal.coe_lt_top 1)
  refine LSeries.eq_of_LSeries_eventually_eq hf hg ?_ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact LSeries_logMul_eq (by simpa using hx)

/-- `λ²` as an arithmetic function. -/
def rsbA : ArithmeticFunction ℝ := ⟨rsb, rsb_zero⟩
/-- `ΛR` as an arithmetic function. -/
def LamRA : ArithmeticFunction ℝ := ⟨LamR, LamR_zero⟩

@[simp] lemma rsbA_apply (n : ℕ) : rsbA n = rsb n := rfl
@[simp] lemma LamRA_apply (n : ℕ) : LamRA n = LamR n := rfl

/-- **Real form**: `λ(n)² log n = (ΛR ∗ λ²)(n)` for every `n`. -/
theorem rsb_mul_log (n : ℕ) : rsb n * Real.log n = (LamRA * rsbA) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have h := logMul_rsB_eq hn
  rw [convolution_def] at h
  rw [mul_apply]
  apply Complex.ofReal_injective
  push_cast
  rw [mul_comm]
  simp only [logMul, rsB] at h
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)] at h
  rw [show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)], h]
  simp [LamRc]

end

end RamanujanTau.SelbergCoeffs2
