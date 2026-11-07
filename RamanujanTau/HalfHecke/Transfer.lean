import RamanujanTau.HalfHecke.Expansion

/-!
# Moving a coset of `T(Q²)` under `S`

If `α S = γ α'` with `γ = [a b; c d] ∈ SL₂(ℤ)`, `c > 0` odd, then on `w = α(−1/z)`, `u = α' z`, with
`cu + d = r z` (`r > 0`):

  `η(−1/z) F(w) = z^k · (e(−3/24)/v_γ) · r^k/√r · η(z) F(u)`,

where `v_γ = (d/c) e(((a+d)c − bd(c²−1) − 3c)/24)` is Petersson's value of the `η`-multiplier
(`ThetaLift.etaLaw_odd`). This is the only place the `η` transformation formula enters.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex ModularForm Finset Rademacher
open UpperHalfPlane hiding I
open RamanujanTau.ThetaLift
open scoped Real MatrixGroups

noncomputable section

/-- The matrix `[a b; c d]`. -/
def gam (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; linarith⟩

lemma gam_10 (a b c d : ℤ) (h : a * d - b * c = 1) : gam a b c d h 1 0 = c := rfl
lemma gam_11 (a b c d : ℤ) (h : a * d - b * c = 1) : gam a b c d h 1 1 = d := rfl

lemma petVal_gam (a b c d : ℤ) (h : a * d - b * c = 1) :
    petVal (gam a b c d h) = (jacobiSym d c.natAbs : ℂ) * e24 (petE a b c d) := rfl

lemma mob_gam (a b c d : ℤ) (h : a * d - b * c = 1) (u : ℂ) :
    mob (gam a b c d h) u = (a * u + b) / (c * u + d) := rfl

lemma lin_gam (a b c d : ℤ) (h : a * d - b * c = 1) (u : ℂ) :
    lin (gam a b c d h) u = c * u + d := rfl

/-- `√(r z) = √r √z` for `r > 0`. -/
lemma sqrt_ofReal_mul {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) :
    Complex.sqrt ((r : ℂ) * z) = (Real.sqrt r : ℂ) * Complex.sqrt z := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [Complex.sqrt]
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hz), cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul hr hz, add_mul, Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le, cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
  push_cast; ring_nf

variable {k : ℤ} (G : CuspForm 𝒮ℒ k)

lemma Gc_mob (γ : SL(2, ℤ)) (u : ℂ) (hu : 0 < u.im) : Gc G (mob γ u) = lin γ u ^ k * Gc G u := by
  set tu : ℍ := ⟨u, hu⟩
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hG := SlashInvariantForm.slash_action_eqn'' G hmem tu
  have hden : denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) tu = lin γ u := by
    simp [UpperHalfPlane.denom, lin, tu]
  have h1 : Gc G (mob γ u) = G (γ • tu) := by
    unfold Gc; rw [show u = (tu : ℂ) from rfl, mob_eq γ tu, ofComplex_apply]
  have h2 : Gc G u = G tu := by
    unfold Gc; rw [show u = (tu : ℂ) from rfl, ofComplex_apply]
  rw [h1, h2, ← hden]
  exact hG

/-- **The transfer identity.** -/
theorem transfer (a b d : ℤ) (c : ℕ) (hodd : Odd c) (h : a * d - b * c = 1) {z u w : ℂ}
    (hz : 0 < z.im) (hu : 0 < u.im) {r : ℝ} (hr : 0 < r) (hlin : (c : ℂ) * u + d = r * z)
    (hw : w = (a * u + b) / (c * u + d)) :
    η (-1 / z) * Fc G w = z ^ k * ((e24 (-3) / ((jacobiSym d c : ℂ) * e24 (petE a b c d))) *
      ((r : ℂ) ^ k / (Real.sqrt r : ℂ))) * (η z * Fc G u) := by
  set γ := gam a b (c : ℤ) d h
  have hlaw := etaLaw_odd c γ rfl hodd u hu
  have hmob : mob γ u = w := by rw [mob_gam, hw, Int.cast_natCast]
  have hlin' : lin γ u = r * z := by rw [lin_gam, Int.cast_natCast, hlin]
  rw [hmob, hlin', petVal_gam] at hlaw
  have hG := Gc_mob G γ u hu
  rw [hmob, hlin'] at hG
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hS := eta_S z hz
  have hsq := sqrt_ofReal_mul hr hz0
  have hηu := eta_ne_zero hu
  have hηz := eta_ne_zero hz
  have hsz : Complex.sqrt z ≠ 0 := by
    simp only [Complex.sqrt]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hz0
  have hsr : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hj : (jacobiSym d (c : ℤ).natAbs : ℂ) ≠ 0 := by
    intro h0
    have : jacobiSym d (c : ℤ).natAbs = 0 := by exact_mod_cast h0
    rw [jacobiSym.eq_zero_iff] at this
    obtain ⟨_, hg⟩ := this
    have hcop : Int.gcd d c = 1 := by
      exact Int.isCoprime_iff_gcd_eq_one.mp ⟨a, -b, by linarith⟩
    simp at hg; omega
  have he := e24_ne_zero (petE a b c d)
  have hηw : η w ≠ 0 := by
    rw [hlaw]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj he) (by rw [hsq]; exact mul_ne_zero hsr hsz)) hηu
  simp only [Int.natAbs_natCast] at hlaw hj
  unfold Fc
  rw [hG, hlaw, hS, hsq, mul_zpow]
  field_simp

end

end RamanujanTau.HalfHecke
