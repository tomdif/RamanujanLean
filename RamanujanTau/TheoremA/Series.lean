import RamanujanTau.BoylanWebb.Forms
import Mathlib.FieldTheory.Finite.Basic

/-!
# Theta and coefficient extraction on actual formal power series

These identities hold coefficientwise, including over extension fields of
`ZMod p`. They do not require a modular-form interpretation of the series.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries

section Ring
variable {R : Type*} [CommRing R]

/-- Coefficient extraction, using the existing Boylan–Webb operator. -/
noncomputable def uOperator (d : ℕ) : Module.End R (PowerSeries R) where
  toFun := BoylanWebb.U d
  map_add' f g := by ext n; simp [BoylanWebb.coeff_U]
  map_smul' c f := by ext n; simp [BoylanWebb.coeff_U]

@[simp] theorem uOperator_apply (d : ℕ) (f : PowerSeries R) :
    uOperator d f = BoylanWebb.U d f := rfl

/-- The operator `q d/dq`, as a linear endomorphism of formal power series. -/
noncomputable def theta : Module.End R (PowerSeries R) where
  toFun f := mk fun n => (n : R) * coeff n f
  map_add' f g := by ext n; simp [mul_add]
  map_smul' c f := by ext n; simp; ring

@[simp] theorem coeff_theta (n : ℕ) (f : PowerSeries R) :
    coeff n (theta f) = (n : R) * coeff n f := by simp [theta]

theorem coeff_theta_pow (r n : ℕ) (f : PowerSeries R) :
    coeff n ((theta ^ r) f) = (n : R) ^ r * coeff n f := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, coeff_theta, ih, pow_succ']
    ring

/-- Differentiating `r` times multiplies the `U_d` eigenvalue by `d^r`. -/
theorem U_theta_pow (d r : ℕ) (f : PowerSeries R) :
    BoylanWebb.U d ((theta ^ r) f) =
      (d : R) ^ r • ((theta ^ r) (BoylanWebb.U d f)) := by
  ext n
  simp only [BoylanWebb.coeff_U, coeff_theta_pow, coeff_smul, smul_eq_mul,
    Nat.cast_mul, mul_pow]
  ring

/-- A normalized series remains nonzero after any number of theta operations. -/
theorem theta_pow_ne_zero (f : PowerSeries R) (hf : coeff 1 f ≠ 0) (r : ℕ) :
    (theta ^ r) f ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  apply hf
  simpa [coeff_theta_pow] using this

end Ring

section Prime
variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [CharP K p]

private lemma natCast_pow_sub_one (n : ℕ) (hn : ¬ p ∣ n) :
    (n : K) ^ (p - 1) = 1 := by
  have h : (n : ZMod p) ≠ 0 := by
    intro h
    exact hn ((ZMod.natCast_eq_zero_iff n p).mp h)
  have he := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card_sub_one_eq_one h)
  simpa only [map_pow, map_natCast, map_one] using he

/-- The coefficientwise theta-cycle criterion, over any field of characteristic `p`. -/
theorem U_eq_zero_iff_theta_cycle (f : PowerSeries K) :
    BoylanWebb.U p f = 0 ↔ (theta ^ (p - 1)) f = f := by
  constructor
  · intro hu
    ext n
    rw [coeff_theta_pow]
    by_cases hn : p ∣ n
    · obtain ⟨j, rfl⟩ := hn
      have hz := congrArg (coeff j) hu
      simp only [BoylanWebb.coeff_U, map_zero] at hz
      rw [hz, mul_zero]
    · rw [natCast_pow_sub_one n hn, one_mul]
  · intro ht
    ext n
    have h := congrArg (coeff (p * n)) ht
    have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
    simpa [coeff_theta_pow, Nat.cast_mul, CharP.cast_eq_zero K p, hp1,
      BoylanWebb.coeff_U] using h.symm

end Prime
end RamanujanTau.TheoremA
