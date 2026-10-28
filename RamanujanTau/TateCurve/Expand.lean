import RamanujanTau.TateCurve.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.Finite.Basic

/-!
# `Tate(q)` versus `Tate(qᵖ)` and Frobenius

* `TateExp p hp = Tate.map (expand p)` is the Tate curve over `ℤ⟦q⟧` with parameter `qᵖ`; its invariants are
  the expanded invariants of `Tate(q)`: `Δ(Tate(qᵖ)) = expand p (Δ(Tate(q))) = qᵖ ∏ (1 − q^{pn})²⁴`.
* Frobenius on `𝔽_p⟦q⟧`: `f ^ p = expand p f`; hence `f(q)ᵖ ≡ f(qᵖ) (mod p)` for every `f ∈ ℤ⟦q⟧`, in particular
  `Δ(Tate(q))ᵖ ≡ Δ(Tate(qᵖ))`.
-/

set_option autoImplicit false

namespace TateCurve
open PowerSeries

section Expand
variable (p : ℕ) (hp : p ≠ 0)

/-- The Tate curve with parameter `qᵖ`: coefficients `aᵢ(qᵖ)`. -/
noncomputable def TateExp : WeierstrassCurve (PowerSeries ℤ) :=
  Tate.map (expand p hp : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ).toRingHom

lemma TateExp_a₄ : (TateExp p hp).a₄ = expand p hp a4 := rfl
lemma TateExp_a₆ : (TateExp p hp).a₆ = expand p hp a6 := rfl
lemma TateExp_a₁ : (TateExp p hp).a₁ = 1 := by simp [TateExp, Tate]
lemma TateExp_a₂ : (TateExp p hp).a₂ = 0 := by simp [TateExp, Tate]
lemma TateExp_a₃ : (TateExp p hp).a₃ = 0 := by simp [TateExp, Tate]

theorem c₄_TateExp : (TateExp p hp).c₄ = expand p hp Tate.c₄ := by
  rw [TateExp, WeierstrassCurve.map_c₄]; rfl

theorem c₆_TateExp : (TateExp p hp).c₆ = expand p hp Tate.c₆ := by
  rw [TateExp, WeierstrassCurve.map_c₆]; rfl

theorem Δ_TateExp_eq_expand : (TateExp p hp).Δ = expand p hp Tate.Δ := by
  rw [TateExp, WeierstrassCurve.map_Δ]; rfl

/-- `Δ(Tate(qᵖ)) = qᵖ ∏ (1 − q^{pn})²⁴`. -/
theorem Δ_TateExp : (TateExp p hp).Δ = X ^ p * (expand p hp MockTheta5.JTP.qfacInf) ^ 24 := by
  rw [Δ_TateExp_eq_expand, Δ_Tate, map_mul, map_pow, expand_X]

end Expand

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime]

instance charP_powerSeries_zmod : CharP (PowerSeries (ZMod p)) p :=
  charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p

lemma polynomial_pow_eq_expand (P : Polynomial (ZMod p)) :
    ((P : PowerSeries (ZMod p))) ^ p = expand p hp.out.ne_zero (P : PowerSeries (ZMod p)) := by
  let φ₁ : Polynomial (ZMod p) →+* PowerSeries (ZMod p) :=
    (frobenius (PowerSeries (ZMod p)) p).comp Polynomial.coeToPowerSeries.ringHom
  let φ₂ : Polynomial (ZMod p) →+* PowerSeries (ZMod p) :=
    (expand p hp.out.ne_zero : PowerSeries (ZMod p) →ₐ[ZMod p] PowerSeries (ZMod p)).toRingHom.comp
      Polynomial.coeToPowerSeries.ringHom
  have h : φ₁ = φ₂ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [φ₁, φ₂, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, frobenius_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, expand_C]
      rw [← map_pow, ZMod.pow_card]
    · simp [φ₁, φ₂, frobenius_def]
  have := congrArg (fun φ => φ P) h
  simpa [φ₁, φ₂, frobenius_def] using this

/-- **Frobenius on `𝔽_p⟦q⟧`**: `f ^ p = f(qᵖ)`. -/
theorem pow_eq_expand (f : PowerSeries (ZMod p)) : f ^ p = expand p hp.out.ne_zero f := by
  ext m
  set T := trunc (m + 1) f
  have hdvd : (X : PowerSeries (ZMod p)) ^ (m + 1) ∣ f - (T : PowerSeries (ZMod p)) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hj, sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hf : f = (T : PowerSeries (ZMod p)) + X ^ (m + 1) * g := by rw [← hg]; ring
  have key : f ^ p - expand p hp.out.ne_zero f =
      X ^ ((m + 1) * p) * (g ^ p - expand p hp.out.ne_zero g) := by
    rw [hf, add_pow_char, polynomial_pow_eq_expand, map_add, map_mul, map_pow, expand_X, mul_pow,
      ← pow_mul, ← pow_mul, mul_comm p (m + 1)]
    ring
  have hlt : m < (m + 1) * p := by nlinarith [hp.out.two_le]
  have h0 : coeff m (f ^ p - expand p hp.out.ne_zero f) = 0 := by
    rw [key]
    exact (X_pow_dvd_iff.mp (dvd_mul_right _ _)) m hlt
  rwa [map_sub, sub_eq_zero] at h0

/-- **`f(q)ᵖ ≡ f(qᵖ) (mod p)`** for `f ∈ ℤ⟦q⟧`. -/
theorem map_pow_eq_map_expand (f : PowerSeries ℤ) :
    (map (Int.castRingHom (ZMod p)) f) ^ p = map (Int.castRingHom (ZMod p)) (expand p hp.out.ne_zero f) := by
  rw [pow_eq_expand, map_expand]

/-- `Δ(Tate(q))ᵖ ≡ Δ(Tate(qᵖ)) (mod p)`. -/
theorem Δ_Tate_pow_mod_p :
    (map (Int.castRingHom (ZMod p)) Tate.Δ) ^ p =
      map (Int.castRingHom (ZMod p)) (TateExp p hp.out.ne_zero).Δ := by
  rw [map_pow_eq_map_expand, Δ_TateExp_eq_expand]

end Frobenius

end TateCurve
