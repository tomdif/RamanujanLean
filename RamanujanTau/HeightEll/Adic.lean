/-
# `T`-adic tools in `R⟦T⟧ = MvPowerSeries Unit R`

* `dvd_subst_sub`: substitution respects congruences modulo `T^M`.
* `u₁ A y = Σ aᵢ y^{d-i}` (`d = deg A`): `φ(y)^d · A(1/φ(y)) = φ(u₁)`, and `u₁ ≡ lead(A)` mod `y`.
* `le_of_X_pow_dvd`: `T^M ∣ T^a · u` with `u` a unit forces `M ≤ a`.
-/
import Mathlib

set_option autoImplicit false

namespace HeightEll

open MvPowerSeries

variable {R : Type*} [CommRing R]

local notation "T" => (X () : MvPowerSeries Unit R)

lemma dvd_prod_sub {σ : Type*} (a b : σ → MvPowerSeries Unit R) (M : ℕ)
    (hab : ∀ s, T ^ M ∣ a s - b s) (d : σ →₀ ℕ) :
    T ^ M ∣ (d.prod fun s e => a s ^ e) - (d.prod fun s e => b s ^ e) := by
  set I := Ideal.span {T ^ M}
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have h : ∀ s, Ideal.Quotient.mk I (a s) = Ideal.Quotient.mk I (b s) := fun s =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hab s))
  simp only [map_finsuppProd, map_pow]
  exact Finsupp.prod_congr fun s _ => congrArg (· ^ d s) (h s)

lemma coeff_eq_zero_of_dvd {M : ℕ} {g : MvPowerSeries Unit R} (h : T ^ M ∣ g) (e : Unit →₀ ℕ)
    (he : e () < M) : coeff e g = 0 := X_pow_dvd_iff.1 h e he

/-- **substitution respects congruences mod `T^M`**. -/
theorem dvd_subst_sub {σ : Type*} [Finite σ] (a b : σ → MvPowerSeries Unit R)
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (M : ℕ)
    (hab : ∀ s, T ^ M ∣ a s - b s) (f : MvPowerSeries σ R) :
    T ^ M ∣ subst a f - subst b f := by
  rw [X_pow_dvd_iff]
  intro e he
  rw [map_sub, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hb), sub_eq_zero]
  refine finsum_congr fun d => ?_
  congr 1
  have := coeff_eq_zero_of_dvd (dvd_prod_sub a b M hab d) e he
  rwa [map_sub, sub_eq_zero] at this

section U1
open Polynomial

/-- `u₁ A y = Σ_{i ≤ d} aᵢ y^{d-i}`. -/
noncomputable def u₁ (A : R[X]) (y : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  ∑ i ∈ Finset.range (A.natDegree + 1), MvPowerSeries.C (A.coeff i) * y ^ (A.natDegree - i)

lemma cc_u₁ (A : R[X]) {y : MvPowerSeries Unit R} (hy : constantCoeff y = 0) :
    constantCoeff (u₁ A y) = A.leadingCoeff := by
  rw [u₁, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
  · rw [zero_add, Nat.sub_self, pow_zero, mul_one, constantCoeff_C]; rfl
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, hy, zero_pow (by omega), mul_zero]

lemma eval_u₁ {L : Type*} [Field L] (φ : MvPowerSeries Unit R →+* L) (A : R[X])
    (y : MvPowerSeries Unit R) (hy : φ y ≠ 0) :
    φ y ^ A.natDegree * A.eval₂ (φ.comp MvPowerSeries.C) (1 / φ y) = φ (u₁ A y) := by
  rw [eval₂_eq_sum_range, u₁, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow, RingHom.comp_apply, div_pow, one_pow, pow_sub₀ _ hy (by omega)]
  field_simp

end U1

/-- `T^M ∣ T^a · u` with `u` a unit (`constantCoeff u ≠ 0`) forces `M ≤ a`. -/
theorem le_of_X_pow_dvd {M a : ℕ} {u : MvPowerSeries Unit R} (hu : constantCoeff u ≠ 0)
    (h : T ^ M ∣ T ^ a * u) : M ≤ a := by
  by_contra hlt
  push Not at hlt
  have := coeff_eq_zero_of_dvd h (Finsupp.single () a) (by simpa using hlt)
  rw [X_pow_eq, coeff_monomial_mul, if_pos le_rfl, tsub_self, one_mul,
    coeff_zero_eq_constantCoeff_apply] at this
  exact hu this

end HeightEll
