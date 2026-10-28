/-
# The formal Vélu `Xd` as a product

In `K⟦z⟧`, with `ρ = 1/x = z² v(z)`:
  `Xd · ∏_{Q∈S} (1 - x_Q ρ)³ = ∏_{i, Q} (1 - x(T_i + Q) ρ)`        (`Xd_mul_prod`),
the image of `N₁ = ∏ (X - x(T_i + Q))` (`N1_eq_prod`) under `x ↦ 1/ρ`.
-/
import RamanujanTau.VeluDescent.TwoTorsion
import RamanujanTau.VeluLubin.Formal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries VeluLubin

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

local notation "K1" => MvPowerSeries Unit K
local notation "T" => (X () : MvPowerSeries Unit K)
local notation "ι" => algebraMap (MvPowerSeries Unit K) (FractionRing (MvPowerSeries Unit K))

/-- `ρ = z² v(z)`. -/
noncomputable abbrev rho (A B : K) : K1 := T ^ 2 * vv A B

lemma xL_mul_rho : xL A B * ι (rho A B) = 1 := by
  have hw := ι_ww_ne (A := A) (B := B)
  have e : ι (ww A B) = ι T * ι (rho A B) := by
    rw [← map_mul, ww_eq, rho]; ring_nf
  show ι T / ι (ww A B) * _ = 1
  rw [e] at hw ⊢
  have hT : ι T ≠ 0 := fun h => hw (by rw [h, zero_mul])
  have hr : ι (rho A B) ≠ 0 := fun h => hw (by rw [h, mul_zero])
  field_simp

lemma evx_sub_C (r : K) :
    xL A B - jj r = xL A B * ι (1 - C r * rho A B) := by
  have h := xL_mul_rho (A := A) (B := B)
  rw [map_sub, map_one, map_mul, jj_apply]
  linear_combination (ι (C r)) * h

lemma evx_prod {ι' : Type*} (s : Finset ι') (r : ι' → K) :
    evx A B (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))) =
      xL A B ^ s.card * ι (∏ i ∈ s, (1 - C (r i) * rho A B)) := by
  rw [map_prod, map_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, evx_X, evx_C, ← jj_apply]
  exact evx_sub_C (r i)

variable (κ : Velu.Kernel A B) (h2 : (2 : K) ≠ 0) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
  {e : Fin 3 → K} (he : ∀ i, e i ^ 3 + A * e i + B = 0) (hinj : Function.Injective e)

lemma uQs_eq (Q : (Velu.short A B).Point) : uQs Q = 1 - C (Velu.xc Q) * rho A B := by
  rw [uQs, rho]; ring

include hinj in
/-- **`Xd · ∏ (1 - x_Q ρ)³ = ∏ (1 - x(T_i+Q) ρ)`**. -/
theorem Xd_mul_prod :
    Xd κ * ∏ Q ∈ κ.S, uQs Q ^ 3 =
      ∏ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ κ.S,
        (1 - C (Kernel'.rr h2 hΔ he p) * rho A B) := by
  have hN := evx_N1 κ
  rw [Kernel'.N1_eq_prod κ h2 hΔ he hinj, evx_prod, Velu.Kernel.D] at hN
  simp only [Velu.Kernel.vp] at hN
  rw [evx_prod] at hN
  have hx : xL A B ≠ 0 := by
    intro h; have := xL_mul_rho (A := A) (B := B); rw [h, zero_mul] at this
    exact zero_ne_one this
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
    mul_comm κ.S.card 3, mul_assoc] at hN
  have hN' := mul_left_cancel₀ (pow_ne_zero _ hx) hN
  have hU : ∏ Q ∈ κ.S, uQs Q ^ 3 = (∏ Q ∈ κ.S, (1 - C (Velu.xc Q) * rho A B)) ^ 3 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun Q _ => by rw [uQs_eq])
  apply ι_inj'
  rw [hU, map_mul, hN', map_pow, mul_comm]

end VeluDescent
