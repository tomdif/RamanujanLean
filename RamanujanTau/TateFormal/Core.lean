import RamanujanTau.TateFormal.Cartier
import RamanujanTau.HasseInv.Elliptic

/-!
# From a multiplicative parametrization to `H = 1`

Let `W : y² + xy = x³ + a₄x + a₆` over a ring of characteristic `p` (odd). Suppose `X, Q ∈ R⟦T⟧` with
`X(0) = 1`, `Q(0) = −2`,
  `Q² = 4X³ + T²X² + 4a₄T⁴X + 4a₆T⁶`  and  `(1+T)(T X' − 2X) = Q`
(i.e. `x = X/T²`, `y = (Q − TX)/(2T³)` is a point of `W` over `R((T))` with `(1+T) dx/dT = 2y + x`).
Then `φ = −x/y` satisfies `ω(φ) φ' = 1/(1+T)` and by the Cartier lemma `H(W) = 1`.
-/

set_option autoImplicit false

namespace TateFormal
open MvPowerSeries EllipticFormal FGL HasseInv

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R
local notation "TT" => (X () : MvPowerSeries Unit R)

lemma coeff_inv_one_add (g : PowerSeries R) (h : (1 + PowerSeries.X) * g = 1) (n : ℕ) :
    PowerSeries.coeff n g = (-1) ^ n := by
  induction n with
  | zero =>
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  | succ n ih =>
    have := congrArg (PowerSeries.coeff (n + 1)) h
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, ih, PowerSeries.coeff_one,
      if_neg (by omega)] at this
    rw [pow_succ]; linear_combination this

theorem hasseH_eq_one_of_param (p : ℕ) [hp : Fact p.Prime] [CharP R p] (hp2 : p ≠ 2)
    (W : WeierstrassCurve R) (ha1 : W.a₁ = 1) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    (Xs Qs : R1) (hX0 : constantCoeff Xs = 1) (hQ0 : constantCoeff Qs = -2)
    (hE4 : Qs ^ 2 = 4 * Xs ^ 3 + TT ^ 2 * Xs ^ 2 + 4 * C W.a₄ * TT ^ 4 * Xs + 4 * C W.a₆ * TT ^ 6)
    (hD : (1 + TT) * (TT * pd () Xs - 2 * Xs) = Qs) :
    hasseH p W = 1 := by
  -- `1/2`
  have hpo : p = 2 * ((p - 1) / 2) + 1 := odd_p p hp2
  set i2 : R1 := (((p + 1) / 2 : ℕ) : R1) with hi2
  have h2 : 2 * i2 = 1 := by
    have e : 2 * ((p + 1) / 2) = p + 1 := by omega
    have : ((2 * ((p + 1) / 2) : ℕ) : R1) = ((p + 1 : ℕ) : R1) := by rw [e]
    push_cast at this
    rw [hi2, this, p_R1 p, zero_add]
  have h2R : 2 * (((p + 1) / 2 : ℕ) : R) = 1 := by
    have := congrArg constantCoeff h2
    simpa [hi2] using this
  set Y : R1 := i2 * (Qs - TT * Xs) with hY
  have hQY : Qs = 2 * Y + TT * Xs := by rw [hY]; linear_combination (-(Qs - TT * Xs)) * h2
  set Ee : R1 := Y ^ 2 + TT * Xs * Y - Xs ^ 3 - C W.a₄ * TT ^ 4 * Xs - C W.a₆ * TT ^ 6 with hEe
  have hE : Ee = 0 := by
    have h4 : 4 * Ee = 0 := by rw [hQY] at hE4; rw [hEe]; linear_combination hE4
    linear_combination i2 ^ 2 * h4 - Ee * (1 + 2 * i2) * h2
  have hY0 : constantCoeff Y = -1 := by
    rw [hY, map_mul, map_sub, map_mul, hQ0, hX0]
    simp only [hi2, map_natCast, constantCoeff_X, zero_mul, sub_zero]
    linear_combination (-1 : R) * h2R
  -- `V = 1/Y`
  set V : R1 := invOfUnit Y (-1) with hV
  have hVY : V * Y = 1 := by
    rw [mul_comm]; exact mul_invOfUnit Y (-1) (by rw [hY0]; simp)
  have hV0 : constantCoeff V = -1 := by
    have := congrArg constantCoeff hVY
    rw [map_mul, hY0, map_one] at this
    linear_combination -this
  set φ : R1 := -TT * Xs * V with hφ
  set ŵ : R1 := -TT ^ 3 * V with hŵ
  have hφ0 : constantCoeff φ = 0 := by simp [hφ]
  have hŵ0 : constantCoeff ŵ = 0 := by simp [hŵ]
  -- the point lies on the curve
  have hG : G (WM W Unit) φ ŵ = 0 := by
    simp only [G, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ha1, ha2, ha3, map_one, map_zero, hφ, hŵ]
    linear_combination (TT ^ 3 * V ^ 3) * hE - (TT ^ 4 * Xs * V ^ 2 + TT ^ 3 * V * (1 + V * Y)) * hVY
  have hw : ŵ = wt W φ := G_unique (WM W Unit) hφ0 hŵ0 (cc_wt (W := W) hφ0) hG (G_wt (W := W) hφ0)
  have hS : HasSubst (fun _ : Unit => φ) := FGL.hs (fun _ => hφ0)
  have hΨ : FGL.Ψ (formalGroup W) φ = 1 - φ - 2 * C W.a₄ * φ * ŵ - 3 * C W.a₆ * ŵ ^ 2 := by
    rw [Ψ_subst (formalGroup W) hφ0, Ψ_formalGroup, ha1, ha2, ha3, hw]
    rw [← coe_substAlgHom hS]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero, zero_mul, sub_zero]
    simp only [coe_substAlgHom]
    simp only [one_mul, mul_zero, zero_mul, sub_zero]
    rw [subst_X hS]
    erw [subst_C, subst_C]
    rfl
  -- derivatives
  have pT : pd () TT = 1 := by rw [FGL.pd_X', if_pos rfl]
  have pC : ∀ a : R, pd () (C a : R1) = 0 := fun a => pd_C () a
  have hEp : 2 * Y * pd () Y + Xs * Y + TT * pd () Xs * Y + TT * Xs * pd () Y -
      3 * Xs ^ 2 * pd () Xs - 4 * C W.a₄ * TT ^ 3 * Xs - C W.a₄ * TT ^ 4 * pd () Xs -
      6 * C W.a₆ * TT ^ 5 = 0 := by
    have h := congrArg (pd ()) hE
    rw [hEe, pd_zero'] at h
    rw [show Y ^ 2 = Y ^ (1 + 1) from rfl, show Xs ^ 3 = Xs ^ (2 + 1) from rfl,
      show TT ^ 4 = TT ^ (3 + 1) from rfl, show TT ^ 6 = TT ^ (5 + 1) from rfl] at h
    simp only [pd_add, pd_sub, pd_mul, pd_pow_succ, pT, pC] at h
    push_cast at h
    linear_combination h
  have hV1 : pd () V = -V ^ 2 * pd () Y := by
    have h := congrArg (pd ()) hVY
    rw [pd_mul, show (1 : R1) = C 1 from rfl, pC] at h
    linear_combination V * h - pd () V * hVY
  have hpdφ : pd () φ = -(Xs * V + TT * pd () Xs * V + TT * Xs * pd () V) := by
    have hn : pd () (-TT) = -1 := by
      rw [show -TT = 0 - TT by ring, pd_sub, pT, pd_zero']; ring
    rw [hφ, pd_mul, pd_mul, hn]; ring
  have hD' : (1 + TT) * (TT * pd () Xs - 2 * Xs) = 2 * Y + TT * Xs := by rw [hD, hQY]
  have key : (FGL.Ψ (formalGroup W) φ - (1 + TT) * pd () φ) * (Y ^ 2 * (2 * Y + TT * Xs)) = 0 := by
    rw [hΨ, hpdφ, hV1, hφ, hŵ]
    linear_combination (-TT * Xs * (TT + 1)) * hEp +
      (-TT ^ 4 * Xs * C W.a₄ + 2 * TT * Xs * Y - 3 * Xs ^ 3 + 2 * Y ^ 2) * hD' +
      (3 * (3 * TT * Xs + 2 * Xs + 2 * Y)) * hE +
      (-(TT * Xs + 2 * Y) * (3 * TT ^ 6 * V * Y * C W.a₆ + 3 * TT ^ 6 * C W.a₆ +
        2 * TT ^ 4 * V * Xs * Y * C W.a₄ + 2 * TT ^ 4 * Xs * C W.a₄ + TT ^ 2 * V * Xs * Y * pd () Y +
        TT ^ 2 * Xs * pd () Y - TT ^ 2 * pd () Xs * Y + TT * V * Xs * Y * pd () Y -
        2 * TT * Xs * Y + TT * Xs * pd () Y - TT * pd () Xs * Y - Xs * Y)) * hVY
  have hunit : IsUnit (Y ^ 2 * (2 * Y + TT * Xs)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have : constantCoeff (Y ^ 2 * (2 * Y + TT * Xs)) = -2 := by
      simp [hY0, map_ofNat]
    rw [this]
    exact IsUnit.of_mul_eq_one (-(((p + 1) / 2 : ℕ) : R)) (by linear_combination h2R)
  have hΨφ : FGL.Ψ (formalGroup W) φ = (1 + TT) * pd () φ :=
    sub_eq_zero.mp ((hunit.mul_left_eq_zero).mp key)
  -- `ω(φ) φ' = 1/(1+T)`
  have hω : FGL.Ψ (formalGroup W) φ * subst (fun _ : Unit => φ) (omega (formalGroup W)) = 1 := by
    rw [Ψ_subst (formalGroup W) hφ0, ← subst_mul hS, Ψ_mul_omega, subst_one']
  set g : R1 := subst (fun _ : Unit => φ) (omega (formalGroup W)) * pd () φ with hg
  have hg1' : (1 + TT) * g = 1 := by
    rw [hΨφ] at hω
    rw [hg]; linear_combination hω
  have hg1 : (1 + PowerSeries.X) * (g : PowerSeries R) = 1 := hg1'
  have hφ1 : PowerSeries.coeff 1 (φ : PowerSeries R) = 1 := by
    have e : φ = TT * (-(Xs * V)) := by rw [hφ]; ring
    rw [e]
    erw [PowerSeries.coeff_succ_X_mul]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    show constantCoeff (-(Xs * V)) = 1
    rw [map_neg, map_mul, hX0, hV0]; ring
  have hc := cartier p (omega (formalGroup W)) φ hφ0 hφ1
  rw [← hg, coeff_inv_one_add _ hg1] at hc
  have heven : Even (p - 1) := ⟨(p - 1) / 2, by omega⟩
  rw [heven.neg_one_pow] at hc
  rw [← coeff_omega_eq_hasseH p hp2 W]
  exact hc.symm

end TateFormal
