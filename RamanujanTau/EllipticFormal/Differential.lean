/-
# The invariant differential of the formal group of a Weierstrass curve

With `FGL.Ψ F u = (∂₂F)(u, 0)` (so that `ω = dT / Ψ(T)` is the normalized invariant differential):
  `Ψ_{F_W}(T) = 1 - a₁ T - a₂ T² - 2 a₃ w - 2 a₄ T w - 3 a₆ w² = -(∂G/∂w)(T, w(T))`,
and, equivalently (Silverman IV.1: `ω = dx / (2y + a₁ x + a₃)` in the parameter `z`),
  `Ψ_{F_W}(T) · (w - T w') = w · (-2 + a₁ T + a₃ w)`.

Method: `E₀ f = f(T, 0)` and `E₁ f = (∂₂ f)(T, 0)` turn the chord identities into identities in
`R⟦T⟧`; over a domain the resulting system is solved in `Frac R⟦T⟧` (`psi_field`), and the
general case follows by specialization from the universal curve.
-/
import RamanujanTau.EllipticFormal.FormalGroup
import RamanujanTau.FormalGroupLayer.Invariant

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace EllipticFormal

open MvPowerSeries

/-! ## The field computation -/

theorem psi_field {K : Type*} [Field K] (a₁ a₂ a₃ a₄ a₆ T w L L' N' I0 I1 Z0 Z1 e0 e1 : K)
    (hT : T ≠ 0) (hδ' : 1 - a₁ * T - a₃ * w ≠ 0)
    (hG : T ^ 3 + a₁ * T * w + a₂ * T ^ 2 * w + a₃ * w ^ 2 + a₄ * T * w ^ 2 + a₆ * w ^ 3 - w = 0)
    (r1 : T * L = w) (r2 : L = T * L') (r4 : N' = -(T * L'))
    (r5 : (1 + a₂ * L + a₄ * L ^ 2 + a₆ * L ^ 3) * I0 = 1)
    (r6 : (1 + a₂ * L + a₄ * L ^ 2 + a₆ * L ^ 3) * I1 + (a₂ + 2 * a₄ * L + 3 * a₆ * L ^ 2) * L' * I0 = 0)
    (r7 : Z0 = -T - (a₁ * L + a₃ * L ^ 2) * I0)
    (r8 : Z1 = -1 - ((a₁ * L' + a₂ * N' + 2 * a₃ * L * L' + 2 * a₄ * L * N' + 3 * a₆ * L ^ 2 * N') * I0 +
      (a₁ * L + a₃ * L ^ 2) * I1))
    (r13 : (a₁ * Z0 + a₃ * (L * Z0) - 1) * e0 = 1)
    (r14 : (a₁ * Z0 + a₃ * (L * Z0) - 1) * e1 +
      (a₁ * Z1 + a₃ * (L * Z1 + L' * Z0 + N')) * e0 = 0) :
    Z1 * e0 + Z0 * e1 = 1 - a₁ * T - a₂ * T ^ 2 - 2 * a₃ * w - 2 * a₄ * T * w - 3 * a₆ * w ^ 2 := by
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = 1 - a₁ * T - a₃ * w := ⟨_, rfl⟩
  have hδ : δ ≠ 0 := hδd ▸ hδ'
  have hI1 : I1 = -((a₂ + 2 * a₄ * L + 3 * a₆ * L ^ 2) * L') * I0 ^ 2 := by
    linear_combination I0 * r6 - I1 * r5
  have hL : L = w / T := by rw [eq_div_iff hT, mul_comm]; exact r1
  have hL' : L' = w / T ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hT)]; linear_combination r1 - T * r2
  subst hI1 hL hL' r4
  have hℓ : 1 + a₂ * (w / T) + a₄ * (w / T) ^ 2 + a₆ * (w / T) ^ 3 = w * δ / T ^ 3 := by
    field_simp; rw [hδd]; linear_combination hG
  rw [hℓ] at r5
  have hw : w ≠ 0 := by rintro rfl; simp at r5
  have hI0 : I0 = T ^ 3 / (w * δ) := by
    rw [eq_div_iff (mul_ne_zero hw hδ)]; field_simp at r5; linear_combination r5
  subst hI0
  have hZ0 : Z0 = -T / δ := by
    rw [r7]; field_simp; rw [hδd]; ring
  rw [hZ0] at r13 r14 ⊢
  have hD0 : a₁ * (-T / δ) + a₃ * (w / T * (-T / δ)) - 1 = -1 / δ := by
    field_simp; rw [hδd]; ring
  rw [hD0] at r13 r14
  have he0 : e0 = -δ := by
    rw [eq_inv_of_mul_eq_one_right r13, inv_div]; ring
  subst he0
  set D1 := a₁ * Z1 + a₃ * (w / T * Z1 + w / T ^ 2 * (-T / δ) + -(T * (w / T ^ 2))) with hD1
  have he1 : e1 = -(D1 * δ) * δ := by
    rw [← div_eq_iff hδ]; linear_combination -r14
  rw [he1, hD1, r8]
  field_simp
  rw [hδd]
  ring

/-! ## `E₀ f = f(T, 0)`, `E₁ f = (∂₂ f)(T, 0)` -/

variable {R : Type*} [CommRing R]

local notation "A₂" => MvPowerSeries (Fin 2) R
local notation "R1" => MvPowerSeries Unit R

lemma hv0 : ∀ s, constantCoeff ((![X (), 0] : Fin 2 → R1) s) = 0 :=
  FGL.cc_vec2 (by simp) (by simp)

/-- `f ↦ f(T, 0)`. -/
noncomputable def E0 : A₂ →ₐ[R] R1 := substAlgHom (FGL.hs (hv0 (R := R)))

lemma E0_apply (f : A₂) : E0 f = subst ![X (), 0] f := by rw [E0, coe_substAlgHom]

/-- `f ↦ (∂₂ f)(T, 0)`. -/
noncomputable def E1 (f : A₂) : R1 := subst ![X (), 0] (pd 1 f)

lemma E1_eq (f : A₂) : E1 f = E0 (pd 1 f) := by rw [E0_apply]; rfl

@[simp] lemma E1_add (f g : A₂) : E1 (f + g) = E1 f + E1 g := by simp [E1_eq, pd_add]
@[simp] lemma E1_sub (f g : A₂) : E1 (f - g) = E1 f - E1 g := by simp [E1_eq, pd_sub]
@[simp] lemma E1_neg (f : A₂) : E1 (-f) = -E1 f := by
  rw [show -f = 0 - f by ring, E1_sub]
  simp [E1_eq, show pd 1 (0 : A₂) = 0 from FGL.pd_zero' 1]
@[simp] lemma E1_mul (f g : A₂) : E1 (f * g) = E1 f * E0 g + E0 f * E1 g := by
  simp only [E1_eq, pd_mul, map_add, map_mul]
@[simp] lemma E1_C (r : R) : E1 (C r : A₂) = 0 := by simp [E1_eq, pd_C]
@[simp] lemma E1_one : E1 (1 : A₂) = 0 := by rw [← map_one (C (σ := Fin 2) (R := R)), E1_C]
@[simp] lemma E1_ofNat (n : ℕ) [n.AtLeastTwo] : E1 (OfNat.ofNat n : A₂) = 0 := by
  rw [← map_ofNat (C (σ := Fin 2) (R := R)) n, E1_C]
@[simp] lemma E1_X0 : E1 (X 0 : A₂) = 0 := by simp [E1_eq, FGL.pd_X']
@[simp] lemma E1_X1 : E1 (X 1 : A₂) = 1 := by simp [E1_eq, FGL.pd_X']
@[simp] lemma E0_X0 : E0 (X 0 : A₂) = X () := by rw [E0_apply]; exact FGL.sX _ hv0 0
@[simp] lemma E0_X1 : E0 (X 1 : A₂) = 0 := by rw [E0_apply]; exact FGL.sX _ hv0 1
@[simp] lemma E0_C (r : R) : E0 (C r : A₂) = C r := by
  rw [c_eq_algebraMap, c_eq_algebraMap]; exact E0.commutes r

variable (W : WeierstrassCurve R)

@[simp] lemma E0_wt0 : E0 (wt W (X 0 : A₂)) = (w W : R1) := by
  rw [E0_apply, subst_wt (by simp) _ hv0, FGL.sX _ hv0 0]
  exact PowerSeries.X_subst _

lemma wt_zero : wt W (0 : R1) = 0 := by
  rw [wt, PowerSeries.subst_def, FGL.subst_zeros,
    show MvPowerSeries.constantCoeff (w W : R1) = 0 from cc_w W, map_zero]

@[simp] lemma E0_wt1 : E0 (wt W (X 1 : A₂)) = 0 := by
  rw [E0_apply, subst_wt (by simp) _ hv0, FGL.sX _ hv0 1]
  exact wt_zero W

lemma pd_wt (j i : Fin 2) : pd i (wt W (X j : A₂)) =
    subst (fun _ : Unit => (X j : A₂)) (pd () (w W : R1)) * pd i (X j : A₂) := by
  rw [wt, PowerSeries.subst_def, pd_subst (fun _ => by simp)]
  simp

@[simp] lemma E1_wt (j : Fin 2) : E1 (wt W (X j : A₂)) = 0 := by
  rw [E1_eq, pd_wt, map_mul, FGL.pd_X']
  split_ifs with h
  · subst h
    have : constantCoeff (pd () (w W : R1)) = 0 := by
      rw [← lin_eq]
      exact coeff_w_of_lt W (by simp)
    rw [E0_apply, FGL.ss _ _ (fun _ => by simp) hv0, FGL.sX _ hv0 1]
    have e : (fun _ : Unit => (![X (), 0] : Fin 2 → R1) 1) = fun _ => 0 := rfl
    rw [e, FGL.subst_zeros, this, map_zero, zero_mul]
  · simp

/-! ### The chord data at `(T, 0)` -/

local notation "T" => (X () : R1)
local notation "w₁" => (w W : R1)

lemma r1 : T * E0 (lam W) = w₁ := by
  have h := congrArg E0 (lam_spec W)
  simp only [map_mul, map_sub, E0_X0, E0_X1, E0_wt0, E0_wt1] at h
  linear_combination -h

lemma r2 : E0 (lam W) = T * E1 (lam W) := by
  have h := congrArg E1 (lam_spec W)
  simp only [E1_mul, E1_sub, E1_X0, E1_X1, map_sub, E0_X0, E0_X1, E1_wt] at h
  linear_combination h

lemma rN : E0 (nu W) = 0 := by
  rw [nu, map_sub, map_mul, E0_wt0, E0_X0, ← r1]; ring

lemma r4 : E1 (nu W) = -(T * E1 (lam W)) := by
  rw [nu, E1_sub, E1_mul, E1_wt, E1_X0, E0_X0]; ring

local notation "Wa" => WeierstrassCurve.map_a₁
lemma r5 : (1 + C W.a₂ * E0 (lam W) + C W.a₄ * E0 (lam W) ^ 2 + C W.a₆ * E0 (lam W) ^ 3) *
    E0 (leadInv W) = 1 := by
  have h := congrArg E0 (lead_mul_leadInv W)
  simp only [lead, map_mul, map_add, map_pow, map_one, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, E0_C] at h
  exact h

lemma r6 : (1 + C W.a₂ * E0 (lam W) + C W.a₄ * E0 (lam W) ^ 2 + C W.a₆ * E0 (lam W) ^ 3) *
    E1 (leadInv W) + (C W.a₂ + 2 * C W.a₄ * E0 (lam W) + 3 * C W.a₆ * E0 (lam W) ^ 2) *
    E1 (lam W) * E0 (leadInv W) = 0 := by
  have h := congrArg E1 (lead_mul_leadInv W)
  simp only [lead, E1_mul, E1_add, pow_succ, pow_zero, one_mul, E1_C, E1_one, map_mul, map_add,
    map_one, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, E0_C] at h
  linear_combination h

lemma r7 : E0 (z3 W) = -X () - (C W.a₁ * E0 (lam W) + C W.a₃ * E0 (lam W) ^ 2) * E0 (leadInv W) := by
  rw [z3]
  simp only [B, map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat, E0_X0, E0_X1,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, E0_C, rN]
  ring

lemma r8 : E1 (z3 W) = -1 - ((C W.a₁ * E1 (lam W) + C W.a₂ * E1 (nu W) +
    2 * C W.a₃ * E0 (lam W) * E1 (lam W) + 2 * C W.a₄ * E0 (lam W) * E1 (nu W) +
    3 * C W.a₆ * E0 (lam W) ^ 2 * E1 (nu W)) * E0 (leadInv W) +
    (C W.a₁ * E0 (lam W) + C W.a₃ * E0 (lam W) ^ 2) * E1 (leadInv W)) := by
  rw [z3]
  simp only [B, E1_sub, E1_neg, E1_mul, E1_add, pow_succ, pow_zero, one_mul, E1_C, E1_one,
    E1_ofNat, E1_X0, E1_X1, map_sub, map_neg, map_mul, map_add, map_pow, map_one, map_ofNat,
    E0_X0, E0_X1, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, E0_C, rN]
  ring

lemma rV0 : E0 (w3 W) = E0 (lam W) * E0 (z3 W) := by
  rw [w3, map_add, map_mul, rN, add_zero]

lemma rV1 : E1 (w3 W) = E0 (lam W) * E1 (z3 W) + E1 (lam W) * E0 (z3 W) + E1 (nu W) := by
  rw [w3, E1_add, E1_mul]; ring

lemma r13 : (C W.a₁ * E0 (z3 W) + C W.a₃ * (E0 (lam W) * E0 (z3 W)) - 1) * E0 (dInv W) = 1 := by
  have h := congrArg E0 (dd_mul_dInv W)
  rw [map_mul, map_one, dd] at h
  simpa only [map_sub, map_add, map_mul, map_one, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, E0_C, rV0] using h

lemma r14 : (C W.a₁ * E0 (z3 W) + C W.a₃ * (E0 (lam W) * E0 (z3 W)) - 1) * E1 (dInv W) +
    (C W.a₁ * E1 (z3 W) + C W.a₃ * (E0 (lam W) * E1 (z3 W) + E1 (lam W) * E0 (z3 W) + E1 (nu W))) *
      E0 (dInv W) = 0 := by
  have h := congrArg E1 (dd_mul_dInv W)
  rw [E1_mul, E1_one, dd] at h
  simp only [E1_sub, E1_add, E1_mul, E1_C, E1_one, map_sub, map_add, map_mul, map_one,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, E0_C, rV0, rV1] at h
  linear_combination h

lemma Ψ_eq_E1 : FGL.Ψ (formalGroup W) (FGL.T : R1) = E1 (F W) := rfl

lemma E1_F : E1 (F W) = E1 (z3 W) * E0 (dInv W) + E0 (z3 W) * E1 (dInv W) := by
  rw [F, E1_mul]

lemma G_T : (X () : R1) ^ 3 + C W.a₁ * X () * w₁ + C W.a₂ * X () ^ 2 * w₁ + C W.a₃ * w₁ ^ 2 +
    C W.a₄ * X () * w₁ ^ 2 + C W.a₆ * w₁ ^ 3 - w₁ = 0 := by
  have h := G_wt (W := W) (t := (X () : R1)) (by simp)
  have e : wt W (X () : R1) = w₁ := PowerSeries.X_subst _
  rw [e] at h
  simpa only [G, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using h

/-- the invariant-differential series over a domain. -/
theorem E1_F_domain [IsDomain R] : E1 (F W) = 1 - C W.a₁ * X () - C W.a₂ * X () ^ 2 -
    2 * C W.a₃ * w₁ - 2 * C W.a₄ * X () * w₁ - 3 * C W.a₆ * w₁ ^ 2 := by
  let ι := algebraMap R1 (FractionRing R1)
  have hinj : Function.Injective ι := IsFractionRing.injective R1 (FractionRing R1)
  have hT : ι (X ()) ≠ 0 := fun h => by
    have := hinj (h.trans (map_zero ι).symm)
    have h1 := congrArg (coeff (Finsupp.single () 1)) this
    simp at h1
  have hδ : 1 - ι (C W.a₁) * ι (X ()) - ι (C W.a₃) * ι w₁ ≠ 0 := by
    intro h
    have h' : ι (1 - C W.a₁ * X () - C W.a₃ * w₁) = ι 0 := by
      rw [map_zero, ← h]; simp only [map_sub, map_mul, map_one]
    have := congrArg constantCoeff (hinj h')
    simp [show MvPowerSeries.constantCoeff (w W : R1) = 0 from cc_w W] at this
  have m : ∀ {x y : R1}, x = y → ι x = ι y := fun h => by rw [h]
  have key := psi_field (ι (C W.a₁)) (ι (C W.a₂)) (ι (C W.a₃)) (ι (C W.a₄)) (ι (C W.a₆))
    (ι (X ())) (ι w₁) (ι (E0 (lam W))) (ι (E1 (lam W))) (ι (E1 (nu W))) (ι (E0 (leadInv W)))
    (ι (E1 (leadInv W))) (ι (E0 (z3 W))) (ι (E1 (z3 W))) (ι (E0 (dInv W))) (ι (E1 (dInv W))) hT hδ
    (by simpa only [map_add, map_sub, map_mul, map_pow, map_zero] using m (G_T W))
    (by simpa only [map_mul] using m (r1 W))
    (by simpa only [map_mul] using m (r2 W))
    (by simpa only [map_mul, map_neg] using m (r4 W))
    (by simpa only [map_add, map_mul, map_pow, map_one] using m (r5 W))
    (by simpa only [map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] using m (r6 W))
    (by simpa only [map_add, map_sub, map_neg, map_mul, map_pow] using m (r7 W))
    (by simpa only [map_add, map_sub, map_neg, map_mul, map_pow, map_one, map_ofNat] using m (r8 W))
    (by simpa only [map_add, map_sub, map_mul, map_one] using m (r13 W))
    (by simpa only [map_add, map_sub, map_mul, map_one, map_zero] using m (r14 W))
  apply hinj
  rw [E1_F]
  simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] using key

/-! ### Base change and the general case -/

lemma pd_map' {S : Type*} [CommRing S] (f : R →+* S) {σ : Type*} [DecidableEq σ] (i : σ)
    (g : MvPowerSeries σ R) : MvPowerSeries.map f (pd i g) = pd i (MvPowerSeries.map f g) := by
  ext e
  simp [coeff_pd, coeff_map]

lemma map_E1 {S : Type*} [CommRing S] (f : R →+* S) (g : A₂) :
    MvPowerSeries.map f (E1 g) = E1 (MvPowerSeries.map f g) := by
  rw [E1, E1, map_subst (FGL.hs hv0), pd_map']
  congr 1
  funext i; fin_cases i <;> simp

/-- **the invariant differential of `F_W`**: `Ψ(T) = (∂₂F_W)(T, 0) = -(∂G/∂w)(T, w(T))`, i.e.
`ω = dT / (1 - a₁T - a₂T² - 2a₃w - 2a₄Tw - 3a₆w²)`. -/
theorem Ψ_formalGroup : FGL.Ψ (formalGroup W) (FGL.T : R1) = 1 - C W.a₁ * X () - C W.a₂ * X () ^ 2 -
    2 * C W.a₃ * w₁ - 2 * C W.a₄ * X () * w₁ - 3 * C W.a₆ * w₁ ^ 2 := by
  rw [Ψ_eq_E1, F_eq_map, ← map_E1, E1_F_domain]
  have hw : MvPowerSeries.map (spec W) (w Wu : MvPowerSeries Unit Ru) = w₁ := by
    have := map_w Wu (spec W)
    rw [Wu_map_spec] at this
    exact this
  simp only [map_sub, map_mul, map_one, map_pow, map_ofNat, map_C, map_X, hw]
  simp [Wu, spec]

/-- **Silverman's form**: `Ψ(T) · (w - T w') = w (-2 + a₁ T + a₃ w)`, i.e.
`dT/Ψ(T) = dx / (2y + a₁x + a₃)` with `x = T/w`, `y = -1/w`. -/
theorem Ψ_mul_eq : FGL.Ψ (formalGroup W) (FGL.T : R1) * (w₁ - X () * pd () w₁) =
    w₁ * (-2 + C W.a₁ * X () + C W.a₃ * w₁) := by
  have hG := G_T W
  have hd := congrArg (pd ()) hG
  simp only [pd_add, pd_sub, pd_mul, pow_succ, pow_zero, one_mul, pd_C, FGL.pd_X', if_true,
    FGL.pd_zero', show pd () (1 : R1) = 0 from by rw [← map_one (C (σ := Unit) (R := R)), pd_C]] at hd
  rw [Ψ_formalGroup]
  linear_combination (X () : R1) * hd - 3 * hG

end EllipticFormal
