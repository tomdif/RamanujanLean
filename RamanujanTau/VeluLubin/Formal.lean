/-
# The formal Vélu map (steps 1–2 of the Vélu–Lubin link)

`K` a field, `E : y² = x³ + Ax + B` (`Velu.short A B`), `κ` Vélu kernel data (a finite subgroup
`G ⊂ E(K)` without 2-torsion and a half-system `S`), `E' = κ.curve : y² = x³ + A'x + B'`.

In the formal parameter `z = -x/y` of `E` (so `x = z/w`, `y = -1/w`, `w = w_E(z) = z³ v(z)`):
* `rQ Q = 1/(x - x_Q) = z² v / (1 - x_Q z² v) ∈ K⟦z⟧` (`eQ_mul_rQ`: `(z - x_Q w)·r_Q = w`);
* Vélu's `X = x + S1`, `S1 = Σ_Q (t_Q r_Q + u_Q r_Q²)`, and `X' = Xd = 1 - Σ_Q (t_Q r_Q² + 2u_Q r_Q³)`;
* the **formal Vélu series** `φ = -X/Y = (z + w S1)/Xd ∈ K⟦z⟧` and `w' = -1/Y = w/Xd`.

Main results:
* `G_phi`: `(φ, w')` satisfies the `(z,w)`-equation of `E'`; hence `w' = w_{E'}(φ)` (`wphi_eq`);
* `phi_invariant`: `φ'(z)·Ψ_E(z) = Ψ_{E'}(φ(z))`, i.e. `φ^*ω' = ω` (from the chain rule
  `w²·r_Q' = -r_Q²·(w - z w')`, the `z`-form of `d(1/(x-x_Q)) = -dx/(x-x_Q)²`);
* `velu_formal_hom` (char 0): `φ` is a homomorphism of formal groups `F_E → F_{E'}` over `K`
  with `φ(0) = 0` and `φ'(0) = 1`.
-/
import RamanujanTau.EllipticI2.LogHom
import RamanujanTau.Velu.All

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries EllipticFormal

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

local notation "K1" => MvPowerSeries Unit K
local notation "T" => (X () : MvPowerSeries Unit K)

/-- `w_E(z)` for `E = short A B`. -/
noncomputable abbrev ww (A B : K) : K1 := (w (Velu.short A B) : K1)
/-- `v_E(z)`, `w = z³ v`. -/
noncomputable abbrev vv (A B : K) : K1 := (v (Velu.short A B) : K1)

lemma ww_eq : ww A B = T ^ 3 * vv A B := w_eq_X3_mul_v _

lemma cc_vv : constantCoeff (vv A B) = 1 := cc_v _

lemma cc_ww : constantCoeff (ww A B) = 0 := cc_w _

/-- the `(z,w)`-equation of `E`: `z³ + A z w² + B w³ - w = 0`. -/
lemma G_ww : T ^ 3 + C A * T * ww A B ^ 2 + C B * ww A B ^ 3 - ww A B = 0 := by
  have h := G_T (Velu.short A B)
  simpa using h

/-- `e_Q = z - x_Q w` (so `x - x_Q = e_Q / w`). -/
noncomputable def eQ (Q : (Velu.short A B).Point) : K1 := T - C (Velu.xc Q) * ww A B

/-- the unit `1 - x_Q z² v`. -/
noncomputable def uQs (Q : (Velu.short A B).Point) : K1 := 1 - C (Velu.xc Q) * T ^ 2 * vv A B

lemma cc_uQs (Q : (Velu.short A B).Point) : constantCoeff (uQs Q) = 1 := by
  simp [uQs]

/-- `r_Q = 1/(x - x_Q) = z² v / (1 - x_Q z² v)`. -/
noncomputable def rQ (Q : (Velu.short A B).Point) : K1 := T ^ 2 * vv A B * (uQs Q)⁻¹

lemma uQs_mul_inv (Q : (Velu.short A B).Point) : uQs Q * (uQs Q)⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel _ (by rw [cc_uQs]; exact one_ne_zero)

lemma cc_rQ (Q : (Velu.short A B).Point) : constantCoeff (rQ Q) = 0 := by
  simp [rQ]

lemma eQ_eq (Q : (Velu.short A B).Point) : eQ Q = T * uQs Q := by
  rw [eQ, uQs, ww_eq]; ring

theorem eQ_mul_rQ (Q : (Velu.short A B).Point) : eQ Q * rQ Q = ww A B := by
  rw [eQ_eq, rQ, ww_eq]
  linear_combination (T ^ 3 * vv A B) * uQs_mul_inv Q

variable (κ : Velu.Kernel A B)

/-- `S1 = Σ_Q (t_Q r_Q + u_Q r_Q²)`, so that Vélu's `X = x + S1`. -/
noncomputable def S1 : K1 :=
  ∑ Q ∈ κ.S, (C (Velu.Kernel.tQ Q) * rQ Q + C (Velu.Kernel.uQ Q) * rQ Q ^ 2)

/-- `Xd = 1 - Σ_Q (t_Q r_Q² + 2 u_Q r_Q³)` (Vélu's `X'(x)`). -/
noncomputable def Xd : K1 :=
  1 - ∑ Q ∈ κ.S, (C (Velu.Kernel.tQ Q) * rQ Q ^ 2 + 2 * C (Velu.Kernel.uQ Q) * rQ Q ^ 3)

lemma cc_Xd : constantCoeff (Xd κ) = 1 := by
  simp [Xd, cc_rQ]

lemma Xd_mul_inv : Xd κ * (Xd κ)⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel _ (by rw [cc_Xd]; exact one_ne_zero)

/-- `z + w S1` (`= w · X`). -/
noncomputable def Pn : K1 := T + ww A B * S1 κ

/-- **the formal Vélu series** `φ = -X/Y = (z + w S1)/Xd`. -/
noncomputable def phi : K1 := Pn κ * (Xd κ)⁻¹

/-- `w' = -1/Y = w/Xd`. -/
noncomputable def wphi : K1 := ww A B * (Xd κ)⁻¹

lemma cc_phi : constantCoeff (phi κ) = 0 := by
  simp [phi, Pn, cc_ww]

lemma cc_wphi : constantCoeff (wphi κ) = 0 := by
  simp [wphi, cc_ww]


/-! ### Vélu's curve equation for `(φ, w')`, via the fraction field of `K⟦z⟧` -/

section Frac

local notation "L" => FractionRing (MvPowerSeries Unit K)

instance instIsDomainK1 : IsDomain (MvPowerSeries Unit K) := NoZeroDivisors.to_isDomain _

local notation "ι" => algebraMap (MvPowerSeries Unit K) (FractionRing (MvPowerSeries Unit K))

lemma ι_inj' {a b : K1} (h : ι a = ι b) : a = b := IsFractionRing.injective _ _ h

lemma ww_ne_zero : ww A B ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single () 3)) h
  rw [show coeff (Finsupp.single () 3) (ww A B) = PowerSeries.coeff 3 (w (Velu.short A B)) from rfl,
    coeff_three_w] at this
  simp at this

lemma ι_ww_ne : ι (ww A B) ≠ 0 := fun h => ww_ne_zero (ι_inj' (h.trans (map_zero ι).symm))

/-- the ring hom `K → L`. -/
noncomputable abbrev jj : K →+* FractionRing (MvPowerSeries Unit K) :=
  (algebraMap (MvPowerSeries Unit K) (FractionRing (MvPowerSeries Unit K))).comp
    (C (σ := Unit) (R := K))

lemma jj_apply (c : K) : jj c = ι (C c) := rfl

/-- `x = z / w` in `L`. -/
noncomputable abbrev xL (A B : K) : FractionRing (MvPowerSeries Unit K) := ι T / ι (ww A B)

lemma x_sub_mul_r (Q : (Velu.short A B).Point) : (xL A B - jj (Velu.xc Q)) * ι (rQ Q) = 1 := by
  have hw := ι_ww_ne (A := A) (B := B)
  have h := congrArg ι (eQ_mul_rQ Q)
  rw [eQ, map_mul, map_sub, map_mul] at h
  simp only [xL, jj_apply]
  field_simp
  linear_combination h

lemma f_xL : xL A B ^ 3 + jj A * xL A B + jj B = 1 / ι (ww A B) ^ 2 := by
  have hw := ι_ww_ne (A := A) (B := B)
  have h := congrArg ι (G_ww (A := A) (B := B))
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
  simp only [xL, jj_apply]
  field_simp
  linear_combination h

/-- evaluation of polynomials at `x`. -/
noncomputable abbrev evx (A B : K) : Polynomial K →+* FractionRing (MvPowerSeries Unit K) :=
  Polynomial.eval₂RingHom jj (xL A B)

lemma evx_X : evx A B Polynomial.X = xL A B := Polynomial.eval₂_X _ _

lemma evx_C (c : K) : evx A B (Polynomial.C c) = ι (C c) := Polynomial.eval₂_C _ _

lemma evx_vp (Q : (Velu.short A B).Point) :
    evx A B (Velu.Kernel.vp Q) = xL A B - jj (Velu.xc Q) := by
  rw [Velu.Kernel.vp, map_sub, evx_X, evx_C, jj_apply]

lemma evx_D_ne : evx A B κ.D ≠ 0 := by
  rw [Velu.Kernel.D, map_prod]
  refine Finset.prod_ne_zero_iff.2 fun Q _ => ?_
  rw [evx_vp]
  intro h
  have := x_sub_mul_r (A := A) (B := B) Q
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma evx_Dq {Q : (Velu.short A B).Point} (hQ : Q ∈ κ.S) :
    evx A B (κ.Dq Q) = evx A B κ.D * ι (rQ Q) := by
  rw [κ.D_eq hQ, map_mul, evx_vp]
  linear_combination (-(evx A B (κ.Dq Q))) * x_sub_mul_r Q

/-- `X(x) = x + S1` in `L`. -/
noncomputable abbrev XL : FractionRing (MvPowerSeries Unit K) := xL A B + ι (S1 κ)

lemma evx_N : evx A B κ.N = evx A B κ.D ^ 2 * XL κ := by
  rw [Velu.Kernel.N, XL, S1, map_add, map_mul, map_pow, map_sum, map_sum, evx_X, mul_add,
    Finset.mul_sum]
  congr 1
  · ring
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [map_mul, map_pow, evx_Dq κ hQ, map_add, map_mul, evx_vp, evx_C, evx_C]
  have h := x_sub_mul_r (A := A) (B := B) Q
  simp only [map_add, map_mul, map_pow]
  linear_combination (ι (C (Velu.Kernel.tQ Q)) * evx A B κ.D ^ 2 * ι (rQ Q)) * h

/-- `Xd` in `L`. -/
lemma evx_N1 : evx A B κ.N1 = evx A B κ.D ^ 3 * ι (Xd κ) := by
  rw [Velu.Kernel.N1, Xd, map_sub, map_pow, map_sum, map_sub, map_one, map_sum, mul_sub, mul_one,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [map_mul, map_pow, evx_Dq κ hQ, map_add, map_mul, map_mul, evx_vp, evx_C, evx_C]
  have h := x_sub_mul_r (A := A) (B := B) Q
  simp only [map_add, map_mul, map_pow, map_ofNat]
  linear_combination (ι (C (Velu.Kernel.tQ Q)) * evx A B κ.D ^ 3 * ι (rQ Q) ^ 2) * h

/-- **Vélu's equation in `L`**: `y² Xd² = X³ + A' X + B'`. -/
lemma velu_L (h2 : (2 : K) ≠ 0) :
    1 / ι (ww A B) ^ 2 * ι (Xd κ) ^ 2 = XL κ ^ 3 + jj κ.A' * XL κ + jj κ.B' := by
  have hP := congrArg (evx A B) (κ.Pv_eq_zero h2)
  rw [Velu.Kernel.Pv, map_zero, map_sub, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow, map_pow, evx_N, evx_N1, Velu.Kernel.fpoly] at hP
  simp only [map_add, map_mul, map_pow, evx_X, evx_C] at hP
  rw [← f_xL]
  have hD := evx_D_ne κ (A := A) (B := B)
  have hD6 : evx A B κ.D ^ 6 ≠ 0 := pow_ne_zero 6 hD
  apply mul_left_cancel₀ hD6
  simp only [jj_apply]
  linear_combination hP

/-- **Vélu's equation in `K⟦z⟧`**: `w Xd² = (z + w S1)³ + A' (z + w S1) w² + B' w³`. -/
theorem velu_series (h2 : (2 : K) ≠ 0) :
    ww A B * Xd κ ^ 2 =
      Pn κ ^ 3 + C κ.A' * Pn κ * ww A B ^ 2 + C κ.B' * ww A B ^ 3 := by
  apply ι_inj'
  have h := velu_L κ h2
  have hw := ι_ww_ne (A := A) (B := B)
  rw [Pn]
  simp only [map_add, map_mul, map_pow]
  simp only [jj_apply] at h
  field_simp at h
  linear_combination h

end Frac

/-! ### `w' = w_{E'}(φ)` -/

/-- the inverse `1/Xd`. -/
noncomputable abbrev Ii : K1 := (Xd κ)⁻¹

/-- **`(φ, w')` lies on `E'`** in `(z,w)`-coordinates. -/
theorem G_phi (h2 : (2 : K) ≠ 0) : G (WM κ.curve Unit) (phi κ) (wphi κ) = 0 := by
  have e := velu_series κ h2
  have hI := Xd_mul_inv κ
  simp only [G, WM, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Velu.Kernel.curve, Velu.short_a₁,
    Velu.short_a₂, Velu.short_a₃, Velu.short_a₄, Velu.short_a₆, map_zero, phi, wphi]
  linear_combination (-(Ii κ) ^ 3) * e + (ww A B * Ii κ * (Ii κ * Xd κ + 1)) * hI

/-- **`w' = w_{E'}(φ)`**. -/
theorem wphi_eq (h2 : (2 : K) ≠ 0) : wphi κ = wt κ.curve (phi κ) :=
  G_unique (WM κ.curve Unit) (cc_phi κ) (cc_wphi κ) (cc_wt (cc_phi κ)) (G_phi κ h2) (G_wt (cc_phi κ))

/-! ### The invariant differential -/

local notation "d" => pd ()

lemma pd_sum' {ι : Type*} (s : Finset ι) (f : ι → K1) : d (∑ i ∈ s, f i) = ∑ i ∈ s, d (f i) :=
  map_sum (pdDer (R := K) ()) f s

lemma pd_T : d T = 1 := by rw [pd_X]; simp

/-- `δ = w - z w'` (`dx/dz = δ/w²`). -/
noncomputable abbrev δ (A B : K) : K1 := ww A B - T * d (ww A B)

lemma T_ne_zero : T ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single () 1)) h
  simp at this

lemma eQ_ne_zero (Q : (Velu.short A B).Point) : eQ Q ≠ 0 := by
  rw [eQ_eq]
  refine mul_ne_zero T_ne_zero fun h => ?_
  have := cc_uQs Q
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- **`d(1/(x - x_Q)) = -dx/(x-x_Q)²`** in the parameter `z`: `w² r_Q' = -r_Q² δ`. -/
theorem pd_rQ (Q : (Velu.short A B).Point) : ww A B ^ 2 * d (rQ Q) = -(rQ Q ^ 2 * δ A B) := by
  have hE := eQ_mul_rQ Q
  have hd := congrArg d hE
  rw [pd_mul] at hd
  have hde : d (eQ Q) = 1 - C (Velu.xc Q) * d (ww A B) := by
    rw [eQ, pd_sub, pd_mul, pd_C, pd_T]; ring
  rw [hde] at hd
  have key : eQ Q * (ww A B ^ 2 * d (rQ Q) + rQ Q ^ 2 * δ A B) = 0 := by
    have he : eQ Q = T - C (Velu.xc Q) * ww A B := rfl
    linear_combination (ww A B ^ 2) * hd + (rQ Q * δ A B - ww A B * d (ww A B)) * hE +
      (ww A B * d (ww A B) * rQ Q) * he
  have := (mul_eq_zero.1 key).resolve_left (eQ_ne_zero Q)
  linear_combination this

lemma pd_S1 : ww A B ^ 2 * d (S1 κ) = δ A B * (Xd κ - 1) := by
  rw [S1, pd_sum', Finset.mul_sum, Xd, sub_sub_cancel_left, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  have h := pd_rQ (A := A) (B := B) Q
  rw [pd_add, pd_mul, pd_mul, pd_C, pd_C, show rQ Q ^ 2 = rQ Q * rQ Q by ring, pd_mul]
  linear_combination (C (Velu.Kernel.tQ Q) + 2 * C (Velu.Kernel.uQ Q) * rQ Q) * h

lemma key_Pn : ww A B * d (Pn κ) - Pn κ * d (ww A B) = δ A B * Xd κ := by
  have h := pd_S1 κ
  rw [Pn, pd_add, pd_mul, pd_T]
  linear_combination h

lemma key_phi : wphi κ * d (phi κ) - phi κ * d (wphi κ) = δ A B * Ii κ := by
  have h := key_Pn κ
  have hI := Xd_mul_inv κ
  rw [phi, wphi, pd_mul, pd_mul]
  linear_combination (Ii κ) ^ 2 * h + δ A B * Ii κ * hI

lemma coeff_three_δ : coeff (Finsupp.single () 3) (δ A B) = -2 := by
  have h3 : coeff (Finsupp.single () 3) (ww A B) = 1 := coeff_three_w _
  have h3' : coeff (Finsupp.single () 3) (T * d (ww A B)) = 3 := by
    show PowerSeries.coeff 3 (PowerSeries.X * d (ww A B)) = 3
    rw [PowerSeries.coeff_succ_X_mul]
    show coeff (Finsupp.single () 2) (d (ww A B)) = 3
    rw [coeff_pd, show (Finsupp.single () 2 + Finsupp.single () 1 : Unit →₀ ℕ) = Finsupp.single () 3 by
      rw [← Finsupp.single_add], h3]
    simp; norm_num
  rw [map_sub, h3, h3']; norm_num

lemma δ_ne_zero (h2 : (2 : K) ≠ 0) : δ A B ≠ 0 := by
  intro h
  have := coeff_three_δ (A := A) (B := B)
  rw [h, map_zero] at this
  exact h2 (by linear_combination this)

/-- `Ψ_E(z)·δ = -2w`. -/
lemma Ψ_E : FGL.Ψ (formalGroup (Velu.short A B)) T * δ A B = -2 * ww A B := by
  have h := Ψ_mul_eq (Velu.short A B)
  simp only [Velu.short_a₁, Velu.short_a₃, map_zero, zero_mul, add_zero] at h
  rw [δ]; linear_combination h

omit [DecidableEq K] in
/-- `subst` of `Ψ(T)` (copy of `EllipticI2.Log.subst_Ψ` without `Algebra ℚ`). -/
lemma subst_Ψ' {R : Type*} [CommRing R] (F : FormalGroup R) {a : MvPowerSeries Unit R}
    (ha : constantCoeff a = 0) :
    subst (fun _ : Unit => a) (FGL.Ψ F (FGL.T : MvPowerSeries Unit R)) = FGL.Ψ F a := by
  have hv : ∀ s, constantCoeff ((![FGL.T, 0] : Fin 2 → MvPowerSeries Unit R) s) = 0 := FGL.cc_T0
  show subst _ (subst ![FGL.T, 0] (pd 1 F.toPowerSeries)) = subst ![a, 0] (pd 1 F.toPowerSeries)
  rw [FGL.ss _ _ hv (fun _ => ha)]
  congr 1; funext s; fin_cases s
  · exact FGL.sX _ (fun _ => ha) ()
  · exact FGL.s0 _ (fun _ => ha)

/-- `Ψ_{E'}(φ)·(w' - φ·w_{E'}'(φ)) = -2w'`. -/
lemma Ψ_E'_phi (h2 : (2 : K) ≠ 0) :
    FGL.Ψ (formalGroup κ.curve) (phi κ) *
      (wphi κ - phi κ * subst (fun _ : Unit => phi κ) (d (w κ.curve : K1))) = -2 * wphi κ := by
  have h := Ψ_mul_eq κ.curve
  simp only [show κ.curve.a₁ = 0 from rfl, show κ.curve.a₃ = 0 from rfl, map_zero, zero_mul,
    add_zero] at h
  have hc : ∀ _ : Unit, constantCoeff ((fun _ : Unit => phi κ) ()) = 0 := fun _ => cc_phi κ
  have hs := congrArg (subst (fun _ : Unit => phi κ)) h
  have hw : subst (fun _ : Unit => phi κ) (w κ.curve : K1) = wphi κ := by
    rw [wphi_eq κ h2, wt, PowerSeries.subst_def]
  rw [subst_mul (FGL.hs hc), subst_mul (FGL.hs hc), subst_sub (FGL.hs hc), subst_mul (FGL.hs hc),
    subst_Ψ' _ (cc_phi κ), FGL.sX _ hc, hw] at hs
  have h2s : subst (fun _ : Unit => phi κ) (-2 : K1) = -2 := by
    rw [← coe_substAlgHom (FGL.hs hc), map_neg, map_ofNat]
  rw [h2s] at hs
  linear_combination hs

/-- chain rule `d(w_{E'}(φ)) = w_{E'}'(φ)·φ'`. -/
lemma pd_wphi (h2 : (2 : K) ≠ 0) :
    d (wphi κ) = subst (fun _ : Unit => phi κ) (d (w κ.curve : K1)) * d (phi κ) := by
  rw [wphi_eq κ h2, wt, PowerSeries.subst_def, pd_subst (fun _ => cc_phi κ), Fintype.sum_unique]

/-- **`φ^*ω' = ω`**: `φ'(z)·Ψ_E(z) = Ψ_{E'}(φ(z))`. -/
theorem phi_invariant (h2 : (2 : K) ≠ 0) :
    d (phi κ) * FGL.Ψ (formalGroup (Velu.short A B)) T = FGL.Ψ (formalGroup κ.curve) (phi κ) := by
  have h1 := Ψ_E'_phi κ h2
  have hc := pd_wphi κ h2
  have hk := key_phi κ
  have hE := Ψ_E (A := A) (B := B)
  have hI := Xd_mul_inv κ
  set D' := subst (fun _ : Unit => phi κ) (d (w κ.curve : K1))
  have hIne : Ii κ ≠ 0 := by intro h; rw [Ii] at h; rw [h, mul_zero] at hI; exact zero_ne_one hI
  have key : (d (phi κ) * FGL.Ψ (formalGroup (Velu.short A B)) T -
      FGL.Ψ (formalGroup κ.curve) (phi κ)) * (δ A B * Ii κ) = 0 := by
    rw [hc] at hk
    have hw : wphi κ = ww A B * Ii κ := rfl
    linear_combination (d (phi κ) * Ii κ) * hE + FGL.Ψ (formalGroup κ.curve) (phi κ) * hk -
      d (phi κ) * h1 + 2 * d (phi κ) * hw
  have := (mul_eq_zero.1 key).resolve_right (mul_ne_zero (δ_ne_zero h2) hIne)
  linear_combination this

/-- `φ'(0) = 1`. -/
theorem lie_phi : coeff (Finsupp.single () 1) (phi κ) = 1 := by
  have hw1 : coeff (Finsupp.single () 1) (ww A B) = 0 := coeff_w_of_lt _ (by norm_num)
  have hI0 : constantCoeff (Xd κ)⁻¹ = 1 := by
    rw [MvPowerSeries.constantCoeff_inv, cc_Xd, inv_one]
  rw [phi, lin_mul, Pn]
  simp only [map_add, lin_mul, hI0, cc_ww, hw1, lin_X]
  simp [cc_ww]

/-- **the formal Vélu map is a homomorphism** `F_E → F_{E'}` (characteristic `0`). -/
theorem velu_formal_hom [CharZero K] :
    EllipticI2.Hom (formalGroup (Velu.short A B)) (formalGroup κ.curve) (phi κ) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine EllipticI2.Log.hom_of_invariant _ _ (phi κ) (cc_phi κ) ?_
  rw [lie_phi, map_one, mul_one]
  exact phi_invariant κ h2

end VeluLubin
