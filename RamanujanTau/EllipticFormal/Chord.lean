/-
# The chord construction of the formal group law of a Weierstrass curve (Silverman, AEC IV.1)

Over any commutative ring `R`, in `R⟦z₁, z₂⟧` (variables `X 0`, `X 1`):
* `w(t)` for any power series `t` without constant term (`wt`), with `G(t, w(t)) = 0`;
* the slope `λ` with coefficients `λ_{ij} = A_{i+j+1}` (`w = Σ Aₙ zⁿ`), so `(z₂ - z₁) λ = w(z₂) - w(z₁)`;
* `ν = w(z₁) - λ z₁`, the third root `z₃ = -z₁ - z₂ - B/lead` of `G(z, λz + ν)`,
  `w₃ = λ z₃ + ν`, and `F = z₃ / (a₁ z₃ + a₃ w₃ - 1)` (= the `z`-coordinate of `-(z₃, w₃)`).
We prove `F(0,0) = 0`, the linear coefficients of `F` are `1, 1`, and `F` commutes with base change.
-/
import RamanujanTau.EllipticFormal.W
import RamanujanTau.FormalGroupLayer.Basic

set_option autoImplicit false

namespace EllipticFormal

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- leading coefficient of `G(z, l z + n)` as a cubic in `z`. -/
def lead {S : Type*} [CommRing S] (W : WeierstrassCurve S) (l : S) : S :=
  1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3

/-- the `z²`-coefficient of `G(z, l z + n)`. -/
def B {S : Type*} [CommRing S] (W : WeierstrassCurve S) (l n : S) : S :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n

/-- the `z`-coefficient of `G(z, l z + n)`. -/
def Cz {S : Type*} [CommRing S] (W : WeierstrassCurve S) (l n : S) : S :=
  W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l

/-- the constant coefficient of `G(z, l z + n)`. -/
def Dz {S : Type*} [CommRing S] (W : WeierstrassCurve S) (n : S) : S :=
  W.a₃ * n ^ 2 + W.a₆ * n ^ 3 - n

lemma G_line {S : Type*} [CommRing S] (W : WeierstrassCurve S) (l n z : S) :
    G W z (l * z + n) = lead W l * z ^ 3 + B W l n * z ^ 2 + Cz W l n * z + Dz W n := by
  simp only [G, lead, B, Cz, Dz]; ring

/-- **the third root** (in any domain): if `s ≠ t` are roots of `G(z, l z + n)` and
`lead·(s + t + z) + B = 0`, then `z` is a root too. -/
theorem G_third {S : Type*} [CommRing S] [NoZeroDivisors S] (W : WeierstrassCurve S)
    {l n s t z : S} (hs : G W s (l * s + n) = 0) (ht : G W t (l * t + n) = 0) (hst : s ≠ t)
    (h3 : lead W l * (s + t + z) + B W l n = 0) : G W z (l * z + n) = 0 := by
  rw [G_line] at hs ht ⊢
  have hQ : lead W l * (s ^ 2 + s * t + t ^ 2) + B W l n * (s + t) + Cz W l n = 0 := by
    have : (s - t) * (lead W l * (s ^ 2 + s * t + t ^ 2) + B W l n * (s + t) + Cz W l n) = 0 := by
      linear_combination hs - ht
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hst)
  linear_combination hs + (z - s) * hQ + (z - s) * (z - t) * h3

/-- the negation map `(z, w) ↦ (z e, w e)`, `e = 1/(a₁ z + a₃ w - 1)`, preserves `G = 0`. -/
lemma G_neg {S : Type*} [CommRing S] (W : WeierstrassCurve S) (z w e : S)
    (he : (W.a₁ * z + W.a₃ * w - 1) * e = 1) : G W (z * e) (w * e) = e ^ 3 * G W z w := by
  simp only [G]
  linear_combination (-e * w * (e - 1)) * he

/-! ## `w(t)` -/

section Wt
variable (W : WeierstrassCurve R) {σ : Type*}

/-- the curve over `R⟦σ⟧`. -/
noncomputable abbrev WM (σ : Type*) : WeierstrassCurve (MvPowerSeries σ R) :=
  W.map (MvPowerSeries.C (σ := σ) (R := R))

/-- `w(t)`. -/
noncomputable def wt (t : MvPowerSeries σ R) : MvPowerSeries σ R := PowerSeries.subst t (w W)

variable {W}

lemma cc_wt {t : MvPowerSeries σ R} (ht : constantCoeff t = 0) : constantCoeff (wt W t) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ht _ (cc_w W)

lemma WM_map_eq {τ : Type*} (φ : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R) :
    (WM W σ).map (φ : MvPowerSeries σ R →+* MvPowerSeries τ R) = WM W τ := by
  simp only [WM, WeierstrassCurve.map_map]
  congr 1
  ext r : 1
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [c_eq_algebraMap, c_eq_algebraMap]; exact φ.commutes r

lemma WC_map_eq {τ : Type*} (φ : PowerSeries R →ₐ[R] MvPowerSeries τ R) :
    (WC W).map (φ : PowerSeries R →+* MvPowerSeries τ R) = WM W τ := by
  simp only [WC, WM, WeierstrassCurve.map_map]
  congr 1
  ext r : 1
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [← PowerSeries.algebraMap_eq, c_eq_algebraMap]; exact φ.commutes r

theorem G_wt {t : MvPowerSeries σ R} (ht : constantCoeff t = 0) : G (WM W σ) t (wt W t) = 0 := by
  have hs : PowerSeries.HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero ht
  have h := congrArg ((PowerSeries.substAlgHom hs : PowerSeries R →ₐ[R] MvPowerSeries σ R) :
    PowerSeries R →+* MvPowerSeries σ R) (G_w W)
  rw [map_G, map_zero, WC_map_eq] at h
  simpa [PowerSeries.substAlgHom_X, wt, PowerSeries.coe_substAlgHom] using h

/-- `w(t) = t³ · v(t)` with `v(t) ≡ 1`. -/
theorem wt_eq {t : MvPowerSeries σ R} (ht : constantCoeff t = 0) :
    wt W t = t ^ 3 * PowerSeries.subst t (v W) := by
  have hs : PowerSeries.HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero ht
  rw [wt, w_eq_X3_mul_v, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]

lemma cc_subst_v [Finite σ] {t : MvPowerSeries σ R} (ht : constantCoeff t = 0) :
    constantCoeff (PowerSeries.subst t (v W)) = 1 := by
  rw [PowerSeries.subst_def, FGL.cc_subst _ (fun _ => ht)]
  exact cc_v W

/-- substituting into `w(t)`. -/
lemma subst_wt [Finite σ] {τ : Type*} [Finite τ] {t : MvPowerSeries σ R} (ht : constantCoeff t = 0)
    (b : σ → MvPowerSeries τ R) (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (wt W t) = wt W (subst b t) := by
  rw [wt, PowerSeries.subst_def, FGL.ss (fun _ : Unit => t) b (fun _ => ht) hb, wt,
    PowerSeries.subst_def]

lemma map_wt {S : Type*} [CommRing S] (f : R →+* S) {t : MvPowerSeries σ R}
    (ht : constantCoeff t = 0) : MvPowerSeries.map f (wt W t) = wt (W.map f) (MvPowerSeries.map f t) := by
  rw [wt, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero ht), map_w, wt]

lemma wt_ne_zero [Finite σ] [IsDomain R] {t : MvPowerSeries σ R} (ht : constantCoeff t = 0) (h0 : t ≠ 0) :
    wt W t ≠ 0 := by
  rw [wt_eq ht]
  refine mul_ne_zero (pow_ne_zero 3 h0) fun h => ?_
  have := cc_subst_v (W := W) ht
  rw [h, map_zero] at this
  exact zero_ne_one this

end Wt

/-! ## Linear coefficients -/

section Lin
variable {σ : Type*} [DecidableEq σ]

lemma lin_eq (i : σ) (f : MvPowerSeries σ R) :
    coeff (Finsupp.single i 1) f = constantCoeff (pd i f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd]; simp

lemma lin_mul (i : σ) (f g : MvPowerSeries σ R) : coeff (Finsupp.single i 1) (f * g) =
    constantCoeff f * coeff (Finsupp.single i 1) g + coeff (Finsupp.single i 1) f * constantCoeff g := by
  rw [lin_eq, lin_eq, lin_eq, pd_mul]; simp only [map_add, map_mul]; ring

lemma lin_C (i : σ) (r : R) : coeff (Finsupp.single i 1) (C r : MvPowerSeries σ R) = 0 := by
  rw [lin_eq, pd_C]; simp

lemma lin_one (i : σ) : coeff (Finsupp.single i 1) (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one (C (σ := σ) (R := R)), lin_C]

lemma lin_X (i j : σ) : coeff (Finsupp.single i 1) (X j : MvPowerSeries σ R) = if j = i then 1 else 0 := by
  rw [lin_eq, pd_X]; split_ifs <;> simp

/-- chain rule at the origin for linear coefficients. -/
lemma lin_subst2 [Fintype σ] (f : MvPowerSeries (Fin 2) R) (s t : MvPowerSeries σ R)
    (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) (i : σ) :
    coeff (Finsupp.single i 1) (subst ![s, t] f) =
      coeff (Finsupp.single 0 1) f * coeff (Finsupp.single i 1) s +
      coeff (Finsupp.single 1 1) f * coeff (Finsupp.single i 1) t := by
  have hv := FGL.cc_vec2 hs ht
  rw [lin_eq, pd_subst hv, Fin.sum_univ_two, map_add, map_mul, map_mul, FGL.cc_subst _ hv,
    FGL.cc_subst _ hv, ← lin_eq, ← lin_eq, ← lin_eq, ← lin_eq]
  rfl

end Lin

/-! ## The two-variable construction -/

section Chord
variable (W : WeierstrassCurve R)

local notation "A₂" => MvPowerSeries (Fin 2) R
local notation "W₂" => WM W (Fin 2)

/-- the slope `λ(z₁, z₂) = Σ Aₙ (z₁^{n-1} + z₁^{n-2} z₂ + ⋯ + z₂^{n-1})`. -/
noncomputable def lam : A₂ := fun e => PowerSeries.coeff (e 0 + e 1 + 1) (w W)

lemma coeff_lam (e : Fin 2 →₀ ℕ) : coeff e (lam W) = PowerSeries.coeff (e 0 + e 1 + 1) (w W) := rfl

lemma cc_lam : constantCoeff (lam W) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_lam]
  exact coeff_w_of_lt W (by simp)

lemma lin_lam (i : Fin 2) : coeff (Finsupp.single i 1) (lam W) = 0 := by
  rw [coeff_lam]
  apply coeff_w_of_lt W
  fin_cases i <;> simp

lemma coeff_X_mul' (i : Fin 2) (f : A₂) (e : Fin 2 →₀ ℕ) :
    coeff e (X i * f) = if 1 ≤ e i then coeff (e - Finsupp.single i 1) f else 0 := by
  simp only [X_def, coeff_monomial_mul, Finsupp.single_le_iff, one_mul]

lemma e_eq_single_iff (e : Fin 2 →₀ ℕ) (i : Fin 2) :
    e = Finsupp.single i (e i) ↔ e (1 - i) = 0 := by
  constructor
  · intro h; rw [h]; fin_cases i <;> simp
  · intro h; ext j; fin_cases i <;> fin_cases j <;> simp_all

/-- **divided difference**: `(z₂ - z₁) λ = w(z₂) - w(z₁)`. -/
theorem lam_spec : (X 1 - X 0) * lam W = wt W (X 1 : A₂) - wt W (X 0) := by
  ext e
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_X_mul', wt, wt,
    PowerSeries.coeff_subst_single, PowerSeries.coeff_subst_single]
  simp only [e_eq_single_iff, coeff_lam]
  simp only [Finsupp.tsub_apply, Fin.isValue, Finsupp.single_eq_same,
    show (1 : Fin 2) - 1 = 0 from rfl, show (1 : Fin 2) - 0 = 1 from rfl]
  rw [Finsupp.single_eq_of_ne (by decide), Finsupp.single_eq_of_ne (by decide)]
  generalize e 0 = a
  generalize e 1 = b
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · simp
  · simp
  · simp only [Nat.add_sub_cancel, tsub_zero, le_add_iff_nonneg_left, zero_le, if_true,
      Nat.add_one_ne_zero, if_false, sub_zero]
    rw [show a + 1 + b + 1 = a + (b + 1) + 1 by omega, sub_self]

/-- `ν = w(z₁) - λ z₁`. -/
noncomputable def nu : A₂ := wt W (X 0) - lam W * X 0

lemma nu_eq_one : wt W (X 1 : A₂) = lam W * X 1 + nu W := by
  have := lam_spec W
  rw [nu]; linear_combination -this

lemma nu_eq_zero : wt W (X 0 : A₂) = lam W * X 0 + nu W := by rw [nu]; ring

lemma cc_nu : constantCoeff (nu W) = 0 := by
  rw [nu, map_sub, cc_wt (by simp), map_mul, cc_lam]; simp

lemma lin_wt_X {σ : Type*} [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (wt W (X j : MvPowerSeries σ R)) = 0 := by
  rw [wt_eq (by simp), pow_succ, pow_succ, pow_one]
  simp [lin_mul, lin_X]

lemma lin_nu (i : Fin 2) : coeff (Finsupp.single i 1) (nu W) = 0 := by
  rw [nu, map_sub, lin_wt_X, lin_mul, cc_lam, lin_lam]; simp

/-- `1/lead`. -/
noncomputable def leadInv : A₂ := invOfUnit (lead W₂ (lam W)) 1

lemma cc_lead : constantCoeff (lead W₂ (lam W)) = 1 := by
  simp [lead, cc_lam]

lemma lead_mul_leadInv : lead W₂ (lam W) * leadInv W = 1 :=
  mul_invOfUnit _ _ (by rw [cc_lead]; rfl)

/-- the third root `z₃ = -z₁ - z₂ - B/lead`. -/
noncomputable def z3 : A₂ := -X 0 - X 1 - B W₂ (lam W) (nu W) * leadInv W

lemma z3_spec : lead W₂ (lam W) * (X 0 + X 1 + z3 W) + B W₂ (lam W) (nu W) = 0 := by
  rw [z3]; linear_combination (-B W₂ (lam W) (nu W)) * lead_mul_leadInv W

lemma cc_B : constantCoeff (B W₂ (lam W) (nu W)) = 0 := by
  simp [B, cc_lam, cc_nu]

lemma lin_B (i : Fin 2) : coeff (Finsupp.single i 1) (B W₂ (lam W) (nu W)) = 0 := by
  simp only [B, map_add, lin_mul, map_mul, cc_lam, cc_nu, lin_lam, lin_nu, pow_two, mul_zero,
    add_zero]

lemma cc_z3 : constantCoeff (z3 W) = 0 := by
  simp [z3, cc_B]

lemma lin_z3 (i : Fin 2) : coeff (Finsupp.single i 1) (z3 W) = -1 := by
  rw [z3, map_sub, map_sub, map_neg, lin_mul, lin_X, lin_X, cc_B, lin_B]
  fin_cases i <;> simp

/-- `w₃ = λ z₃ + ν`. -/
noncomputable def w3 : A₂ := lam W * z3 W + nu W

lemma cc_w3 : constantCoeff (w3 W) = 0 := by simp [w3, cc_lam, cc_nu]

/-- `d = a₁ z₃ + a₃ w₃ - 1`. -/
noncomputable def dd : A₂ := (WM W (Fin 2)).a₁ * z3 W + (WM W (Fin 2)).a₃ * w3 W - 1

lemma cc_dd : constantCoeff (dd W) = -1 := by simp [dd, cc_z3, cc_w3]

/-- `1/d`. -/
noncomputable def dInv : A₂ := invOfUnit (dd W) (-1)

lemma dd_mul_dInv : dd W * dInv W = 1 := mul_invOfUnit _ _ (by rw [cc_dd]; simp)

lemma cc_dInv : constantCoeff (dInv W) = -1 := by simp [dInv]

/-- **the formal group law** `F(z₁, z₂) = i(z₃)` of the Weierstrass curve `W`. -/
noncomputable def F : A₂ := z3 W * dInv W

theorem cc_F : constantCoeff (F W) = 0 := by simp [F, cc_z3]

theorem lin_F (i : Fin 2) : coeff (Finsupp.single i 1) (F W) = 1 := by
  rw [F, lin_mul, lin_z3, cc_z3, cc_dInv]; simp

/-! ### Base change -/

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_WM {σ : Type*} : (WM W σ).map (MvPowerSeries.map f) = WM (W.map f) σ := by
  simp only [WM, WeierstrassCurve.map_map]
  congr 1
  ext r : 1
  simp

lemma map_lam : MvPowerSeries.map f (lam W) = lam (W.map f) := by
  ext e
  rw [coeff_map, coeff_lam, coeff_lam, ← map_w, PowerSeries.coeff_map]

lemma map_nu : MvPowerSeries.map f (nu W) = nu (W.map f) := by
  rw [nu, nu, map_sub, map_mul, map_lam, map_wt f (by simp), map_X]

lemma map_inv_eq {σ : Type*} {a b c : MvPowerSeries σ S} (hab : a * b = 1) (hac : a * c = 1) :
    b = c := by
  calc b = b * (a * c) := by rw [hac, mul_one]
    _ = (a * b) * c := by ring
    _ = c := by rw [hab, one_mul]

lemma map_lead : MvPowerSeries.map f (lead W₂ (lam W)) = lead (WM (W.map f) (Fin 2)) (lam (W.map f)) := by
  rw [← map_lam, ← map_WM]; simp [lead]

lemma map_B : MvPowerSeries.map f (B W₂ (lam W) (nu W)) =
    B (WM (W.map f) (Fin 2)) (lam (W.map f)) (nu (W.map f)) := by
  rw [← map_lam, ← map_nu, ← map_WM]; simp [B, map_ofNat]

lemma map_leadInv : MvPowerSeries.map f (leadInv W) = leadInv (W.map f) := by
  apply map_inv_eq (a := lead (WM (W.map f) (Fin 2)) (lam (W.map f)))
  · rw [← map_lead, ← map_mul, lead_mul_leadInv, map_one]
  · exact lead_mul_leadInv _

lemma map_z3 : MvPowerSeries.map f (z3 W) = z3 (W.map f) := by
  rw [z3, z3, map_sub, map_sub, map_neg, map_mul, map_B, map_leadInv, map_X, map_X]

lemma map_w3 : MvPowerSeries.map f (w3 W) = w3 (W.map f) := by
  rw [w3, w3, map_add, map_mul, map_lam, map_z3, map_nu]

lemma map_dd : MvPowerSeries.map f (dd W) = dd (W.map f) := by
  rw [dd, dd, ← map_z3, ← map_w3]; simp

lemma map_dInv : MvPowerSeries.map f (dInv W) = dInv (W.map f) := by
  apply map_inv_eq (a := dd (W.map f))
  · rw [← map_dd, ← map_mul, dd_mul_dInv, map_one]
  · exact dd_mul_dInv _

/-- **base change**: `F_{W.map f} = f_* F_W`. -/
theorem map_F : MvPowerSeries.map f (F W) = F (W.map f) := by
  rw [F, F, map_mul, map_z3, map_dInv]

end Chord

end EllipticFormal
