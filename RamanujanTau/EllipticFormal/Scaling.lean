/-
# Compatibility with the variable change `(x, y) = (u² x', u³ y')`

For `W' = ⟨u, 0, 0, 0⟩ • W` (so `aᵢ = uⁱ aᵢ'`, and `Δ' = u⁻¹² Δ` by Mathlib's
`WeierstrassCurve.variableChange_Δ`) the parameter changes by `z' = u z`, and
* `w_{W'}(u z) = u³ w_W(z)`                          (`rescale_w`);
* `F_{W'}(u z₁, u z₂) = u F_W(z₁, z₂)`                (`rescale_F`),
where `rescale (fun _ => u)` is the substitution `Xᵢ ↦ u Xᵢ`. So `T ↦ uT` is an isomorphism of
formal groups `F_W → F_{W'}`.
-/
import RamanujanTau.EllipticFormal.FormalGroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticFormal

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- `W` is obtained from `W'` by `aᵢ = uⁱ aᵢ'`. -/
structure IsScaling (W W' : WeierstrassCurve R) (u : R) : Prop where
  h₁ : W.a₁ = u * W'.a₁
  h₂ : W.a₂ = u ^ 2 * W'.a₂
  h₃ : W.a₃ = u ^ 3 * W'.a₃
  h₄ : W.a₄ = u ^ 4 * W'.a₄
  h₆ : W.a₆ = u ^ 6 * W'.a₆

lemma isScaling_variableChange (W : WeierstrassCurve R) (u : Rˣ) :
    IsScaling W ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • W) u := by
  have e : ∀ k : ℕ, ∀ x : R, x = (u : R) ^ k * ((↑u⁻¹ : R) ^ k * x) := fun k x => by
    rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  constructor
  · rw [WeierstrassCurve.variableChange_a₁]; simp
  · rw [WeierstrassCurve.variableChange_a₂]; simpa using e 2 W.a₂
  · rw [WeierstrassCurve.variableChange_a₃]; simpa using e 3 W.a₃
  · rw [WeierstrassCurve.variableChange_a₄]; simpa using e 4 W.a₄
  · rw [WeierstrassCurve.variableChange_a₆]; simpa using e 6 W.a₆

variable {W W' : WeierstrassCurve R} {u : R}

section Rescale
variable {σ : Type*}

/-- the scaling `Xᵢ ↦ u Xᵢ`. -/
noncomputable abbrev ψ (σ : Type*) (u : R) : MvPowerSeries σ R →+* MvPowerSeries σ R :=
  rescale (fun _ => u)

lemma ψ_C (r : R) : ψ σ u (C r) = C r := by
  classical
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

lemma ψ_X [DecidableEq σ] (i : σ) : ψ σ u (X i) = C u * X i := by
  ext n
  rw [coeff_rescale, coeff_X, coeff_C_mul, coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

lemma ψ_WM (W : WeierstrassCurve R) : (WM W σ).map (ψ σ u) = WM W σ := by
  simp only [WM, WeierstrassCurve.map_map]
  congr 1
  ext r : 1
  exact ψ_C r

lemma G_scale (h : IsScaling W W' u) (z w : MvPowerSeries σ R) :
    G (WM W' σ) (C u * z) (C u ^ 3 * w) = C u ^ 3 * G (WM W σ) z w := by
  simp only [G, WM, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h.h₁, h.h₂, h.h₃, h.h₄, h.h₆, map_mul,
    map_pow]
  ring

/-- **`w_{W'}(u z) = u³ w_W(z)`**, for any variable `z = Xⱼ`. -/
theorem ψ_wt [DecidableEq σ] (h : IsScaling W W' u) (j : σ) :
    ψ σ u (wt W' (X j)) = C u ^ 3 * wt W (X j) := by
  have hz : constantCoeff (C u * X j : MvPowerSeries σ R) = 0 := by simp
  have e1 : G (WM W' σ) (C u * X j) (ψ σ u (wt W' (X j))) = 0 := by
    have := congrArg (ψ σ u) (G_wt (W := W') (t := (X j : MvPowerSeries σ R)) (by simp))
    rwa [map_G, ψ_WM, ψ_X, map_zero] at this
  have e2 : G (WM W' σ) (C u * X j) (C u ^ 3 * wt W (X j)) = 0 := by
    rw [G_scale h, G_wt (by simp), mul_zero]
  refine G_unique _ hz ?_ ?_ e1 e2
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
    simp [cc_wt]
  · simp [cc_wt]

/-- **`w_{W'}(u T) = u³ w_W(T)`**. -/
theorem rescale_w (h : IsScaling W W' u) :
    ψ Unit u (w W' : MvPowerSeries Unit R) = C u ^ 3 * (w W : MvPowerSeries Unit R) := by
  have e : ∀ V : WeierstrassCurve R, wt V (X () : MvPowerSeries Unit R) = (w V : _) :=
    fun V => PowerSeries.X_subst _
  have := ψ_wt h ()
  rwa [e, e] at this

lemma coeff_w_scale (h : IsScaling W W' u) (n : ℕ) :
    u ^ n * PowerSeries.coeff n (w W') = u ^ 3 * PowerSeries.coeff n (w W) := by
  have := congrArg (coeff (Finsupp.single () n)) (rescale_w h)
  rw [coeff_rescale, ← map_pow, coeff_C_mul] at this
  simpa [Finsupp.prod_single_index] using this

end Rescale

section Chord2
variable {v : Rˣ} (h : IsScaling W W' (v : R))

local notation "ψ₂" => ψ (Fin 2) (v : R)
local notation "u" => ((v : Rˣ) : R)

include h

lemma ψ_lam' : ψ₂ (lam W') = C (u ^ 2) * lam W := by
  ext e
  rw [coeff_rescale, coeff_C_mul, coeff_lam, coeff_lam]
  have hp : (e.prod fun _ m => u ^ m) = u ^ (e 0 + e 1) := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, pow_add]
  rw [hp]
  have h1 := coeff_w_scale h (e 0 + e 1 + 1)
  have : (v : R) * (u ^ (e 0 + e 1) * PowerSeries.coeff (e 0 + e 1 + 1) (w W')) =
      (v : R) * (u ^ 2 * PowerSeries.coeff (e 0 + e 1 + 1) (w W)) := by
    rw [← mul_assoc, ← pow_succ', h1]; ring
  exact (Units.mul_right_inj v).1 this

lemma ψ_nu : ψ₂ (nu W') = C (u ^ 3) * nu W := by
  rw [nu, nu, map_sub, map_mul, ψ_wt h, ψ_lam' h, ψ_X]; simp only [map_pow]; ring

lemma ψ_lead : ψ₂ (lead (WM W' (Fin 2)) (lam W')) = lead (WM W (Fin 2)) (lam W) := by
  have e := lead_map ψ₂ (WM W' (Fin 2)) (lam W')
  rw [ψ_WM, ψ_lam' h] at e
  rw [e]
  simp only [lead, WM, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    h.h₂, h.h₄, h.h₆, map_mul, map_pow]
  ring

lemma ψ_B : ψ₂ (B (WM W' (Fin 2)) (lam W') (nu W')) = C u * B (WM W (Fin 2)) (lam W) (nu W) := by
  have e := B_map ψ₂ (WM W' (Fin 2)) (lam W') (nu W')
  rw [ψ_WM, ψ_lam' h, ψ_nu h] at e
  rw [e]
  simp only [B, WM, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h.h₁, h.h₂, h.h₃, h.h₄, h.h₆, map_mul,
    map_pow]
  ring

lemma ψ_leadInv : ψ₂ (leadInv W') = leadInv W := by
  apply map_inv_eq (a := lead (WM W (Fin 2)) (lam W))
  · rw [← ψ_lead h, ← map_mul, lead_mul_leadInv, map_one]
  · exact lead_mul_leadInv W

lemma ψ_z3 : ψ₂ (z3 W') = C u * z3 W := by
  rw [z3, z3, map_sub, map_sub, map_neg, map_mul, ψ_B h, ψ_leadInv h, ψ_X, ψ_X]; ring

lemma ψ_w3 : ψ₂ (w3 W') = C (u ^ 3) * w3 W := by
  rw [w3, w3, map_add, map_mul, ψ_lam' h, ψ_z3 h, ψ_nu h]; simp only [map_pow]; ring

lemma ψ_dd : ψ₂ (dd W') = dd W := by
  rw [dd, dd, map_sub, map_add, map_mul, map_mul, ψ_z3 h, ψ_w3 h, map_one]
  simp only [WM, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ψ_C, h.h₁, h.h₃, map_mul,
    map_pow]
  ring

lemma ψ_dInv : ψ₂ (dInv W') = dInv W := by
  apply map_inv_eq (a := dd W)
  · rw [← ψ_dd h, ← map_mul, dd_mul_dInv, map_one]
  · exact dd_mul_dInv W

/-- **`F_{W'}(u z₁, u z₂) = u F_W(z₁, z₂)`**. -/
theorem ψ_F : ψ₂ (F W') = C u * F W := by
  rw [F, F, map_mul, ψ_z3 h, ψ_dInv h]; ring

end Chord2

/-- **variable change**: for `W' = ⟨u, 0, 0, 0⟩ • W` (`aᵢ' = u⁻ⁱ aᵢ`, `Δ' = u⁻¹² Δ`),
`F_{W'}(u X₀, u X₁) = u · F_W(X₀, X₁)`. -/
theorem rescale_F (W : WeierstrassCurve R) (u : Rˣ) :
    rescale (fun _ => (u : R)) (F ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • W)) =
      C (u : R) * F W :=
  ψ_F (isScaling_variableChange W u)

/-- `w_{W'}(u T) = u³ w_W(T)` for `W' = ⟨u, 0, 0, 0⟩ • W`. -/
theorem rescale_w_variableChange (W : WeierstrassCurve R) (u : Rˣ) :
    rescale (fun _ => (u : R))
        (w ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • W) : MvPowerSeries Unit R) =
      C (u : R) ^ 3 * (w W : MvPowerSeries Unit R) :=
  rescale_w (isScaling_variableChange W u)

end EllipticFormal
