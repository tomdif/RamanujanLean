/-
# The formal group of a Weierstrass curve is a (commutative) `FormalGroup`

* Over a domain `R` with `2 ≠ 0`: associativity and commutativity of the chord series `F W`
  follow from Mathlib's group law on `W(Frac R⟦X₀,X₁,X₂⟧)` via `P_add` and injectivity of `P`.
* The universal curve over `ℤ[A₁, A₂, A₃, A₄, A₆]` is such a case.
* For an arbitrary commutative ring, `F W` is the image of the universal `F` (`map_F`), so the
  axioms transfer (`FormalGroup.map`).
-/
import RamanujanTau.EllipticFormal.Points

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticFormal

open MvPowerSeries

open scoped Classical

section Domain
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

local notation "A₃" => MvPowerSeries (Fin 3) R

lemma lin_X' {σ : Type*} [DecidableEq σ] (i : σ) :
    coeff (Finsupp.single i 1) (X i : MvPowerSeries σ R) = 1 := by rw [lin_X, if_pos rfl]

lemma lin_X'' {σ : Type*} [DecidableEq σ] {i j : σ} (h : j ≠ i) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ R) = 0 := by rw [lin_X, if_neg h]

/-- **associativity** over a domain with `2 ≠ 0`. -/
theorem assoc_domain (h2 : (2 : R) ≠ 0) :
    subst ![subst ![(X 0 : A₃), X 1] (F W), X 2] (F W) =
      subst ![X 0, subst ![(X 1 : A₃), X 2] (F W)] (F W) := by
  have c0 : constantCoeff (X 0 : A₃) = 0 := by simp
  have c1 : constantCoeff (X 1 : A₃) = 0 := by simp
  have c2 : constantCoeff (X 2 : A₃) = 0 := by simp
  have c01 := FGL.cc0 _ (FGL.cc_vec2 c0 c1) (cc_F W)
  have c12 := FGL.cc0 _ (FGL.cc_vec2 c1 c2) (cc_F W)
  have l01 : coeff (Finsupp.single 0 1) (subst ![(X 0 : A₃), X 1] (F W)) = 1 := by
    rw [lin_subst2 _ _ _ c0 c1, lin_F, lin_F, lin_X', lin_X'' (by decide)]; ring
  have l12a : coeff (Finsupp.single 0 1) (subst ![(X 1 : A₃), X 2] (F W)) = 0 := by
    rw [lin_subst2 _ _ _ c1 c2, lin_F, lin_F, lin_X'' (by decide), lin_X'' (by decide)]; ring
  have l12b : coeff (Finsupp.single 1 1) (subst ![(X 1 : A₃), X 2] (F W)) = 1 := by
    rw [lin_subst2 _ _ _ c1 c2, lin_F, lin_F, lin_X', lin_X'' (by decide)]; ring
  have e1 := P_add W h2 c0 c1 (i := 0) (lin_X' 0) (lin_X'' (by decide)) (lin_ne_zero (lin_X' 1))
  have e2 := P_add W h2 c01 c2 (i := 0) l01 (lin_X'' (by decide)) (lin_ne_zero (lin_X' 2))
  have e3 := P_add W h2 c1 c2 (i := 1) (lin_X' 1) (lin_X'' (by decide)) (lin_ne_zero (lin_X' 2))
  have e4 := P_add W h2 c0 c12 (i := 0) (lin_X' 0) l12a (lin_ne_zero l12b)
  have := e2.symm.trans ((congrArg (· + P W h2 (X 2) c2 (lin_ne_zero (lin_X' 2))) e1.symm).trans
    ((add_assoc _ _ _).trans ((congrArg (P W h2 (X 0) c0 (lin_ne_zero (lin_X' 0)) + ·) e3).trans e4)))
  exact P_inj W h2 this

/-- **commutativity** over a domain with `2 ≠ 0`. -/
theorem comm_domain (h2 : (2 : R) ≠ 0) :
    F W = subst ![(X 1 : MvPowerSeries (Fin 2) R), X 0] (F W) := by
  have c0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have c1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have e1 := P_add W h2 c0 c1 (i := 0) (lin_X' 0) (lin_X'' (by decide)) (lin_ne_zero (lin_X' 1))
  have e2 := P_add W h2 c1 c0 (i := 1) (lin_X' 1) (lin_X'' (by decide)) (lin_ne_zero (lin_X' 0))
  have h := P_inj W h2 (e1.symm.trans ((add_comm _ _).trans e2))
  have hX : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X := by
    funext i; fin_cases i <;> rfl
  rw [hX, subst_self] at h
  exact h

end Domain

/-! ## The universal Weierstrass curve -/

/-- the universal coefficient ring `ℤ[A₁, A₂, A₃, A₄, A₆]`. -/
abbrev Ru := MvPolynomial (Fin 5) ℤ

/-- the universal Weierstrass curve. -/
noncomputable def Wu : WeierstrassCurve Ru where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

/-- the formal group of the universal curve. -/
noncomputable def formalGroupU : FormalGroup Ru where
  toPowerSeries := F Wu
  zero_constantCoeff := cc_F Wu
  lin_coeff_X := lin_F Wu 0
  lin_coeff_Y := lin_F Wu 1
  assoc := assoc_domain Wu two_ne_zero

variable {R : Type*} [CommRing R]

/-- the specialization `ℤ[A] → R`, `Aᵢ ↦ aᵢ`. -/
noncomputable def spec (W : WeierstrassCurve R) : Ru →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

lemma Wu_map_spec (W : WeierstrassCurve R) : Wu.map (spec W) = W := by
  ext <;> simp [Wu, spec]

lemma F_eq_map (W : WeierstrassCurve R) : F W = MvPowerSeries.map (spec W) (F Wu) := by
  rw [map_F, Wu_map_spec]

/-- **the formal group of a Weierstrass curve** over any commutative ring. -/
noncomputable def formalGroup (W : WeierstrassCurve R) : FormalGroup R where
  toPowerSeries := F W
  zero_constantCoeff := cc_F W
  lin_coeff_X := lin_F W 0
  lin_coeff_Y := lin_F W 1
  assoc := by
    have h := (formalGroupU.map (spec W)).assoc
    have e : (formalGroupU.map (spec W)).toPowerSeries = F W := by
      rw [FormalGroup.map_toPowerSeries, F_eq_map]; rfl
    rwa [e] at h

@[simp] lemma formalGroup_toPowerSeries (W : WeierstrassCurve R) :
    (formalGroup W).toPowerSeries = F W := rfl

/-- the formal group of `W` is commutative. -/
instance (W : WeierstrassCurve R) : (formalGroup W).IsComm where
  comm := by
    have h := congrArg (MvPowerSeries.map (spec W)) (comm_domain Wu two_ne_zero)
    have hs : HasSubst ![(X 1 : MvPowerSeries (Fin 2) Ru), X 0] :=
      FGL.hs (FGL.cc_vec2 (by simp) (by simp))
    rw [map_subst hs, ← F_eq_map] at h
    have hv : (fun i => MvPowerSeries.map (spec W) (![(X 1 : MvPowerSeries (Fin 2) Ru), X 0] i)) =
        ![X 1, X 0] := by
      funext i; fin_cases i <;> simp
    rw [hv] at h
    exact h

/-- base change of the formal group. -/
theorem formalGroup_map {S : Type*} [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (formalGroup W).map f = formalGroup (W.map f) := by
  ext : 1
  rw [FormalGroup.map_toPowerSeries, formalGroup_toPowerSeries, formalGroup_toPowerSeries, map_F]

end EllipticFormal
