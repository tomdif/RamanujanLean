/-
# Formal-group homomorphisms: base change, inverses, and factoring through a homomorphism

`EllipticI2.Hom F G f` is the raw homomorphism property `f(F(X,Y)) = G(f X, f Y)`, `f(0) = 0`.
* `hom_map` / `hom_of_map`: homomorphisms are preserved by `map f`, and reflected when `f` is
  injective.
* `hom_inv`: a two-sided compositional inverse of a homomorphism is a homomorphism.
* `hom_of_comp`: if `π : F₁ → F₂` and `σ : F₁ → F₃` are homomorphisms, `π` has a compositional
  inverse `ρ`, and `θ ∘ π = σ`, then `θ : F₂ → F₃` is a homomorphism.
-/
import RamanujanTau.EllipticI2.Step3

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries FGL EllipticI2

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R
local notation "R2" => MvPowerSeries (Fin 2) R

lemma cX0 : constantCoeff (X 0 : R2) = 0 := by simp
lemma cX1 : constantCoeff (X 1 : R2) = 0 := by simp

/-- `f ↦ f(a)` for a one-variable `f`. -/
noncomputable abbrev sb {β : Type*} (a : MvPowerSeries β R) (f : R1) : MvPowerSeries β R :=
  subst (fun _ : Unit => a) f

lemma hc {β : Type*} {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    ∀ s : Unit, constantCoeff ((fun _ : Unit => a) s) = 0 := fun _ => ha

section Map
variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_sb {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) (g : R1) :
    MvPowerSeries.map f (sb a g) = sb (MvPowerSeries.map f a) (MvPowerSeries.map f g) := by
  rw [sb, map_subst (hs (hc ha))]

lemma map_ev' (F : FormalGroup R) {β : Type*} [Finite β] {a b : MvPowerSeries β R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.map f (ev F a b) = ev (F.map f) (MvPowerSeries.map f a) (MvPowerSeries.map f b) := by
  rw [ev, map_subst (hs (cc_vec2 ha hb)), ev]
  congr 1
  funext i; fin_cases i <;> rfl

lemma cc_map {β : Type*} {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    constantCoeff (MvPowerSeries.map f a) = 0 := by
  rw [constantCoeff_map, ha, map_zero]

/-- homomorphisms are preserved by base change. -/
theorem hom_map {F G : FormalGroup R} {φ : R1} (h : Hom F G φ) :
    Hom (F.map f) (G.map f) (MvPowerSeries.map f φ) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨cc_map f h0, ?_⟩
  have := congrArg (MvPowerSeries.map f) h1
  rw [map_sb f (cc_ev F cX0 cX1), map_ev' f F cX0 cX1, map_ev' f G (cc0 _ (hc cX0) h0)
    (cc0 _ (hc cX1) h0), map_sb f cX0, map_sb f cX1] at this
  simpa using this

lemma map_inj (hf : Function.Injective f) {β : Type*} {a b : MvPowerSeries β R}
    (h : MvPowerSeries.map f a = MvPowerSeries.map f b) : a = b := by
  ext e; apply hf; rw [← coeff_map, ← coeff_map, h]

/-- homomorphisms are reflected by an injective base change. -/
theorem hom_of_map (hf : Function.Injective f) {F G : FormalGroup R} {φ : R1}
    (h0 : constantCoeff φ = 0) (h : Hom (F.map f) (G.map f) (MvPowerSeries.map f φ)) :
    Hom F G φ := by
  refine ⟨h0, ?_⟩
  apply map_inj f hf
  have h1 := h.2
  rw [map_sb f (cc_ev F cX0 cX1), map_ev' f F cX0 cX1, map_ev' f G (cc0 _ (hc cX0) h0)
    (cc0 _ (hc cX1) h0), map_sb f cX0, map_sb f cX1]
  simpa using h1

end Map

/-! ### Composition bookkeeping -/

lemma sb_sb {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) {g : R1}
    (hg : constantCoeff g = 0) (f : R1) : sb a (sb g f) = sb (sb a g) f := by
  rw [sb, sb, ss _ _ (hc hg) (hc ha)]

lemma sb_X {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    sb a (X () : R1) = a := sX _ (hc ha) ()

lemma X_sb (f : R1) : sb (X () : R1) f = f := by
  have : (fun _ : Unit => (X () : R1)) = X := by funext s; rfl
  rw [sb, this, subst_self]; rfl

lemma sb_ev (F : FormalGroup R) {β : Type*} [Finite β] {a b : MvPowerSeries β R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (c : β → MvPowerSeries β R) (hcc : ∀ s, constantCoeff (c s) = 0) :
    subst c (ev F a b) = ev F (subst c a) (subst c b) := subst_ev F a b c ha hb hcc

/-- **inverse of a homomorphism**: if `g ∘ f = T`, `f ∘ g = T`, `g(0) = 0` and `f : F₁ → F₂` is a
homomorphism, then so is `g : F₂ → F₁`. -/
theorem hom_inv {F₁ F₂ : FormalGroup R} {f g : R1} (hf : Hom F₁ F₂ f) (hg0 : constantCoeff g = 0)
    (hgf : sb f g = X ()) (hfg : sb g f = X ()) : Hom F₂ F₁ g := by
  obtain ⟨hf0, hfh⟩ := hf
  refine ⟨hg0, ?_⟩
  set g0 := sb (X 0 : R2) g
  set g1 := sb (X 1 : R2) g
  have hg00 : constantCoeff g0 = 0 := cc0 _ (hc cX0) hg0
  have hg10 : constantCoeff g1 = 0 := cc0 _ (hc cX1) hg0
  have hv := cc_vec2 hg00 hg10
  -- substitute `(g X₀, g X₁)` into the homomorphism property of `f`
  have h1 := congrArg (subst ![g0, g1]) hfh
  have eL : subst ![g0, g1] (sb (ev F₁ (X 0 : R2) (X 1)) f) = sb (ev F₁ g0 g1) f := by
    rw [sb, ss _ _ (hc (cc_ev F₁ cX0 cX1)) hv, subst_ev F₁ _ _ _ cX0 cX1 hv, sX _ hv, sX _ hv]
    rfl
  have eX : ∀ i : Fin 2, subst ![g0, g1] (sb (X i : R2) f) = (X i : R2) := by
    intro i
    rw [sb, ss _ _ (hc (by simp)) hv]
    have : (fun _ : Unit => subst ![g0, g1] (X i : R2)) = fun _ => sb (X i : R2) g := by
      funext s; rw [sX _ hv]; fin_cases i <;> rfl
    rw [this, ← sb, ← sb_sb (by simp) hg0, hfg, sb_X (by simp)]
  have eR : subst ![g0, g1] (ev F₂ (sb (X 0 : R2) f) (sb (X 1 : R2) f)) = ev F₂ (X 0) (X 1) := by
    rw [subst_ev F₂ _ _ _ (cc0 _ (hc cX0) hf0) (cc0 _ (hc cX1) hf0) hv, eX 0, eX 1]
  rw [eL, eR] at h1
  -- apply `g`
  have h2 := congrArg (sb · g) h1
  simp only at h2
  rw [← sb_sb (cc_ev F₁ hg00 hg10) hf0, hgf, sb_X (cc_ev F₁ hg00 hg10)] at h2
  exact h2.symm

/-- **the target law is the conjugate of the source law**: if `f : F₁ → F₂` is a homomorphism and
`f ∘ g = T`, then `F₂(X, Y) = f(F₁(g X, g Y))`. -/
theorem law_eq_conj {F₁ F₂ : FormalGroup R} {f g : R1} (hf : Hom F₁ F₂ f) (hg0 : constantCoeff g = 0)
    (hfg : sb g f = X ()) :
    (F₂.toPowerSeries : R2) = sb (ev F₁ (sb (X 0 : R2) g) (sb (X 1 : R2) g)) f := by
  obtain ⟨hf0, hfh⟩ := hf
  set g0 := sb (X 0 : R2) g
  set g1 := sb (X 1 : R2) g
  have hg00 : constantCoeff g0 = 0 := cc0 _ (hc cX0) hg0
  have hg10 : constantCoeff g1 = 0 := cc0 _ (hc cX1) hg0
  have hv := cc_vec2 hg00 hg10
  have h1 := congrArg (subst ![g0, g1]) hfh
  have eL : subst ![g0, g1] (sb (ev F₁ (X 0 : R2) (X 1)) f) = sb (ev F₁ g0 g1) f := by
    rw [sb, ss _ _ (hc (cc_ev F₁ cX0 cX1)) hv, subst_ev F₁ _ _ _ cX0 cX1 hv, sX _ hv, sX _ hv]
    rfl
  have eX : ∀ i : Fin 2, subst ![g0, g1] (sb (X i : R2) f) = (X i : R2) := by
    intro i
    rw [sb, ss _ _ (hc (by simp)) hv]
    have : (fun _ : Unit => subst ![g0, g1] (X i : R2)) = fun _ => sb (X i : R2) g := by
      funext s; rw [sX _ hv]; fin_cases i <;> rfl
    rw [this, ← sb, ← sb_sb (by simp) hg0, hfg, sb_X (by simp)]
  have eR : subst ![g0, g1] (ev F₂ (sb (X 0 : R2) f) (sb (X 1 : R2) f)) = ev F₂ (X 0) (X 1) := by
    rw [subst_ev F₂ _ _ _ (cc0 _ (hc cX0) hf0) (cc0 _ (hc cX1) hf0) hv, eX 0, eX 1]
  rw [eL, eR] at h1
  rw [h1, ev]
  have hX : (![X 0, X 1] : Fin 2 → R2) = X := by funext i; fin_cases i <;> rfl
  rw [hX, subst_self]; rfl

/-- **factoring through a homomorphism**: `θ ∘ π = σ` with `π, σ` homomorphisms and `π` invertible
(`ρ ∘ π = π ∘ ρ = T`) forces `θ` to be a homomorphism. -/
theorem hom_of_comp {F₁ F₂ F₃ : FormalGroup R} {π σ θ ρ : R1} (hπ : Hom F₁ F₂ π)
    (hσ : Hom F₁ F₃ σ) (hθ : sb π θ = σ) (hρ0 : constantCoeff ρ = 0)
    (hρπ : sb π ρ = X ()) (hπρ : sb ρ π = X ()) : Hom F₂ F₃ θ := by
  have hρ : Hom F₂ F₁ ρ := hom_inv hπ hρ0 hρπ hπρ
  have e : θ = sb ρ σ := by
    rw [← hθ, sb_sb hρ0 hπ.1, hπρ, X_sb]
  rw [e]
  exact hom_comp hρ hσ

end VeluLubin
