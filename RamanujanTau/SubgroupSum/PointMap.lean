import RamanujanTau.SubgroupSum.Basic

/-!
# Group homomorphisms between short curves given by coordinate maps

`PointMap.map f g` sends `(x, y) ↦ (f x, g y)` from `short A B` to `short A₂ B₂`. If `f, g` are
injective, `g (-y) = -(g y)`, nonsingular points go to nonsingular points, and the addition formulas
are respected (`HomData`), then it is an additive group homomorphism (`PointMap.map_add`), injective.

Instances: Galois conjugation (`SubgroupSum.Galois`) and the scaling `(x,y) ↦ (u²x, u³y)`
(`SubgroupSum.Scale`).
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {A B A₂ B₂ : K}

/-- Data for a coordinate map `(x, y) ↦ (f x, g y)` respecting the group law. -/
structure HomData (A B A₂ B₂ : K) where
  f : K → K
  g : K → K
  f_inj : Function.Injective f
  g_inj : Function.Injective g
  g_neg : ∀ y, g (-y) = -g y
  ns : ∀ x y, (short A B).Nonsingular x y → (short A₂ B₂).Nonsingular (f x) (g y)
  addX : ∀ x₁ x₂ y₁ y₂, (short A B).Nonsingular x₁ y₁ → (short A B).Nonsingular x₂ y₂ →
    ¬(x₁ = x₂ ∧ y₁ = (short A B).negY x₂ y₂) →
    f ((short A B).addX x₁ x₂ ((short A B).slope x₁ x₂ y₁ y₂)) =
      (short A₂ B₂).addX (f x₁) (f x₂) ((short A₂ B₂).slope (f x₁) (f x₂) (g y₁) (g y₂))
  addY : ∀ x₁ x₂ y₁ y₂, (short A B).Nonsingular x₁ y₁ → (short A B).Nonsingular x₂ y₂ →
    ¬(x₁ = x₂ ∧ y₁ = (short A B).negY x₂ y₂) →
    g ((short A B).addY x₁ x₂ y₁ ((short A B).slope x₁ x₂ y₁ y₂)) =
      (short A₂ B₂).addY (f x₁) (f x₂) (g y₁) ((short A₂ B₂).slope (f x₁) (f x₂) (g y₁) (g y₂))

namespace HomData

variable (φ : HomData A B A₂ B₂)

/-- The induced map on points. -/
def toFun : (short A B).Point → (short A₂ B₂).Point
  | 0 => 0
  | .some x y h => .some (φ.f x) (φ.g y) (φ.ns x y h)

@[simp] lemma toFun_zero : φ.toFun 0 = 0 := rfl

omit [DecidableEq K] in
lemma negY_short (a b x y : K) : (short a b).negY x y = -y := by
  simp [Affine.negY]

lemma opp_iff (x₁ x₂ y₁ y₂ : K) :
    (φ.f x₁ = φ.f x₂ ∧ φ.g y₁ = (short A₂ B₂).negY (φ.f x₂) (φ.g y₂)) ↔
      (x₁ = x₂ ∧ y₁ = (short A B).negY x₂ y₂) := by
  rw [negY_short, negY_short, ← φ.g_neg, φ.f_inj.eq_iff, φ.g_inj.eq_iff]

lemma toFun_add (P Q : (short A B).Point) : φ.toFun (P + Q) = φ.toFun P + φ.toFun Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (short A B).negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    change 0 = Point.some _ _ (φ.ns x₁ y₁ h₁) + Point.some _ _ (φ.ns x₂ y₂ h₂)
    rw [Point.add_of_Y_eq ((φ.opp_iff _ _ _ _).2 hxy).1 ((φ.opp_iff _ _ _ _).2 hxy).2]
  · have hxy' : ¬(φ.f x₁ = φ.f x₂ ∧ φ.g y₁ = (short A₂ B₂).negY (φ.f x₂) (φ.g y₂)) := by
      rwa [φ.opp_iff]
    rw [Point.add_some hxy]
    change Point.some _ _ _ = Point.some _ _ (φ.ns x₁ y₁ h₁) + Point.some _ _ (φ.ns x₂ y₂ h₂)
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    exact ⟨φ.addX _ _ _ _ h₁ h₂ hxy, φ.addY _ _ _ _ h₁ h₂ hxy⟩

/-- The additive group homomorphism. -/
def hom : (short A B).Point →+ (short A₂ B₂).Point where
  toFun := φ.toFun
  map_zero' := rfl
  map_add' := φ.toFun_add

@[simp] lemma hom_apply (P : (short A B).Point) : φ.hom P = φ.toFun P := rfl

lemma toFun_injective : Function.Injective φ.toFun := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · simp only [toFun, Point.some.injEq] at h
    obtain rfl := φ.f_inj h.1
    obtain rfl := φ.g_inj h.2
    rfl

lemma toFun_eq_zero {P : (short A B).Point} : φ.toFun P = 0 ↔ P = 0 := by
  rw [← φ.toFun_zero, φ.toFun_injective.eq_iff]

lemma xc_toFun {P : (short A B).Point} (hP : P ≠ 0) : xc (φ.toFun P) = φ.f (xc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

lemma yc_toFun {P : (short A B).Point} (hP : P ≠ 0) : yc (φ.toFun P) = φ.g (yc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

/-- Images of subgroups are subgroups (of the same cardinality). -/
lemma isSub_image {G : Finset (short A B).Point} (hG : IsSub G) :
    IsSub (G.image φ.toFun) := by
  refine ⟨Finset.mem_image.2 ⟨0, hG.1, rfl⟩, ?_, ?_⟩
  · intro P hP Q hQ
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_image.2 ⟨P' + Q', hG.2.1 _ hP' _ hQ', φ.toFun_add _ _⟩
  · intro P hP
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_image.2 ⟨-P', hG.2.2 _ hP', φ.hom.map_neg P'⟩

lemma card_image (G : Finset (short A B).Point) : (G.image φ.toFun).card = G.card :=
  Finset.card_image_of_injective _ φ.toFun_injective

lemma image_mem_subs {n : ℕ} {G : Finset (short A B).Point} (hG : G ∈ subs A B n) :
    G.image φ.toFun ∈ subs A₂ B₂ n :=
  ⟨φ.isSub_image hG.1, (φ.card_image G).trans hG.2⟩

/-- Sums over `G ∖ 0` transport along the map. -/
lemma sum_image_erase (G : Finset (short A B).Point) (F : (short A₂ B₂).Point → K) :
    ∑ P ∈ (G.image φ.toFun).erase 0, F P = ∑ P ∈ G.erase 0, F (φ.toFun P) := by
  have : (G.image φ.toFun).erase 0 = (G.erase 0).image φ.toFun := by
    rw [← φ.toFun_zero, Finset.image_erase φ.toFun_injective]
  rw [this, Finset.sum_image fun P _ Q _ h => φ.toFun_injective h]

end HomData

end SubgroupSum
