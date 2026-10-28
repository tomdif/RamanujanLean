import RamanujanTau.TorsionSpec.Spec

/-!
# Points over an algebraically closed subfield

For an algebraically closed `F`, a field `L ⊇ F` (`Algebra F L`), and `E : y² = x³ + ax + b` over
`F`, the coordinatewise map `E(F) → E(L)` is an injective group homomorphism (`liftHom`) whose image
is the set of points with coordinates in `F` (`mem_range_lift`); elements of `L` algebraic over `F`
lie in `F` (`mem_range_of_isAlgebraic`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Velu WeierstrassCurve WeierstrassCurve.Affine

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq F] [DecidableEq L]

lemma mem_range_of_isIntegral [IsAlgClosed F] {z : L} (h : IsIntegral F z) :
    z ∈ Set.range (algebraMap F L) :=
  minpoly.mem_range_of_degree_eq_one F z
    (IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible h))

lemma short_map_eq (a b : F) :
    (short a b).map (algebraMap F L) = short (algebraMap F L a) (algebraMap F L b) := by
  ext <;> simp [short]

variable (a b : F)

/-- The lift of points. -/
def liftPt : (short a b).Point → (short (algebraMap F L a) (algebraMap F L b)).Point
  | 0 => 0
  | .some x y h => .some (algebraMap F L x) (algebraMap F L y) (by
      have := (map_nonsingular (short a b) (algebraMap F L).injective x y).2 h
      rwa [short_map_eq] at this)

@[simp] lemma liftPt_zero : liftPt (L := L) a b 0 = 0 := rfl

lemma liftPt_add (P Q : (short a b).Point) :
    liftPt (L := L) a b (P + Q) = liftPt a b P + liftPt a b Q := by
  set f := algebraMap F L
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  have hneg : ∀ x y : F, f ((short a b).negY x y) = (short (f a) (f b)).negY (f x) (f y) := by
    intro x y; simp [Affine.negY]
  have hopp : (f x₁ = f x₂ ∧ f y₁ = (short (f a) (f b)).negY (f x₂) (f y₂)) ↔
      (x₁ = x₂ ∧ y₁ = (short a b).negY x₂ y₂) := by
    rw [← hneg, f.injective.eq_iff, f.injective.eq_iff]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (short a b).negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    change 0 = Point.some _ _ _ + Point.some _ _ _
    rw [Point.add_of_Y_eq (hopp.2 hxy).1 (hopp.2 hxy).2]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (short (f a) (f b)).negY (f x₂) (f y₂)) := by rwa [hopp]
    rw [Point.add_some hxy]
    change Point.some _ _ _ = Point.some _ _ _ + Point.some _ _ _
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    have h1 := map_slope (W := short a b) f x₁ x₂ y₁ y₂
    have h2 := map_addX (W' := short a b) f x₁ x₂ ((short a b).slope x₁ x₂ y₁ y₂)
    have h3 := map_addY (W' := short a b) f x₁ y₁ x₂ ((short a b).slope x₁ x₂ y₁ y₂)
    rw [short_map_eq] at h1 h2 h3
    rw [← h1] at h2 h3
    exact ⟨h2.symm, h3.symm⟩

/-- The lift as a group homomorphism. -/
def liftHom : (short a b).Point →+ (short (algebraMap F L a) (algebraMap F L b)).Point where
  toFun := liftPt a b
  map_zero' := rfl
  map_add' := liftPt_add a b

lemma liftPt_injective : Function.Injective (liftPt (L := L) a b) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · simp only [liftPt, Point.some.injEq] at h
    obtain rfl := (algebraMap F L).injective h.1
    obtain rfl := (algebraMap F L).injective h.2
    rfl

/-- Points with coordinates in `F` are lifts. -/
lemma mem_range_lift {P : (short (algebraMap F L a) (algebraMap F L b)).Point}
    (hx : xc P ∈ Set.range (algebraMap F L)) (hy : yc P ∈ Set.range (algebraMap F L)) :
    ∃ P₀, liftPt a b P₀ = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨x₀, rfl⟩ := hx
    obtain ⟨y₀, rfl⟩ := hy
    have h₀ : (short a b).Nonsingular x₀ y₀ := by
      have := (map_nonsingular (short a b) (algebraMap F L).injective x₀ y₀).1
      rw [short_map_eq] at this
      exact this h
    exact ⟨.some x₀ y₀ h₀, rfl⟩

end TorsionSpec
