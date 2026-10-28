import RamanujanTau.SubgroupSum.PointMap
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Rationality of the subgroup sum (Galois descent)

* `galData σ` — a ring endomorphism `σ` of `L` fixing `A, B` acts on `E(L)` (`E = short A B`) by a
  group homomorphism `(x, y) ↦ (σx, σy)`.
* `aC_image`, `bC_image` — `A'_{σG} = σ(A'_G)`, `B'_{σG} = σ(B'_G)`.
* `subSum_map` — `σ (Σ_G f(A'_G, B'_G)) = Σ_G f(A'_G, B'_G)` when `f` commutes with `σ`.
* **`subSum_mem_range`** — for a Galois extension `L/F` (possibly infinite, e.g.
  `L = AlgebraicClosure F` in characteristic `0`), a short curve over `F`, and `Φ ∈ F[X₀, X₁]`:
  `Σ_{G ≤ E(L), |G| = n} Φ(c₄(E/G), −c₆(E/G)) ∈ F`.
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu WeierstrassCurve WeierstrassCurve.Affine

section Conj

variable {L : Type*} [Field L] [DecidableEq L] {A B : L}

omit [DecidableEq L] in
lemma short_map (σ : L →+* L) (hA : σ A = A) (hB : σ B = B) :
    (short A B).map σ = short A B := by
  ext <;> simp [hA, hB]

/-- Conjugation of points by a ring endomorphism fixing the coefficients. -/
def galData (σ : L →+* L) (hA : σ A = A) (hB : σ B = B) : HomData A B A B where
  f := σ
  g := σ
  f_inj := σ.injective
  g_inj := σ.injective
  g_neg := map_neg σ
  ns x y h := by
    have := (map_nonsingular (short A B) σ.injective x y).2 h
    rwa [short_map σ hA hB] at this
  addX x₁ x₂ y₁ y₂ _ _ _ := by
    have h1 := map_slope (W := short A B) σ x₁ x₂ y₁ y₂
    have h2 := map_addX (W' := short A B) σ x₁ x₂ ((short A B).slope x₁ x₂ y₁ y₂)
    rw [short_map σ hA hB] at h1 h2
    rw [← h2, h1]
  addY x₁ x₂ y₁ y₂ _ _ _ := by
    have h1 := map_slope (W := short A B) σ x₁ x₂ y₁ y₂
    have h2 := map_addY (W' := short A B) σ x₁ y₁ x₂ ((short A B).slope x₁ x₂ y₁ y₂)
    rw [short_map σ hA hB] at h1 h2
    rw [← h2, h1]

variable (σ : L →+* L) (hA : σ A = A) (hB : σ B = B)

lemma tSum_image (G : Finset (short A B).Point) :
    tSum (G.image (galData σ hA hB).toFun) = σ (tSum G) := by
  rw [tSum, HomData.sum_image_erase, tSum, map_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Kernel.tQ, Kernel.tQ, HomData.xc_toFun _ (Finset.ne_of_mem_erase hP)]
  simp [galData, hA, map_ofNat]

lemma wSum_image (G : Finset (short A B).Point) :
    wSum (G.image (galData σ hA hB).toFun) = σ (wSum G) := by
  rw [wSum, HomData.sum_image_erase, wSum, map_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Kernel.tQ, Kernel.tQ, Kernel.uQ, Kernel.uQ, HomData.xc_toFun _ (Finset.ne_of_mem_erase hP),
    HomData.yc_toFun _ (Finset.ne_of_mem_erase hP)]
  simp [galData, hA, map_ofNat]

lemma aC_image (G : Finset (short A B).Point) :
    aC (G.image (galData σ hA hB).toFun) = σ (aC G) := by
  rw [aC, aC, tSum_image]; simp [hA, map_ofNat]

lemma bC_image (G : Finset (short A B).Point) :
    bC (G.image (galData σ hA hB).toFun) = σ (bC G) := by
  rw [bC, bC, wSum_image]; simp [hB, map_ofNat]

/-- An injective self-map of a finite set that maps it into itself is onto; so a sum over it is
invariant under the map. -/
lemma sum_image_self {α β : Type*} [DecidableEq α] [AddCommMonoid β] (T : Finset α) (e : α → α)
    (he : Function.Injective e) (hT : ∀ x ∈ T, e x ∈ T) (F : α → β) :
    ∑ x ∈ T, F (e x) = ∑ x ∈ T, F x := by
  have him : T.image e = T :=
    Finset.eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy; exact hT x hx)
      (Finset.card_image_of_injective _ he).ge
  conv_rhs => rw [← him]
  rw [Finset.sum_image fun x _ y _ h => he h]

omit hA hB in
/-- **Galois invariance of the subgroup sum.** -/
theorem subSum_map (hA : σ A = A) (hB : σ B = B) (n : ℕ) (f : L → L → L) (hf : ∀ a b, σ (f a b) = f (σ a) (σ b)) :
    σ (subSum n f A B) = subSum n f A B := by
  classical
  unfold subSum
  split_ifs with h
  · rw [map_sum]
    simp_rw [hf, ← aC_image σ hA hB, ← bC_image σ hA hB]
    refine sum_image_self h.toFinset (fun G => G.image (galData σ hA hB).toFun)
      (Finset.image_injective (galData σ hA hB).toFun_injective) (fun G hG => ?_)
      (fun G => f (aC G) (bC G))
    rw [Set.Finite.mem_toFinset] at hG ⊢
    exact (galData σ hA hB).image_mem_subs hG
  · exact map_zero σ

end Conj

section Descent

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq L]

/-- **Rationality of the subgroup sum.** For a Galois extension `L/F` (e.g. `AlgebraicClosure F`,
characteristic `0`), a short curve `y² = x³ + ax + b` with `a, b ∈ F`, and any `Φ ∈ F[X₀,X₁]`,
the sum over the subgroups `G ≤ E(L)` of order `n` of `Φ(c₄(E/G), −c₆(E/G))` lies in `F`. -/
theorem subSum_mem_range [IsGalois F L] (n : ℕ) (a b : F) (Φ : MvPolynomial (Fin 2) F) :
    subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) Φ)
      (algebraMap F L a) (algebraMap F L b) ∈ Set.range (algebraMap F L) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  refine subSum_map σ.toRingHom (σ.commutes a) (σ.commutes b) n _ fun x y => ?_
  change σ.toAlgHom _ = _
  rw [MvPolynomial.comp_aeval_apply, ptR_short, ptR_short]
  congr 2
  funext i; fin_cases i <;> simp [map_ofNat]

/-- The same over the algebraic closure of a field of characteristic `0`. -/
theorem subSum_mem_range_algebraicClosure [CharZero F] (n : ℕ) (a b : F)
    (Φ : MvPolynomial (Fin 2) F) [DecidableEq (AlgebraicClosure F)] :
    subSum n (fun x y => MvPolynomial.aeval
        (HeckeQExp.ptR (short x y : WeierstrassCurve (AlgebraicClosure F))) Φ)
      (algebraMap F _ a) (algebraMap F _ b) ∈ Set.range (algebraMap F (AlgebraicClosure F)) :=
  subSum_mem_range n a b Φ

end Descent

end SubgroupSum
