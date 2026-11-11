import RamanujanTau.MultiQuintupleFourPlaneCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Four-dimensional rational isometries assembled from a spanning Gram family. -/
namespace Ramanujan.MultiQuintuple

abbrev FourRatPoint := Fin 4 → ℚ

def fourRatNorm (x : FourRatPoint) : ℚ := fourDot x x

theorem fourDot_comm {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    fourDot x y=fourDot y x := by simp only [fourDot]; ring

theorem fourDot_add_left {R : Type*} [CommRing R] (x y z : Fin 4 → R) :
    fourDot (x+y) z=fourDot x z+fourDot y z := by simp [fourDot]; ring

theorem fourDot_add_right {R : Type*} [CommRing R] (x y z : Fin 4 → R) :
    fourDot x (y+z)=fourDot x y+fourDot x z := by simp [fourDot]; ring

theorem fourDot_smul_left {R : Type*} [CommRing R] (c : R) (x y : Fin 4 → R) :
    fourDot (c • x) y=c*fourDot x y := by simp [fourDot,smul_eq_mul]; ring

theorem fourDot_smul_right {R : Type*} [CommRing R] (c : R) (x y : Fin 4 → R) :
    fourDot x (c • y)=c*fourDot x y := by simp [fourDot,smul_eq_mul]; ring

@[simp] theorem fourDot_zero_left {R : Type*} [CommRing R] (x : Fin 4 → R) :
    fourDot 0 x=0 := by simp [fourDot]

@[simp] theorem fourDot_zero_right {R : Type*} [CommRing R] (x : Fin 4 → R) :
    fourDot x 0=0 := by simp [fourDot]

theorem fourRatNorm_sub (x y : FourRatPoint) :
    fourRatNorm (x-y)=fourRatNorm x-2*fourDot x y+fourRatNorm y := by
  simp [fourRatNorm,fourDot]
  ring

theorem fourRatNorm_eq_zero_iff (x : FourRatPoint) : fourRatNorm x=0 ↔ x=0 := by
  constructor
  · intro h
    funext i
    simp only [fourRatNorm,fourDot] at h
    fin_cases i
    · change x 0=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 1=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 2=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
    · change x 3=0
      nlinarith [mul_self_nonneg (x 0),mul_self_nonneg (x 1),
        mul_self_nonneg (x 2),mul_self_nonneg (x 3)]
  · rintro rfl
    simp [fourRatNorm]

/-- A pairing preserving every Gram entry on a spanning set has a single
orthogonal linear extension.  No linearity of the pairing is assumed. -/
theorem four_exists_linear_of_spanning_dot_pairing
    (S : Set FourRatPoint) (hspan : Submodule.span ℚ S = ⊤)
    (f : FourRatPoint → FourRatPoint)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, fourDot (f x) (f y) = fourDot x y) :
    ∃ T : FourRatPoint →ₗ[ℚ] FourRatPoint,
      (∀ x ∈ S, T x = f x) ∧
      (∀ x y, fourDot (T x) (T y) = fourDot x y) := by
  classical
  let b := Module.Basis.ofSpan (show ⊤ ≤ Submodule.span ℚ S by rw [hspan])
  have hb : ∀ i, b i ∈ S := fun i => Module.Basis.ofSpan_subset _ ⟨i,rfl⟩
  let T := b.constr ℚ (fun i => f (b i))
  have hTb : ∀ i, T (b i) = f (b i) := fun i => b.constr_basis ℚ _ i
  have hcross : ∀ x s, s ∈ S → fourDot (T x) (f s) = fourDot x s := by
    intro x s hs
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hTb]
        exact hpair (b i) (hb i) s hs
    | zero => simp
    | add a b ha hb' ia ib =>
        rw [map_add, fourDot_add_left, fourDot_add_left, ia, ib]
    | smul c a ha ia =>
        rw [map_smul, fourDot_smul_left, fourDot_smul_left, ia]
  have hdot : ∀ x y, fourDot (T x) (T y) = fourDot x y := by
    intro x y
    have hy : y ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hTb]
        exact hcross x (b i) (hb i)
    | zero => simp
    | add a b ha hb' ia ib =>
        rw [map_add, fourDot_add_right, fourDot_add_right, ia, ib]
    | smul c a ha ia =>
        rw [map_smul, fourDot_smul_right, fourDot_smul_right, ia]
  refine ⟨T, ?_, hdot⟩
  intro x hx
  apply sub_eq_zero.mp
  apply (fourRatNorm_eq_zero_iff _).mp
  rw [fourRatNorm_sub, fourRatNorm, fourRatNorm,
    hdot, hcross x x hx, hpair x hx x hx]
  ring

/-- The spanning-set theorem also applies to indexed families, even when
the indexing contains duplicate vectors. Preservation of the Gram matrix
itself proves that duplicate sources have equal images. -/
theorem four_exists_linear_of_spanning_gram_family {ι : Type*}
    (a b : ι → FourRatPoint) (hspan : Submodule.span ℚ (Set.range a) = ⊤)
    (hgram : ∀ i j, fourDot (b i) (b j) = fourDot (a i) (a j)) :
    ∃ T : FourRatPoint →ₗ[ℚ] FourRatPoint,
      (∀ i, T (a i) = b i) ∧
      (∀ x y, fourDot (T x) (T y) = fourDot x y) := by
  classical
  have hconsistent : ∀ i j, a i = a j → b i = b j := by
    intro i j hij
    apply sub_eq_zero.mp
    apply (fourRatNorm_eq_zero_iff _).mp
    rw [fourRatNorm_sub, fourRatNorm, fourRatNorm,
      hgram, hgram, hgram, hij]
    ring
  let f : FourRatPoint → FourRatPoint := fun x =>
    if hx : ∃ i, a i = x then b hx.choose else 0
  have hf : ∀ i, f (a i) = b i := by
    intro i
    dsimp [f]
    split_ifs with hx
    · exact hconsistent _ _ hx.choose_spec
    · exact False.elim (hx ⟨i,rfl⟩)
  obtain ⟨T,hT,hdot⟩ := four_exists_linear_of_spanning_dot_pairing (Set.range a) hspan f (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    rw [hf,hf]
    exact hgram i j)
  exact ⟨T, fun i => (hT (a i) ⟨i,rfl⟩).trans (hf i), hdot⟩

end Ramanujan.MultiQuintuple
