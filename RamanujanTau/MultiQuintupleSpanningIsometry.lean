/-
# Extending a spanning dot-product-preserving pairing

A map on a rational spanning set that preserves all pairwise dot products
extends to one rational orthogonal linear map.  This is the linear assembly
step in the short-vector converse, rather than a coherence assumption.
-/
import RamanujanTau.MultiQuintupleThetaArithmetic
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Ramanujan.MultiQuintuple

theorem ternaryRatDot_comm (x y : TernaryRatPoint) :
    ternaryRatDot x y = ternaryRatDot y x := by
  simp only [ternaryRatDot]
  ring

theorem ternaryRatDot_add_right (x y z : TernaryRatPoint) :
    ternaryRatDot x (y+z) = ternaryRatDot x y + ternaryRatDot x z := by
  rw [ternaryRatDot_comm, ternaryRatDot_add_left]
  rw [ternaryRatDot_comm y x, ternaryRatDot_comm z x]

@[simp] theorem ternaryRatDot_zero_left (x : TernaryRatPoint) :
    ternaryRatDot 0 x = 0 := by simp [ternaryRatDot]

@[simp] theorem ternaryRatDot_zero_right (x : TernaryRatPoint) :
    ternaryRatDot x 0 = 0 := by simp [ternaryRatDot]

theorem ternaryRatNorm_sub (x y : TernaryRatPoint) :
    ternaryRatNorm (x-y) = ternaryRatNorm x - 2*ternaryRatDot x y + ternaryRatNorm y := by
  rcases x with ⟨⟨a,b⟩,c⟩
  rcases y with ⟨⟨d,e⟩,f⟩
  simp only [ternaryRatNorm, ternaryRatDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem ternaryRatNorm_eq_zero_iff (x : TernaryRatPoint) :
    ternaryRatNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_gt (ternaryRatNorm_pos hn)) h
  · rintro rfl
    norm_num [ternaryRatNorm]

/-- A pairing preserving every Gram entry on a spanning set has a single
orthogonal linear extension.  No linearity of the pairing is assumed. -/
theorem exists_linear_of_spanning_dot_pairing
    (S : Set TernaryRatPoint) (hspan : Submodule.span ℚ S = ⊤)
    (f : TernaryRatPoint → TernaryRatPoint)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, ternaryRatDot (f x) (f y) = ternaryRatDot x y) :
    ∃ T : TernaryRatPoint →ₗ[ℚ] TernaryRatPoint,
      (∀ x ∈ S, T x = f x) ∧
      (∀ x y, ternaryRatDot (T x) (T y) = ternaryRatDot x y) := by
  classical
  let b := Module.Basis.ofSpan (show ⊤ ≤ Submodule.span ℚ S by rw [hspan])
  have hb : ∀ i, b i ∈ S := fun i => Module.Basis.ofSpan_subset _ ⟨i,rfl⟩
  let T := b.constr ℚ (fun i => f (b i))
  have hTb : ∀ i, T (b i) = f (b i) := fun i => b.constr_basis ℚ _ i
  have hcross : ∀ x s, s ∈ S → ternaryRatDot (T x) (f s) = ternaryRatDot x s := by
    intro x s hs
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hTb]
        exact hpair (b i) (hb i) s hs
    | zero => simp
    | add a b ha hb' ia ib =>
        rw [map_add, ternaryRatDot_add_left, ternaryRatDot_add_left, ia, ib]
    | smul c a ha ia =>
        rw [map_smul, ternaryRatDot_smul_left, ternaryRatDot_smul_left, ia]
  have hdot : ∀ x y, ternaryRatDot (T x) (T y) = ternaryRatDot x y := by
    intro x y
    have hy : y ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hTb]
        exact hcross x (b i) (hb i)
    | zero => simp
    | add a b ha hb' ia ib =>
        rw [map_add, ternaryRatDot_add_right, ternaryRatDot_add_right, ia, ib]
    | smul c a ha ia =>
        rw [map_smul, ternaryRatDot_smul_right, ternaryRatDot_smul_right, ia]
  refine ⟨T, ?_, hdot⟩
  intro x hx
  apply sub_eq_zero.mp
  apply (ternaryRatNorm_eq_zero_iff _).mp
  rw [ternaryRatNorm_sub, ← ternaryRatDot_self, ← ternaryRatDot_self,
    hdot, hcross x x hx, hpair x hx x hx]
  ring

/-- The spanning-set theorem also applies to indexed families, even when
the indexing contains duplicate vectors. Preservation of the Gram matrix
itself proves that duplicate sources have equal images. -/
theorem exists_linear_of_spanning_gram_family {ι : Type*}
    (a b : ι → TernaryRatPoint) (hspan : Submodule.span ℚ (Set.range a) = ⊤)
    (hgram : ∀ i j, ternaryRatDot (b i) (b j) = ternaryRatDot (a i) (a j)) :
    ∃ T : TernaryRatPoint →ₗ[ℚ] TernaryRatPoint,
      (∀ i, T (a i) = b i) ∧
      (∀ x y, ternaryRatDot (T x) (T y) = ternaryRatDot x y) := by
  classical
  have hconsistent : ∀ i j, a i = a j → b i = b j := by
    intro i j hij
    apply sub_eq_zero.mp
    apply (ternaryRatNorm_eq_zero_iff _).mp
    rw [ternaryRatNorm_sub, ← ternaryRatDot_self, ← ternaryRatDot_self,
      hgram, hgram, hgram, hij]
    ring
  let f : TernaryRatPoint → TernaryRatPoint := fun x =>
    if hx : ∃ i, a i = x then b hx.choose else 0
  have hf : ∀ i, f (a i) = b i := by
    intro i
    dsimp [f]
    split_ifs with hx
    · exact hconsistent _ _ hx.choose_spec
    · exact False.elim (hx ⟨i,rfl⟩)
  obtain ⟨T,hT,hdot⟩ := exists_linear_of_spanning_dot_pairing (Set.range a) hspan f (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    rw [hf,hf]
    exact hgram i j)
  exact ⟨T, fun i => (hT (a i) ⟨i,rfl⟩).trans (hf i), hdot⟩

/-- Involutivity and the two noncentral witnesses also extend from the
spanning set. -/
theorem exists_orthogonal_involution_of_spanning_pairing
    (S : Set TernaryRatPoint) (hspan : Submodule.span ℚ S = ⊤)
    (f : TernaryRatPoint → TernaryRatPoint)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, ternaryRatDot (f x) (f y) = ternaryRatDot x y)
    (hclosed : ∀ x ∈ S, f x ∈ S)
    (hinvol : ∀ x ∈ S, f (f x) = x)
    (hne : ∃ x ∈ S, f x ≠ x)
    (hneneg : ∃ x ∈ S, f x ≠ -x) :
    ∃ T : RationalTernaryOrthogonalInvolution, ∀ x ∈ S, T.linear x = f x := by
  obtain ⟨T, hT, hdot⟩ := exists_linear_of_spanning_dot_pairing S hspan f hpair
  have hinv : ∀ x, T (T x) = x := by
    intro x
    have hx : x ∈ Submodule.span ℚ S := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => rw [hT x hx, hT (f x) (hclosed x hx), hinvol x hx]
    | zero => simp
    | add a b ha hb ia ib => simp only [map_add, ia, ib]
    | smul c a ha ia => simp only [map_smul, ia]
  refine ⟨{
    linear := T
    norm_preserving := fun x => by simpa only [ternaryRatDot_self] using hdot x x
    involutive := hinv
    not_identity := ?_
    not_neg_identity := ?_
  }, hT⟩
  · obtain ⟨x,hx,hnx⟩ := hne
    exact ⟨x, by rwa [hT x hx]⟩
  · obtain ⟨x,hx,hnx⟩ := hneneg
    exact ⟨x, by rwa [hT x hx]⟩

end Ramanujan.MultiQuintuple
