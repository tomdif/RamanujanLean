import RamanujanTau.Velu.Defs

/-!
# Vélu: summation over the kernel

Reindexing lemmas for sums over the finite subgroup `G` and its half-system `S`.
-/

namespace Velu

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

lemma mem_G_iff (P : (short A B).Point) :
    P ∈ κ.G ↔ P ∈ insert 0 (κ.S ∪ κ.S.image Neg.neg) := by
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hP
    by_cases h0 : P = 0
    · exact Or.inl h0
    · rcases κ.cover P hP h0 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨-P, h, neg_neg P⟩)
  · rintro (h | h | ⟨Q, hQ, rfl⟩)
    · exact h ▸ κ.zero_mem
    · exact κ.S_sub h
    · exact κ.neg_mem Q (κ.S_sub hQ)

lemma G_eq : κ.G = insert 0 (κ.S ∪ κ.S.image Neg.neg) := by
  ext P; exact κ.mem_G_iff P

/-- `Σ_{V∈G} g V = g 0 + Σ_{Q∈S} (g Q + g (-Q))`. -/
lemma sum_G {M : Type*} [AddCommMonoid M] (g : (short A B).Point → M) :
    ∑ V ∈ κ.G, g V = g 0 + ∑ Q ∈ κ.S, (g Q + g (-Q)) := by
  rw [κ.G_eq, Finset.sum_insert, Finset.sum_union, Finset.sum_image, Finset.sum_add_distrib]
  · intro a _ b _ h; exact neg_injective h
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP'
    exact κ.neg_not_mem_S Q hQ hP
  · simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨κ.zero_not_mem_S, fun Q hQ h => ?_⟩
    rw [neg_eq_zero] at h
    exact κ.zero_not_mem_S (h ▸ hQ)

/-- Translation invariance of sums over `G`. -/
lemma sum_G_translate {M : Type*} [AddCommMonoid M] (g : (short A B).Point → M)
    {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.G) :
    ∑ V ∈ κ.G, g (Q0 + V) = ∑ V ∈ κ.G, g V := by
  refine Finset.sum_nbij' (fun V => Q0 + V) (fun V => -Q0 + V) ?_ ?_ ?_ ?_ ?_
  · intro V hV; exact κ.add_mem _ hQ0 _ hV
  · intro V hV; exact κ.add_mem _ (κ.neg_mem _ hQ0) _ hV
  · intro V _; simp
  · intro V _; simp
  · intro V _; rfl

/-- The basic reindexing: `{Q₀ ± Q : Q ∈ S ∖ {Q₀}} = G ∖ {0, Q₀, 2Q₀}`. -/
lemma sum_pairs {M : Type*} [AddCommGroup M] (g : (short A B).Point → M)
    {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) :
    ∑ Q ∈ κ.S.erase Q0, (g (Q0 + Q) + g (Q0 + -Q)) =
      ∑ Q ∈ κ.S, (g Q + g (-Q)) - g Q0 - g (Q0 + Q0) := by
  have h1 := κ.sum_G_translate g (κ.S_sub hQ0)
  rw [κ.sum_G (fun V => g (Q0 + V)), κ.sum_G g, ← Finset.add_sum_erase _ _ hQ0] at h1
  simp only [add_zero, add_neg_cancel] at h1
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h1
  rw [← h1]
  abel

lemma ne_zero_of_mem_S {Q : (short A B).Point} (hQ : Q ∈ κ.S) : Q ≠ 0 := by
  rintro rfl; exact κ.zero_not_mem_S hQ

lemma yc_ne_zero_of_mem_G {P : (short A B).Point} (hP : P ∈ κ.G) (h0 : P ≠ 0) :
    yc P ≠ 0 := by
  intro hy
  obtain ⟨h, eP⟩ := eq_some_of_ne_zero h0
  apply h0
  apply κ.no_two_torsion P hP
  rw [eP]
  apply Affine.Point.add_self_of_Y_eq
  simp [Affine.negY, hy]

lemma yc_ne_zero {Q : (short A B).Point} (hQ : Q ∈ κ.S) : yc Q ≠ 0 :=
  κ.yc_ne_zero_of_mem_G (κ.S_sub hQ) (κ.ne_zero_of_mem_S hQ)

omit [DecidableEq K] in
lemma eq_or_eq_neg_of_xc_eq {P Q : (short A B).Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : xc P = xc Q) : P = Q ∨ P = -Q := by
  obtain ⟨hP', eP⟩ := eq_some_of_ne_zero hP
  obtain ⟨hQ', eQ⟩ := eq_some_of_ne_zero hQ
  rw [eP, eQ]
  exact (Affine.Point.X_eq_iff).1 h

lemma xc_injOn : Set.InjOn (xc (A := A) (B := B)) (κ.S : Set (short A B).Point) := by
  intro P hP Q hQ h
  rcases eq_or_eq_neg_of_xc_eq (κ.ne_zero_of_mem_S hP) (κ.ne_zero_of_mem_S hQ) h with h' | h'
  · exact h'
  · exact absurd (h' ▸ hP) (κ.neg_not_mem_S Q hQ)

lemma xc_ne_of_mem_S {P Q : (short A B).Point} (hP : P ∈ κ.S) (hQ : Q ∈ κ.S) (hne : P ≠ Q) :
    xc P ≠ xc Q := fun h => hne (κ.xc_injOn hP hQ h)

/-- A point outside `G` has `x`-coordinate different from all `x_Q`, `Q ∈ S`. -/
lemma xc_ne_of_not_mem_G {P : (short A B).Point} (hP0 : P ≠ 0) (hP : P ∉ κ.G)
    {Q : (short A B).Point} (hQ : Q ∈ κ.S) : xc P ≠ xc Q := by
  intro h
  rcases eq_or_eq_neg_of_xc_eq hP0 (κ.ne_zero_of_mem_S hQ) h with h' | h'
  · exact hP (h' ▸ κ.S_sub hQ)
  · exact hP (h' ▸ κ.neg_mem _ (κ.S_sub hQ))

end Kernel

end Velu
