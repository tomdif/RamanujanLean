import RamanujanTau.Velu.Defs
import Mathlib.GroupTheory.OrderOfElement

/-!
# Vélu: kernel data from a finite subgroup of odd order

Every finite subgroup `H ⊂ E(K)` of odd order gives Vélu kernel data `κ` with `κ.G = H`.
-/

namespace Velu

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

/-- A canonical representative of `{P, -P}`. -/
noncomputable def pmRep (P : (short A B).Point) : (short A B).Point :=
  Classical.epsilon fun Q => Q = P ∨ Q = -P

omit [DecidableEq K] in
lemma pmRep_spec (P : (short A B).Point) : pmRep P = P ∨ pmRep P = -P :=
  Classical.epsilon_spec (p := fun Q => Q = P ∨ Q = -P) ⟨P, Or.inl rfl⟩

omit [DecidableEq K] in
lemma pmRep_neg (P : (short A B).Point) : pmRep (-P) = pmRep P := by
  unfold pmRep
  congr 1
  funext Q
  rw [neg_neg, or_comm]

/-- **Existence of Vélu kernel data** for a finite subgroup of odd order. -/
theorem exists_kernel (H : AddSubgroup (short A B).Point) [Finite H] (hodd : Odd (Nat.card H)) :
    ∃ κ : Kernel A B, (κ.G : Set (short A B).Point) = H := by
  classical
  have hfin : (H : Set (short A B).Point).Finite := Set.toFinite _
  set G := hfin.toFinset with hG
  have memG : ∀ P, P ∈ G ↔ P ∈ H := fun P => by simp [hG]
  have h2t : ∀ P ∈ G, P + P = 0 → P = 0 := by
    intro P hP hPP
    rw [memG] at hP
    have hd1 : addOrderOf (⟨P, hP⟩ : H) ∣ Nat.card H := addOrderOf_dvd_natCard _
    have hd2 : addOrderOf (⟨P, hP⟩ : H) ∣ 2 := by
      apply addOrderOf_dvd_of_nsmul_eq_zero
      ext; simp [two_nsmul, hPP]
    have h1 : addOrderOf (⟨P, hP⟩ : H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
      · exact h
      · rw [h] at hd1
        exact absurd (even_iff_two_dvd.2 hd1) (Nat.not_even_iff_odd.2 hodd)
    have := AddMonoid.addOrderOf_eq_one_iff.1 h1
    simpa using congrArg Subtype.val this
  set S := G.filter fun P => P ≠ 0 ∧ pmRep P = P with hS
  have hneg_ne : ∀ P ∈ G, P ≠ 0 → -P ≠ P := by
    intro P hP h0 h
    exact h0 (h2t P hP (by nth_rewrite 1 [← h]; exact neg_add_cancel P))
  refine ⟨Kernel.mk G S ?_ ?_ ?_ h2t ?_ ?_ ?_ ?_, ?_⟩
  · rw [memG]; exact H.zero_mem
  · intro P hP Q hQ; rw [memG] at *; exact H.add_mem hP hQ
  · intro P hP; rw [memG] at *; exact H.neg_mem hP
  · exact Finset.filter_subset _ _
  · simp [hS]
  · intro Q hQ hQ'
    simp only [hS, Finset.mem_filter] at hQ hQ'
    rw [pmRep_neg, hQ.2.2] at hQ'
    exact hneg_ne Q hQ.1 hQ.2.1 hQ'.2.2.symm
  · intro P hP h0
    simp only [hS, Finset.mem_filter]
    rcases pmRep_spec P with h | h
    · exact Or.inl ⟨hP, h0, h⟩
    · refine Or.inr ⟨?_, neg_ne_zero.2 h0, by rw [pmRep_neg, h]⟩
      rw [memG] at *; exact H.neg_mem hP
  · ext P; simp [hG]

end Velu
