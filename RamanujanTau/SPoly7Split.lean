/-
# Split certificates

A large identity `N = Σ_p (piece p)` with each piece known to vanish is checked block by block: every piece
and `N` are concatenations of blocks (`List Poly`, the same number `nb` of blocks), and for each block
`N_b = Σ_p piece_{p,b}` is a separate small kernel check. Soundness only uses evaluation:
`Σ_b N_b = Σ_b Σ_p piece_{p,b} = Σ_p Σ_b piece_{p,b} = Σ_p 0`.
-/
import RamanujanTau.SPoly7Fast
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace SPoly7

variable {R : Type*} [CommRing R]

lemma evalP_flatten' (x : List R) (l : List Poly) : evalP x l.flatten = (l.map (evalP x)).sum := by
  induction l with
  | nil => simp [evalP]
  | cons a l ih => rw [List.flatten_cons, evalP_append, ih, List.map_cons, List.sum_cons]

/-- **block assembly**. -/
theorem assemble (x : List R) (nb : ℕ) (Ns : List Poly) (Rs : List (List Poly)) (hN : Ns.length = nb)
    (hlen : ∀ r ∈ Rs, r.length = nb)
    (hsum : ∀ b < nb, evalP x (Ns.getD b []) = (Rs.map fun r => evalP x (r.getD b [])).sum)
    (hzero : ∀ r ∈ Rs, evalP x r.flatten = 0) : evalP x Ns.flatten = 0 := by
  rw [evalP_flatten']
  have h1 : (Ns.map (evalP x)).sum = ∑ b ∈ Finset.range nb, evalP x (Ns.getD b []) := by
    rw [← hN]
    clear hN hsum
    induction Ns using List.reverseRecOn with
    | nil => simp
    | append_singleton l a ih =>
      rw [List.map_append, List.sum_append, ih, List.length_append, List.length_singleton, Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hb)]
      · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  have h2 : ∀ r ∈ Rs, (∑ b ∈ Finset.range nb, evalP x (r.getD b [])) = 0 := by
    intro r hr
    have := hzero r hr
    rw [evalP_flatten'] at this
    rw [← this, ← hlen r hr]
    clear this hr
    induction r using List.reverseRecOn with
    | nil => simp
    | append_singleton l a ih =>
      rw [List.map_append, List.sum_append, ← ih, List.length_append, List.length_singleton, Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hb)]
      · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  rw [h1, Finset.sum_congr rfl fun b hb => hsum b (Finset.mem_range.mp hb)]
  have : ∀ b ∈ Finset.range nb, (Rs.map fun r => evalP x (r.getD b [])).sum =
      ∑ r ∈ Finset.range Rs.length, evalP x ((Rs.getD r []).getD b []) := by
    intro b _
    clear hsum hzero h2 hlen
    induction Rs using List.reverseRecOn with
    | nil => simp
    | append_singleton l a ih =>
      rw [List.map_append, List.sum_append, ih, List.length_append, List.length_singleton, Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun r hr => ?_
        rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hr)]
      · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hr)]
  exact h2 _ (List.getElem_mem _)

end SPoly7
