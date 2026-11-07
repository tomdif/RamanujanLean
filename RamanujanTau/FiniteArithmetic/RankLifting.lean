import RamanujanTau.FiniteArithmetic.DeterminantRank

/-!
# Predicting the precision at which a divided relation becomes visible

If one generator is a combination of the others plus `p^d` times a new
direction, and replacing it by that direction gives a unit determinant,
then its determinant is nonzero modulo `p^m` exactly when `d < m`.
This is a general algebraic criterion, not a prime-607 numerical certificate.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic
noncomputable section

/-- Dividing a relation extracts its exact contribution to an alternating
determinant. The coefficient of the replaced vector in the old sum is zero. -/
theorem alternating_eq_mul_of_relation {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[R] R) (v : Fin n → M) (j : Fin n)
    (c : Fin n → R) (hc : c j = 0) (a : R) (w : M)
    (hrel : v j = (∑ i, c i • v i) + a • w) :
    f v = a * f (Function.update v j w) := by
  classical
  calc
    f v = f (Function.update v j (v j)) := by rw [Function.update_eq_self]
    _ = f (Function.update v j (∑ i, c i • v i)) +
        f (Function.update v j (a • w)) := by rw [hrel, f.map_update_add]
    _ = 0 + a * f (Function.update v j w) := by
      congr 1
      · rw [f.map_update_sum]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i = j
        · subst i
          simp [hc]
        · rw [f.map_update_smul]
          have hz : f (Function.update v j (v i)) = 0 :=
            f.map_eq_zero_of_eq _ (i := j) (j := i) (by simp [hi]) (Ne.symm hi)
          rw [hz, smul_zero]
      · rw [f.map_update_smul, smul_eq_mul]
    _ = _ := zero_add _

/-- A factor `p^d` is first visible at precision `p^(d+1)`. -/
theorem prime_pow_ne_zero_iff (p d m : ℕ) (hp : 1 < p) :
    (p : ZMod (p ^ m)) ^ d ≠ 0 ↔ d < m := by
  rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff,
    Nat.pow_dvd_pow_iff_le_right hp]
  omega

/-- A unit divided-relation determinant predicts the exact first precision
at which the original determinant is nonzero. -/
theorem relation_visible_iff {p d m n : ℕ} (hp : 1 < p)
    {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M]
    (f : M [⋀^Fin n]→ₗ[ZMod (p ^ m)] ZMod (p ^ m))
    (v : Fin n → M) (j : Fin n) (c : Fin n → ZMod (p ^ m))
    (hc : c j = 0) (w : M)
    (hrel : v j = (∑ i, c i • v i) + (p : ZMod (p ^ m)) ^ d • w)
    (hunit : IsUnit (f (Function.update v j w))) :
    f v ≠ 0 ↔ d < m := by
  rw [alternating_eq_mul_of_relation f v j c hc _ w hrel]
  rw [Ne, hunit.mul_left_eq_zero, ← Ne, prime_pow_ne_zero_iff p d m hp]

/-- Above the predicted precision, every generating set needs at least `n`
elements. This works over the prime-power ring, including its zero divisors. -/
theorem card_le_of_lifted_relation {p d m n : ℕ} (hp : 1 < p) (hdm : d < m)
    {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M]
    (f : M [⋀^Fin n]→ₗ[ZMod (p ^ m)] ZMod (p ^ m))
    (v : Fin n → M) (j : Fin n) (c : Fin n → ZMod (p ^ m))
    (hc : c j = 0) (w : M)
    (hrel : v j = (∑ i, c i • v i) + (p : ZMod (p ^ m)) ^ d • w)
    (hunit : IsUnit (f (Function.update v j w)))
    (s : Finset M) (hs : ∀ i, v i ∈ Submodule.span (ZMod (p ^ m)) (s : Set M)) :
    n ≤ s.card :=
  card_le_of_alternating_ne_zero f v s hs
    ((relation_visible_iff hp f v j c hc w hrel hunit).mpr hdm)

/-- A divided orbit relation determines the entire orbit lattice when the
old iterates together with the divided remainder span the ambient module.
Specializing `a = p^d` and making those vectors a basis gives Smith exponents
`0,...,0,d`, hence first appearance of the last generator at precision `d+1`. -/
theorem orbit_span_eq_of_divided_relation {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (T : Module.End R M) (y w : M)
    (r : ℕ) (c : Fin r → R) (a : R)
    (hrel : (T ^ r) y = (∑ i : Fin r, c i • (T ^ (i : ℕ)) y) + a • w)
    (hspan : Submodule.span R (Set.range (fun i : Fin r => (T ^ (i : ℕ)) y) ∪ {w}) = ⊤) :
    Submodule.span R (Set.range (fun k : ℕ => (T ^ k) y)) =
      Submodule.span R (Set.range (fun i : Fin r => (T ^ (i : ℕ)) y) ∪ {a • w}) := by
  classical
  let H := Submodule.span R (Set.range (fun i : Fin r => (T ^ (i : ℕ)) y) ∪ {a • w})
  have hold (i : Fin r) : (T ^ (i : ℕ)) y ∈ H :=
    Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have haw : a • w ∈ H := Submodule.subset_span (Or.inr rfl)
  have hsum : (∑ i : Fin r, c i • (T ^ (i : ℕ)) y) ∈ H :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hold i)
  have hmul (z : M) : a • z ∈ H := by
    have hz : z ∈ Submodule.span R (Set.range (fun i : Fin r => (T ^ (i : ℕ)) y) ∪ {w}) := by
      rw [hspan]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | rfl
      · exact Submodule.smul_mem _ _ (hold i)
      · exact haw
    | zero => simpa using H.zero_mem
    | add x z _ _ hx hz => simpa only [smul_add] using H.add_mem hx hz
    | smul b z _ hz => simpa only [smul_comm a b] using H.smul_mem b hz
  have hstable : ∀ z ∈ H, T z ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | rfl
      · rw [← Module.End.mul_apply, ← pow_succ']
        by_cases hi : (i : ℕ) + 1 < r
        · exact hold ⟨(i : ℕ) + 1, hi⟩
        · have he : (i : ℕ) + 1 = r := by have := i.isLt; omega
          rw [he, hrel]
          exact H.add_mem hsum haw
      · rw [map_smul]
        exact hmul (T w)
    | zero => simpa using H.zero_mem
    | add x z _ _ hx hz => simpa only [map_add] using H.add_mem hx hz
    | smul b z _ hz => simpa only [map_smul] using H.smul_mem b hz
  have hy : y ∈ H := by
    by_cases hr : r = 0
    · subst r
      have h := H.add_mem hsum haw
      rw [← hrel] at h
      simpa only [pow_zero, Module.End.one_apply] using h
    · simpa only [pow_zero, Module.End.one_apply] using hold ⟨0, by omega⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change (T ^ k) y ∈ H
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hy
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hstable _ ih
  · apply Submodule.span_le.mpr
    rintro z (⟨i, rfl⟩ | rfl)
    · exact Submodule.subset_span ⟨(i : ℕ), rfl⟩
    · have he : a • w = (T ^ r) y - ∑ i : Fin r, c i • (T ^ (i : ℕ)) y := by
        rw [hrel]; abel
      rw [he]
      apply Submodule.sub_mem
      · exact Submodule.subset_span ⟨r, rfl⟩
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨(i : ℕ), rfl⟩)

end
end RamanujanTau.FiniteArithmetic
