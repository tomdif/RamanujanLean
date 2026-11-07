import RamanujanTau.BLBound.RankGrowth

/-! Nonzero coefficient determinants bound the number of generators, even
over a ring with zero divisors. The prime-607 application deliberately retains
its numerical arithmetic input as an explicit hypothesis. -/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic
noncomputable section

theorem card_le_of_alternating_ne_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] R)
    (v : Fin n → M) (s : Finset M) (hv : ∀ i, v i ∈ Submodule.span R (s : Set M))
    (hne : f v ≠ 0) : n ≤ s.card := by
  classical
  by_contra hcard
  have hlt : s.card < n := by omega
  choose c hc using fun i => Submodule.mem_span_finset'.mp (hv i)
  apply hne
  have he : v = fun i => ∑ a : s, c i a • (a : M) := funext fun i => (hc i).symm
  rw [he]
  change f.toMultilinearMap (fun i => ∑ a : s, c i a • (a : M)) = 0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro r _
  change f (fun i => c i (r i) • ((r i : s) : M)) = 0
  rw [f.map_smul_univ]
  have hni : ¬ Function.Injective (fun i => ((r i : s) : M)) := by
    intro hinj
    have hr : Function.Injective r := fun a b h => hinj (congrArg Subtype.val h)
    have := Fintype.card_le_of_injective r hr
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  rw [f.map_eq_zero_of_not_injective _ hni, smul_zero]

/-- A nonzero `n`-by-`n` coefficient minor excludes generation by fewer than
`n` elements. Nonzero means nonzero, not necessarily invertible. -/
theorem card_le_of_coeff_det_ne_zero {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → PowerSeries R) (rows : Fin n → ℕ) (s : Finset (PowerSeries R))
    (hv : ∀ i, v i ∈ Submodule.span R (s : Set _))
    (hdet : Matrix.det (fun i j => PowerSeries.coeff (rows i) (v j)) ≠ 0) :
    n ≤ s.card := by
  let obs : PowerSeries R →ₗ[R] (Fin n → R) := LinearMap.pi fun i => PowerSeries.coeff (rows i)
  apply card_le_of_alternating_ne_zero (Matrix.detRowAlternating.compLinearMap obs) v s hv
  change (Matrix.transpose (fun i j => PowerSeries.coeff (rows i) (v j))).det ≠ 0
  rwa [Matrix.det_transpose]

open PowerSeries BoylanWebb BLBound

private instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- The exact remaining arithmetic target: coefficients q^26 through q^50
of the actual L(3), L(5), ..., L(51), modulo 607^2. -/
def rank607Matrix : Matrix (Fin 25) (Fin 25) (ZMod (607 ^ 2)) :=
  fun i j => coeff (i.val + 26) (redm 607 2 (L 607 (2 * j.val + 3)))

/-- A single nonzero determinant at precision two settles every higher
generator rank. This theorem does not assert its determinant hypothesis. -/
theorem rank607_eq_of_det (hdet : rank607Matrix.det ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    rEll 607 m = 25 := by
  have hlower : 25 ≤ rEll 607 2 := by
    obtain ⟨s, -, hs⟩ := rank_Lam_le (ℓ := 607) (by norm_num) 2 (by norm_num) 1 (by norm_num)
    obtain ⟨s, hcard, hspan⟩ := Nat.sInf_mem
      (s := {r | ∃ s : Finset (PowerSeries (Rm 607 2)), s.card = r ∧
        Submodule.span (Rm 607 2) (s : Set _) = Lam 607 2 (2 * 2 - 1)})
      ⟨_, s, rfl, hs⟩
    have hc : 25 ≤ s.card := card_le_of_coeff_det_ne_zero
      (fun j : Fin 25 => redm 607 2 (L 607 (2 * j.val + 3)))
      (fun i : Fin 25 => i.val + 26) s (fun j => ?_) hdet
    · simpa only [hcard, rEll] using hc
    · rw [hspan]
      apply Submodule.subset_span
      exact ⟨j.val + 1, by omega, by congr 3⟩
  have h := rEll_eq_bound_of_le (ℓ := 607) (by norm_num) (by norm_num : 1 ≤ 2) hm hlower
  simpa using h

end
end RamanujanTau.FiniteArithmetic
