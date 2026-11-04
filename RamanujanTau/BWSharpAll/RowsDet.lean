import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Linearly independent power series have a nonzero square coefficient minor
-/

set_option autoImplicit false

namespace RamanujanTau.BWSharpAll
open PowerSeries

/-- If `v₀, …, v_{n-1}` are linearly independent power series over a field, some choice of
`n` coefficient indices gives a nonzero `n × n` minor. -/
theorem exists_rows_det_ne_zero {K : Type*} [Field K] {n : ℕ} (v : Fin n → PowerSeries K)
    (hv : LinearIndependent K v) :
    ∃ rows : Fin n → ℕ, Matrix.det (fun i j => coeff (rows i) (v j)) ≠ 0 := by
  classical
  set r : ℕ → (Fin n → K) := fun t j => coeff t (v j)
  have hspan : Submodule.span K (Set.range r) = ⊤ := by
    by_contra h
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr h) inferInstance
    set c : Fin n → K := fun j => f (fun i => if j = i then 1 else 0)
    have hfx : ∀ x : Fin n → K, f x = ∑ j, x j * c j := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      rfl
    have hrel : ∑ j, c j • v j = 0 := by
      ext t
      have : f (r t) = 0 := by
        have hmem : f (r t) ∈ (Submodule.span K (Set.range r)).map f :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨t, rfl⟩)
        rw [hmap] at hmem
        exact (Submodule.mem_bot K).mp hmem
      rw [hfx] at this
      simp only [map_sum, LinearMap.map_smul, smul_eq_mul, map_zero]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by simp [r]; ring
    have hc0 := Fintype.linearIndependent_iff.mp hv c hrel
    apply hf
    apply LinearMap.ext
    intro x
    rw [hfx]
    simp [hc0]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range r)
  rw [hspan] at hbspan
  let B := Module.Basis.mk hbli (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan])
  haveI : Fintype b := by
    haveI := hbli.finite
    exact Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ t, r t = (e i : Fin n → K) := fun i => hbsub (e i).2
  choose rows hrows using hmem
  refine ⟨rows, ?_⟩
  have hM : (fun i j => coeff (rows i) (v j)) = Matrix.of fun i => (e i : Fin n → K) := by
    ext i j
    rw [Matrix.of_apply, ← hrows i]
  rw [hM]
  have hli : LinearIndependent K (fun i => (Matrix.of fun i => (e i : Fin n → K)) i) := by
    simpa using hbli.comp e e.injective
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
    |>.ne_zero
