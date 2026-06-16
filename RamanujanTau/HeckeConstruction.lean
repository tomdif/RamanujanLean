import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! # Constructing the Hecke operator `T_p`: the foundation

The goal is to build a `HeckeData` term (see `HeckeOperator.lean`) — a genuine Hecke operator `T_p` on
`CuspForm 𝒮ℒ 12` with its `q`-expansion action — which would *unconditionally* discharge `TauHeckeMaster`
and the whole tower below it. This file is the **first, sorry-free step**: it defines the shape of `T_p`
(a weight-`k` slash-sum over a finite family of matrices) and proves the two structural facts that the
construction rests on, reusing Mathlib's already-formalized coset machinery.

Mathlib provides exactly the hard combinatorial core:
* `FixedDetMatrix (Fin 2) ℤ p` (`= Δ p`), `reps p` (the `SL₂(ℤ)`-coset representatives of det-`p`
  matrices), `reduce`/`reduce_mem_reps`/`induction_on` (Hermite-style reduction to a representative);
* the weight-`k` slash action of `GL (Fin 2) ℝ` on `ℍ → ℂ` (`SlashAction.add_slash`, `sum_slash`, …);
* `SlashInvariantForm.slash_action_generators_SL2Z`: a function is `SL₂(ℤ)`-modular **iff** it is
  invariant under the two generators `S` and `T`.

## What this file proves (kernel-verified, no `sorry`)
* `slashSum` — the candidate operator `f ↦ ∑_{A ∈ s} f ∣[k] A`.
* `slashSum_add` — additivity in `f` (half of ℂ-linearity).
* `slashSum_modular_of_S_T` — **the backbone**: `slashSum` is `SL₂(ℤ)`-modular as soon as it is `S`- and
  `T`-invariant, so the entire modularity obligation collapses to two generator checks.

## The remaining obligations (the roadmap to a `HeckeData` term)
1. **Embed** `reps p : Finset (Δ p)` into `Finset (GL (Fin 2) ℝ)` (cast entries to ℝ; `det = p > 0`).
2. **`S`/`T`-invariance** of `slashSum k (heckeReps p) f`: right-multiplying the representatives by `S`
   (resp. `T`) permutes the `SL₂(ℤ)`-cosets, so the sum is unchanged — this is where `reduce` /
   `induction_on` do the work. (Then `slashSum_modular_of_S_T` finishes modularity.)
3. **Holomorphy** and the **cusp condition** (sum of holomorphic slashes; bounded at `i∞`), packaging
   `T_p f : CuspForm 𝒮ℒ k`.
4. **`q`-expansion action** `(T_p f)_n = f_{p n} + p^{k-1} f_{n/p}` (the coset reps evaluated on
   `q`-expansions), giving the `HeckeData.hecke_action` field.

Steps 2–4 are substantial but standard (no research content). Completing them yields `HeckeData`, and
`HeckeData.tauHeckeMaster` then discharges `TauHeckeMaster` unconditionally.
-/

open scoped ModularForm MatrixGroups UpperHalfPlane
open ModularForm UpperHalfPlane ModularGroup

namespace RamanujanTau

/-- The weight-`k` slash-sum over a finite family of matrices — the shape of a Hecke operator
(`T_p f = ∑_{A ∈ reps p} f ∣[k] A`, once `reps p` is embedded in `GL (Fin 2) ℝ`). -/
noncomputable def slashSum (k : ℤ) (s : Finset (GL (Fin 2) ℝ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ A ∈ s, f ∣[k] A

/-- Additivity of the slash-sum in `f` (half of ℂ-linearity; the other half, `(c • f)`, is analogous). -/
theorem slashSum_add (k : ℤ) (s : Finset (GL (Fin 2) ℝ)) (f g : ℍ → ℂ) :
    slashSum k s (f + g) = slashSum k s f + slashSum k s g := by
  unfold slashSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => SlashAction.add_slash k A f g

/-- The slash-sum of `0` is `0`. -/
@[simp] theorem slashSum_zero (k : ℤ) (s : Finset (GL (Fin 2) ℝ)) :
    slashSum k s 0 = 0 := by
  unfold slashSum; simp

/-- **The modularity backbone.** A slash-sum is `SL₂(ℤ)`-modular as soon as it is invariant under the two
generators `S` and `T` — so the whole modularity obligation for `T_p f` reduces to two generator checks
(`Mathlib.SlashInvariantForm.slash_action_generators_SL2Z`). -/
theorem slashSum_modular_of_S_T (k : ℤ) (s : Finset (GL (Fin 2) ℝ)) (f : ℍ → ℂ)
    (hS : slashSum k s f ∣[k] S = slashSum k s f)
    (hT : slashSum k s f ∣[k] T = slashSum k s f) :
    ∀ γ : SL(2, ℤ), slashSum k s f ∣[k] γ = slashSum k s f :=
  SlashInvariantForm.slash_action_generators_SL2Z hS hT

end RamanujanTau
