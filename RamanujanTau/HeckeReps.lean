import RamanujanTau.HeckeConstruction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # `T_p` construction, steps 1–2: embed the representatives, reduce `S`-invariance to a coset bijection

Building on `HeckeConstruction`. We carry out **step 1** (embed Mathlib's coset representatives `reps p`
into `GL (Fin 2) ℝ`) and the provable **structural core of step 2** (slashing the Hecke-sum by any
`γ ∈ SL₂(ℤ)` equals the sum over the right-translated matrices `A·γ`).

What remains for full `S`-invariance — and it is the genuine crux — is the **coset bijection**: for a
modular `f`, each `A·S` lies in the `SL₂(ℤ)`-coset of a unique representative `reduce (A·S) ∈ reps p`, and
`A ↦ reduce (A·S)` is a *permutation of `reps p`*. Then
`f ∣[k] (A·S) = f ∣[k] reduce (A·S)` (absorbing the `SL₂(ℤ)` factor by modularity of `f`), and reindexing
along the permutation returns the original sum. The missing ingredients are purely on the Mathlib side:
`reduce` is constant on `SL₂(ℤ)`-orbits and fixes `reps` (so `reps` is a transversal) — lemmas not yet in
`FixedDetMatrices`. We do **not** fake them; they are the next real step.
-/

open scoped ModularForm MatrixGroups UpperHalfPlane
open ModularForm UpperHalfPlane

namespace RamanujanTau

/-- **Step 1.** Embed a det-`p` integer matrix into `GL (Fin 2) ℝ` (cast entries; `det = p ≠ 0`). -/
noncomputable def toGLℝ {p : ℕ} (hp : 0 < p) (A : FixedDetMatrix (Fin 2) ℤ (p : ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (A.1.map (Int.castRingHom ℝ)) (by
    have hdet : (A.1.map (Int.castRingHom ℝ)).det = (p : ℝ) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, A.2]; simp
    rw [hdet]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hp.ne'))

/-- **Step 1.** The Hecke representatives at `p`, embedded as a finite family in `GL (Fin 2) ℝ`. The
operator is then `T_p f = slashSum k (heckeReps p hp) f` (up to the standard normalization). -/
noncomputable def heckeReps (p : ℕ) (hp : 0 < p) : Finset (GL (Fin 2) ℝ) :=
  (FixedDetMatrices.reps (p : ℤ)).toFinset.image (toGLℝ hp)

/-- **Step 2 (structural core).** Slashing the Hecke-sum by `γ ∈ SL₂(ℤ)` equals the sum over the
right-translated matrices `A·γ`. This is the verified first half of `S`/`T`-invariance; the remaining
half is the coset bijection `A ↦ reduce (A·γ)` on `reps p` (see the module docstring). -/
theorem slashSum_slash_SL (k : ℤ) (s : Finset (GL (Fin 2) ℝ)) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    slashSum k s f ∣[k] γ = ∑ A ∈ s, f ∣[k] (A * (γ : GL (Fin 2) ℝ)) := by
  unfold slashSum
  rw [SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [ModularForm.SL_slash, ← SlashAction.slash_mul]

end RamanujanTau
