import RamanujanTau.HeckeBridge.Tate

/-!
# Transporting `TateKernels` along a field extension

`TateKernels p F ι₀ ζ` makes sense over any field `F` (it is only *used* over an algebraically
closed `L`). If the Tate addition theorem is proved over some field `F` receiving `K⟦t⟧`
(e.g. `LaurentSeries K` or `FractionRing K⟦t⟧`), then `tateKernels_lift` moves it to any extension
`L` of `F`, e.g. `AlgebraicClosure F`, as needed by `hT_of_kernels`.

* `aC_lift`, `bC_lift`, `ptR_veluC_lift` — Vélu's coefficients commute with `E(F) ↪ E(L)`.
* **`tateKernels_lift`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum TorsionSpec TateQuot

section Lift
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq F] [DecidableEq L] (a b : F)

lemma xc_liftPt (P : (short a b).Point) : xc (liftPt (L := L) a b P) = algebraMap F L (xc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (algebraMap F L)).symm
  · rfl

lemma yc_liftPt (P : (short a b).Point) : yc (liftPt (L := L) a b P) = algebraMap F L (yc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (algebraMap F L)).symm
  · rfl

lemma sum_lift_erase (G : Finset (short a b).Point)
    (Φ : (short (algebraMap F L a) (algebraMap F L b)).Point → L) :
    ∑ P ∈ (G.image (liftPt (L := L) a b)).erase 0, Φ P = ∑ P ∈ G.erase 0, Φ (liftPt a b P) := by
  have : (G.image (liftPt (L := L) a b)).erase 0 = (G.erase 0).image (liftPt a b) := by
    rw [← liftPt_zero (L := L) a b, Finset.image_erase (liftPt_injective a b)]
  rw [this, Finset.sum_image fun P _ Q _ h => liftPt_injective a b h]

lemma aC_lift (G : Finset (short a b).Point) :
    aC (G.image (liftPt (L := L) a b)) = algebraMap F L (aC G) := by
  simp only [aC, tSum, sum_lift_erase, Kernel.tQ, xc_liftPt, map_sub, map_mul, map_div₀, map_sum,
    map_add, map_pow, map_ofNat]

lemma bC_lift (G : Finset (short a b).Point) :
    bC (G.image (liftPt (L := L) a b)) = algebraMap F L (bC G) := by
  simp only [bC, wSum, sum_lift_erase, Kernel.tQ, Kernel.uQ, xc_liftPt, yc_liftPt, map_sub,
    map_mul, map_div₀, map_sum, map_add, map_pow, map_ofNat]

lemma ptR_veluC_lift (G : Finset (short a b).Point) :
    HeckeQExp.ptR (veluC (G.image (liftPt (L := L) a b))) =
      fun i => algebraMap F L (HeckeQExp.ptR (veluC G) i) := by
  rw [ptR_veluC, ptR_veluC, aC_lift, bC_lift]
  funext i; fin_cases i <;> simp [map_ofNat]

lemma image_lift_mem_subs {n : ℕ} {G : Finset (short a b).Point} (hG : G ∈ subs a b n) :
    G.image (liftPt (L := L) a b) ∈ subs (algebraMap F L a) (algebraMap F L b) n := by
  refine ⟨⟨Finset.mem_image.2 ⟨0, hG.1.1, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro P hP Q hQ
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_image.2 ⟨P' + Q', hG.1.2.1 _ hP' _ hQ', liftPt_add a b _ _⟩
  · intro P hP
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_image.2 ⟨-P', hG.1.2.2 _ hP', (liftHom (L := L) a b).map_neg P'⟩
  · rw [Finset.card_image_of_injective _ (liftPt_injective a b), hG.2]

end Lift

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

/-- **`TateKernels` over `F` gives `TateKernels` over any extension `L` of `F`.** -/
theorem tateKernels_lift {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq F]
    [DecidableEq L] (ι₀ : PowerSeries K →+* F) (ζ : K) (h : TateKernels p F ι₀ ζ) :
    TateKernels p L ((algebraMap F L).comp ι₀) ζ := by
  obtain ⟨G, hmem, hinj, hptR⟩ := h
  refine ⟨fun c => (G c).image (liftPt (L := L) _ _), fun c => image_lift_mem_subs _ _ (hmem c),
    fun c d hcd => hinj (Finset.image_injective (liftPt_injective _ _) hcd), fun c => ?_⟩
  rw [ptR_veluC_lift, hptR c]
  rfl

end HeckeBridge
