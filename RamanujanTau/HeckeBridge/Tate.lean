import RamanujanTau.HeckeBridge.Alg
import RamanujanTau.TateQuot.Main
import RamanujanTau.TateCurve.Laurent

/-!
# `hT` of `HeckeQExp.classical_hU`, modulo the Tate addition theorem (`TateKernels`)

Let `A = eP(Ash)`, `B = eP(Bsh) ∈ K⟦t⟧` be the short model of `tateBase` (`q = t^p`), and let
`ι : K⟦t⟧ → L` be an injective ring map into an algebraically closed field of characteristic `0`
(e.g. `L = AlgebraicClosure (LaurentSeries K)` or `AlgebraicClosure (FractionRing K⟦t⟧)`).

* **`TateKernels p L ι ζ`** (the hypothesis `hKer`, to be supplied by the Tate addition theorem):
  there are `p + 1` *distinct* subgroups `G c` of order `p` of `E(L)`, `E = short (ιA) (ιB)`,
  whose Vélu quotients have `ptR (E/G c) = ι (ptR (veluQuot ζ p c))`.
  (`tateKernels_of_kernels`: it suffices to give Vélu kernel data `κ c` of cardinality `p` with
  distinct `G`'s and `κ.curve = (veluQuot ζ p c).map ι`.)
  Exhaustiveness is *not* assumed: it follows from `#E[p] = p²` (`surj_of_inj_algClosed`).
* `tate_disc_ne` — `4A³ + 27B² ≠ 0` in `K⟦t⟧` (from `Δ(Tate) = q·unit`).
* **`hT_of_kernels`** — `Siso p k P` satisfies the hypothesis `hT` of `HeckeQExp.classical_hU`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial ModP TateQuot

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

local notation "Aₜ" => eP K p (Ash K)
local notation "Bₜ" => eP K p (Bsh K)

/-- **`hKer`**: `p + 1` distinct order-`p` subgroups of the short Tate curve over `L` whose Vélu
quotients are (the images under `ι` of) `veluQuot ζ p`. This is what the Tate addition theorem
(the explicit kernel points form subgroups) provides. -/
def TateKernels (L : Type*) [Field L] [DecidableEq L] (ι : PowerSeries K →+* L) (ζ : K) : Prop :=
  ∃ G : Fin (p + 1) → Finset (short (ι Aₜ) (ι Bₜ)).Point, (∀ c, G c ∈ subs (ι Aₜ) (ι Bₜ) p) ∧
    Function.Injective G ∧
    ∀ c, HeckeQExp.ptR (veluC (G c)) = fun i => ι (HeckeQExp.ptR (veluQuot ζ p c) i)

lemma ptR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    HeckeQExp.ptR (W.map f) = fun i => f (HeckeQExp.ptR W i) := by
  funext i; fin_cases i <;> simp [HeckeQExp.ptR, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆]

/-- `TateKernels` from Vélu kernel data (the form in which the Tate addition theorem is stated). -/
theorem tateKernels_of_kernels {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (ζ : K) (κ : Fin (p + 1) → Kernel (ι Aₜ) (ι Bₜ))
    (hcard : ∀ c, (κ c).G.card = p) (hinj : Function.Injective fun c => (κ c).G)
    (hcurve : ∀ c, ((κ c).curve : WeierstrassCurve L) = (veluQuot ζ p c).map ι) :
    TateKernels p L ι ζ := by
  refine ⟨fun c => (κ c).G, fun c => ⟨⟨(κ c).zero_mem, (κ c).add_mem, (κ c).neg_mem⟩, hcard c⟩,
    hinj, fun c => ?_⟩
  rw [← Kernel.curve_eq_veluC two_ne_zero, hcurve, ptR_map]

/-- `Δ ≠ 0` for the short model of `tateBase`. -/
theorem tate_disc_ne : 4 * Aₜ ^ 3 + 27 * Bₜ ^ 2 ≠ 0 := by
  intro hz
  have h := ptR_shortW_base (K := K) (p := p)
  rw [ptR_shortW] at h
  have h4 := congrFun h 0
  have h6 := congrFun h 1
  simp only [HeckeQExp.ptR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at h4 h6
  have hc := (HeckeQExp.tateBase (K := K) p).c_relation
  have hΔ0 : (1728 : PowerSeries K) * (HeckeQExp.tateBase (K := K) p).Δ = 0 := by
    rw [hc, h4, show (HeckeQExp.tateBase (K := K) p).c₆ = -(864 * Bₜ) by rw [← h6, neg_neg]]
    linear_combination (-27648 : PowerSeries K) * hz
  have h1728 : (1728 : PowerSeries K) ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.constantCoeff (R := K)) h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have hΔ : (HeckeQExp.tateBase (K := K) p).Δ = 0 := (mul_eq_zero.1 hΔ0).resolve_left h1728
  obtain ⟨u, hu⟩ := TateCurve.Δ_Tate_eq_X_mul_unit
  rw [HeckeQExp.tateBase, HeckeQExp.TateAt, WeierstrassCurve.map_Δ, hu, map_mul] at hΔ
  rcases mul_eq_zero.1 hΔ with h | h
  · have := congrArg (PowerSeries.coeff (R := K) p) h
    simp at this
  · exact (u.isUnit.map _).ne_zero h

lemma map_aeval_eq {L : Type*} [Field L] (ι : PowerSeries K →+* L) (x : Fin 2 → PowerSeries K)
    (Q : MvPolynomial (Fin 2) K) :
    ι (aeval x Q) = eval (fun i => ι (x i)) (map (ι.comp (algebraMap K (PowerSeries K))) Q) := by
  rw [aeval_def, eval₂_comp_left, eval_map]
  rfl

/-- **`hT`, modulo `TateKernels`.** The isobaric polynomial `Siso p k P` of `hAlg` satisfies the Tate
hypothesis of `HeckeQExp.classical_hU`. -/
theorem hT_of_kernels {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {L : Type*} [Field L]
    [CharZero L] [IsAlgClosed L] [DecidableEq L] (ι : PowerSeries K →+* L)
    (hι : Function.Injective ι) (hKer : TateKernels p L ι ζ) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : Iso P k) :
    aeval (HeckeQExp.ptR (HeckeQExp.tateBase (K := K) p)) (Siso p k P) =
      ∑ c, aeval (HeckeQExp.ptR (HeckeQExp.tateQuot p ζ c)) P := by
  obtain ⟨G, hmem, hinj, hptR⟩ := hKer
  rw [hT_iff_velu hζ hp2]
  apply hι
  set f := ι.comp (algebraMap K (PowerSeries K))
  have hΔ : 4 * ι Aₜ ^ 3 + 27 * ι Bₜ ^ 2 ≠ 0 := by
    intro h; apply tate_disc_ne (K := K) p; apply hι
    simpa [map_ofNat] using h
  have hbase : (fun i => ι (HeckeQExp.ptR (shortW Aₜ Bₜ) i)) =
      HeckeQExp.ptR (short (ι Aₜ) (ι Bₜ) : WeierstrassCurve L) := by
    rw [ptR_shortW, ptR_short]
    funext i; fin_cases i <;> simp [map_ofNat]
  rw [map_aeval_eq, hbase, ← subSum_Siso p f hP _ _ hΔ, map_sum,
    ← sum_fin_eq_subSum _ G hmem hinj (surj_of_inj_algClosed p hΔ G hmem hinj)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_aeval_eq, ← hptR c]
  rfl

end HeckeBridge
