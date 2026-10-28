import RamanujanTau.UBSharp.Basic
import RamanujanTau.ConjAlg.NoKer

/-!
# The geometric layer in terms of the Vélu quotients (the objects of `ConjAlg.QuotValBound`)

For a test curve `W`, `Wₛ = short (sa W) (sb W)` is its `u = 1` short model and, for an order-`ℓ`
subgroup `C ∈ subs (sa W) (sb W) ℓ`, `veluC C` is Vélu's quotient (normalization `φ_C^*ω_C = ω`).

**`QuotEBound ℓ hℓ φ`**: for every test curve `W` of the break region there is `H ∈ subs` with
* `‖Δ(Wₛ/H)‖·‖E(W)‖^{12} ≤ ‖ℓ‖^{12}` and `‖Δ(Wₛ/C)‖^ℓ ≤ ‖E(W)‖^{12}` (`C ≠ H`) — this is
  **exactly `ConjAlg.QuotValBound`** (`QuotEBound.toQuotValBound`);
* `‖E(Wₛ/H)‖·‖E(W)‖^ℓ ≤ max(‖ℓ‖^{ℓ−1}‖E(W)‖^{ℓ+1}, ‖ℓ‖^ℓ)` — i.e. `v(E(Wₛ/H)) ≥ min(ℓ−1+v, ℓ(1−v))`:
  `(ℓ−1)·v(λ_H) + v(E(W/H))` with `v(λ_H) = 1 − v` and Buzzard 3.3 `v(W/H) ≥ min(ℓv, 1−v)`;
* `‖E(Wₛ/C)‖ ≤ ‖E(W)‖` (`C ≠ H`) — i.e. `(ℓ−1)v/ℓ + v(W/C) ≥ v`, the Vélu-normalized form of
  `‖E(W/C)‖^ℓ = ‖E(W)‖` (`UpContraction.QuotHyp`, Buzzard 3.3(v)); in fact equality holds;
* `‖c₄(Wₛ/C)‖³ ≤ ‖Δ(Wₛ/C)‖`, `‖c₆(Wₛ/C)‖² ≤ ‖Δ(Wₛ/C)‖` for all `C`: the model scaled by `λ_C`
  (`AllQuotients.model_of_finSub`) is integral.

**`quotBound_of_E`** (modulo `hKer`, now unconditional via `TateAdd.tateKernels`):
`QuotEBound → QuotBound`, the algebraicity being `HeckeBridge.classical_hU_short` on the enumerated
Vélu quotients. Over `ℂ_ℓ`: **`quotBound_of_E_C`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBSharp
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal DBound HeckeBridge SubgroupSum Velu
  ConjAlg

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

section Def
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [DecidableEq K]

variable (ℓ) in
/-- **`QuotValBound` plus the Hasse and integrality bounds of the Vélu quotients.** -/
def QuotEBound (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ W : WeierstrassCurve K, KatzForms.IsTest W → UpContraction.Brk ℓ (KatzForms.Eh φ hℓ) W →
    ∃ H ∈ subs (sa W) (sb W) ℓ,
      (‖(veluC H).Δ‖ * ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
        ∀ C ∈ subs (sa W) (sb W) ℓ, C ≠ H →
          ‖(veluC C).Δ‖ ^ ℓ ≤ ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12) ∧
      ‖eval (KatzForms.pt (veluC H)) (KatzForms.Eh φ hℓ)‖ *
          ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) * ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ C ∈ subs (sa W) (sb W) ℓ, C ≠ H →
        ‖eval (KatzForms.pt (veluC C)) (KatzForms.Eh φ hℓ)‖ ≤
          ‖eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖) ∧
      ∀ C ∈ subs (sa W) (sb W) ℓ,
        ‖(veluC C : WeierstrassCurve K).c₄‖ ^ 3 ≤ ‖(veluC C : WeierstrassCurve K).Δ‖ ∧
        ‖(veluC C : WeierstrassCurve K).c₆‖ ^ 2 ≤ ‖(veluC C : WeierstrassCurve K).Δ‖

/-- `QuotEBound` contains `QuotValBound`. -/
theorem QuotEBound.toQuotValBound [IsAlgClosed K] {φ : ℤ_[ℓ] →+* K} (h : QuotEBound ℓ hℓ φ) :
    QuotValBound ℓ hℓ φ := fun W hW hB => by
  obtain ⟨H, hH, hV, -⟩ := h W hW hB
  exact ⟨H, hH, hV⟩

end Def

section Alg
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [IsAlgClosed K]
  [DecidableEq K]

/-- `T_ℓ` over `ℤ_ℓ` agrees with `heckePoly` over `ℚ_ℓ`. -/
lemma map_PT {k : ℕ} (hk : 1 ≤ k) {P PT : Poly ℓ} (hP : Iso P k) (hPT : Iso PT k)
    (he : ev ℤ_[ℓ] PT = Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P)) :
    MvPolynomial.map (ιz ℓ) PT = heckePoly ℓ (MvPolynomial.map (ιz ℓ) P) := by
  refine heckePoly_unique (R := ℚ_[ℓ]) ℓ (ModP.iso_map (ιz ℓ) hP) (ModP.iso_map (ιz ℓ) hPT) ?_
  have hc : algebraMap ℚ ℚ_[ℓ] (mulQ ℓ k) = ιz ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) := by
    rw [mulQ_of_pos ℓ hk]; simp
  rw [← map_ev, he, map_Tq, map_ev, hc]

/-- **`QuotEBound → QuotBound`** (modulo `hKer`). -/
theorem quotBound_of_E (ψ : ℚ_[ℓ] →+* K) {ζK : K} (hζK : IsPrimitiveRoot ζK ℓ)
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (ι : PowerSeries K →+* L) (hι : Function.Injective ι) (hKer : TateKernels ℓ L ι ζK)
    (hE : QuotEBound ℓ hℓ (ψ.comp (ιz ℓ))) : QuotBound ℓ hℓ (ψ.comp (ιz ℓ)) := by
  intro W hW hBrk
  obtain ⟨H, hH, ⟨hΔH, hΔC⟩, hEH, hEC, hint⟩ := hE W hW hBrk
  have hW0 : W.Δ ≠ 0 := by
    intro h; have := hW.2.2.2.2.2; rw [h, norm_zero] at this; exact zero_ne_one this
  have hΔ := shortModel_disc_ne hW0
  obtain ⟨G, hmem, hinj, hsurj, h0⟩ := exists_enum_algClosed ℓ hΔ hH
  have hne : ∀ c : Fin ℓ, G c.succ ≠ H := fun c h => by
    rw [← h0] at h; exact Fin.succ_ne_zero c (hinj h)
  refine ⟨fun i => veluC (G (i.elim 0 Fin.succ)), ?_, fun i => hint _ (hmem _), ?_, fun c => ?_, ?_,
    fun c => ?_⟩
  · intro k P PT hk hP hPT he
    have hp2 : ℓ ≠ 2 := by omega
    have hQe : IsQuotEnum ℓ (short (sa W) (sb W) : WeierstrassCurve K) (fun c => veluC (G c)) :=
      ⟨sa W, sb W, hΔ, rfl, G, hmem, hinj, hsurj, fun _ => rfl⟩
    have hPK : Iso (MvPolynomial.map (ψ.comp (ιz ℓ)) P) k := ModP.iso_map (ψ.comp (ιz ℓ)) hP
    have hs := classical_hU_short ℓ hζK hp2 ι hι hKer hPK
      (fun _ c => veluC (G c)) (short (sa W) (sb W) : WeierstrassCurve K) hQe
    rw [shortModel_ptR] at hs
    have hH' : heckePoly ℓ (MvPolynomial.map (ψ.comp (ιz ℓ)) P) =
        MvPolynomial.map (ψ.comp (ιz ℓ)) PT := by
      rw [← MvPolynomial.map_map, ← map_heckePoly, ← map_PT hk hP hPT he, MvPolynomial.map_map]
    rw [hH'] at hs
    rw [Fintype.sum_option]
    have := hs.symm
    rw [Fin.sum_univ_succ] at this
    exact this
  · simpa [h0] using hΔH
  · exact hΔC _ (hmem _) (hne c)
  · simpa [h0] using hEH
  · exact hEC _ (hmem _) (hne c)

end Alg

/-- **`QuotEBound → QuotBound` over `ℂ_ℓ`**, unconditionally (`TateAdd.tateKernels`). -/
theorem quotBound_of_E_C [DecidableEq ℂ_[ℓ]] (hE : QuotEBound ℓ hℓ (SharpHQ.φC ℓ)) :
    QuotBound ℓ hℓ (SharpHQ.φC ℓ) := by
  have hℓ0 : ℓ ≠ 0 := hℓp.out.ne_zero
  haveI : NeZero (ℓ : ℂ_[ℓ]) := ⟨by
    have : (ℓ : ℂ_[ℓ]) = algebraMap ℚ_[ℓ] ℂ_[ℓ] (ℓ : ℚ_[ℓ]) := by simp
    rw [this]; exact (map_ne_zero _).mpr (by exact_mod_cast hℓ0)⟩
  obtain ⟨ζK, hζK⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[ℓ] ℓ
  classical
  set F := FractionRing (PowerSeries ℂ_[ℓ])
  set L := AlgebraicClosure F
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let ι : PowerSeries ℂ_[ℓ] →+* L := (algebraMap F L).comp (algebraMap (PowerSeries ℂ_[ℓ]) F)
  have hι : Function.Injective ι :=
    (algebraMap F L).injective.comp (IsFractionRing.injective (PowerSeries ℂ_[ℓ]) F)
  exact quotBound_of_E hℓ (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hζK ι hι (TateAdd.tateKernels hι hζK hℓ) hE

end UBSharp
