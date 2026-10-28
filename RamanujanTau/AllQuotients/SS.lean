/-
# `UpContraction.SSData` for short curves

**`ssData_short`**: for a short `W = shortO a b` with good supersingular reduction in the break region,
the `p` non-canonical order-`p` subgroups `G c` (an injective, exhaustive enumeration of
`subs a b p ∖ {H}`, `H` canonical) have good-reduction quotient models `Qs c` (each the `μ`-scaled
`veluC (G c)`), and `SSData p W Qs` holds.
-/
import RamanujanTau.AllQuotients.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

/-- **`SSData` for short curves**, with the enumeration of the non-canonical subgroups. -/
theorem ssData_short (a b : ↥(CanonicalIsogeny.integers K)) (p : ℕ) [hpf : Fact p.Prime]
    (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖) (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    ∃ (H : Finset (Velu.short (a : K) (b : K)).Point)
      (G : Fin p → Finset (Velu.short (a : K) (b : K)).Point) (Qs : Fin p → WeierstrassCurve K),
      H ∈ SubgroupSum.subs (a : K) (b : K) p ∧
      (∀ c, G c ∈ SubgroupSum.subs (a : K) (b : K) p ∧ G c ≠ H) ∧ Function.Injective G ∧
      (∀ G' ∈ SubgroupSum.subs (a : K) (b : K) p, G' ≠ H → ∃ c, G c = G') ∧
      (∀ c, ∃ u : Kˣ, Qs c =
        (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • SubgroupSum.veluC (G c)) ∧
      UpContraction.SSData p (UpContraction.toK (shortO a b)) Qs := by
  classical
  have hp := hpf.out
  have hp1 : ‖(p : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one hp.two_le (norm_nonneg _) ha.le hbreak
  have hu := HeightEll.topc_norm_eq_one (shortO a b) p hp5 hp1 hΔ ha
  have hΔ' := disc_ne_zero a b hΔ
  obtain ⟨T, hT, hTc⟩ := exists_torsion (formalGroup (shortO a b)) p hu ha hε hp1
  have hT' : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0 := hT
  set C₀ := canSub a b hT' hu ha hε hp1 hbreak
  have hC₀T : C₀.H ⊆ T := canSub_sub a b hT' hu ha hε hp1 hbreak
  have hC₀c : C₀.H.card = p := card_canSub a b hp5 hT' hTc hu ha hε hp1 hbreak
  have hH := image_mem_subs a b hp hp5 hT' C₀ hC₀T hC₀c
  obtain ⟨G, hmem, hinj, hsurj, h0⟩ := HeckeBridge.exists_enum_algClosed p hΔ' hH
  have hne : ∀ c : Fin p, G c.succ ≠ C₀.H.image (Pt a b) := fun c h =>
    Fin.succ_ne_zero c (hinj (h.trans h0.symm))
  have hmodel : ∀ c : Fin p, ∃ Q : WeierstrassCurve K,
      (∃ u : Kˣ, Q = (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) •
        SubgroupSum.veluC (G c.succ)) ∧
      ∃ C : Lubin.FinSub (EllipticFormal.formalGroup (shortO a b)),
      (∀ x ∈ C.H, Lubin.pt (fun _ : Unit => x)
        (FGL.nmul (EllipticFormal.formalGroup (shortO a b)) p) = 0) ∧
      C.H.card = p ∧
      (∀ x ∈ C.H, x ≠ 0 →
        ‖((QuotientHasse.hasse (EllipticFormal.formalGroup (shortO a b)) p : 𝒪) : K)‖ *
          ‖(x : K)‖ ^ (p - 1) ≠ ‖(p : K)‖) ∧
      ∃ (W' : WeierstrassCurve 𝒪) (ψ : MvPowerSeries Unit 𝒪),
        ‖((W'.Δ : 𝒪) : K)‖ = 1 ∧
        UpContraction.HomR (EllipticFormal.formalGroup W') (Lubin.quot C) ψ ∧
        ‖((coeff (Finsupp.single () 1) ψ : 𝒪) : K)‖ = 1 ∧ UpContraction.toK W' = Q := by
    intro c
    have hG := hmem c.succ
    set C := ofSub a b hp hp5 hT' hG.1
    have hcard : C.H.card = p := card_ofSub a b hp hp5 hT' hTc hΔ' hG
    have himg : C.H.image (Pt a b) = G c.succ := image_ofSub a b hp hp5 hT' hTc hΔ' hG
    have hCT : C.H ⊆ T := ofSub_sub a b hp hp5 hT' hG.1
    have hCp : ∀ h ∈ C.H, nm a b h p = 0 := fun h hh => ((hT' h).1 (hCT hh)).2
    have hCH : ∀ x ∈ C.H, x ≠ 0 →
        ‖((QuotientHasse.hasse (EllipticFormal.formalGroup (shortO a b)) p : 𝒪) : K)‖ *
          ‖(x : K)‖ ^ (p - 1) ≠ ‖(p : K)‖ := by
      intro x hx hx0 hcan
      apply hne c
      refine himg.symm.trans ?_
      rw [eq_canSub a b hp5 hT' hTc hu ha hε hp1 hbreak C hCT hcard hx hx0 hcan]
    obtain ⟨κ, hκ⟩ := exists_kernel_of_finSub a b hp hp5 C hCp
    have hκG : κ.G = G c.succ := by
      rw [← himg]; apply Finset.coe_injective; rw [hκ, Finset.coe_image]
    obtain ⟨A'', B'', ψ, hK, hΔ'', hψ, hψ1⟩ := model_of_finSub a b p hp5 hp1 hΔ ha C hcard κ hκ
    refine ⟨toK (shortO A'' B''), ⟨Units.mk0 _ (lie_pis_ne_zero C), ?_⟩, C, hCp, hcard, hCH,
      shortO A'' B'', ψ, hΔ'', ⟨hψ.1, hψ.2⟩, by rw [hψ1]; simp, rfl⟩
    rw [hK, SubgroupSum.Kernel.curve_eq_veluC two_ne_zero κ, hκG]
  choose Qs hQs1 hQs2 using hmodel
  refine ⟨C₀.H.image (Pt a b), fun c => G c.succ, Qs, hH, fun c => ⟨hmem _, hne c⟩,
    fun c d h => Fin.succ_injective _ (hinj h), ?_, hQs1, ⟨shortO a b, rfl, hQs2⟩⟩
  intro G' hG' hne'
  obtain ⟨c, hc⟩ := hsurj G' hG'
  cases c using Fin.cases with
  | zero => exact absurd (hc.symm.trans h0) hne'
  | succ c => exact ⟨c, hc⟩

end AllQuotients
