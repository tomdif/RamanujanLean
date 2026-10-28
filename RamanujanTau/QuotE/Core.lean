/-
# Integral models of all `p + 1` Vélu quotients, with their Lie and Hasse norms

`W : y² = x³ + ax + b` over `𝒪` with good supersingular reduction, in the break region. Write
`α = ‖a_W‖`, `ε = ‖p‖`. **`velu_models`**: there is `H ∈ subs a b p` (the canonical subgroup) such
that for every `G ∈ subs a b p` there are `μ : Kˣ` and an integral good-reduction `W'` with
`toK W' = ⟨μ,0,0,0⟩ • veluC G`, and
* `G = H`: `‖μ‖·α = ε` and `‖E_{p−1}(W')‖·α ≤ max(α^{p+1}, ε)` (Buzzard 3.3 (ii)/(iv), transport
  and Deligne);
* `G ≠ H`: `‖μ‖^p = α` and `‖E_{p−1}(W')‖^p = α` (Buzzard 3.3 (v), `UpContraction.quot_E_pow`).
-/
import RamanujanTau.AllQuotients.SS
import RamanujanTau.QuotE.Canonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotE
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin AllQuotients

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]

/-- the model of the quotient by a `FinSub` lying over `G`, with `‖μ‖ = ‖Lie π_C‖`. -/
lemma model_data (a b : ↥(CanonicalIsogeny.integers K)) (p : ℕ) [hpf : Fact p.Prime]
    (hp5 : 5 ≤ p) (hp1 : ‖(p : K)‖ < 1) (hΔ : ‖(((shortO a b).Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (C : Lubin.FinSub (formalGroup (shortO a b))) (hcard : C.H.card = p)
    (hCp : ∀ h ∈ C.H, nm a b h p = 0)
    (G : Finset (Velu.short (a : K) (b : K)).Point) (hG : C.H.image (Pt a b) = G) :
    ∃ (μ : Kˣ) (W' : WeierstrassCurve ↥(CanonicalIsogeny.integers K))
      (ψ : MvPowerSeries Unit ↥(CanonicalIsogeny.integers K)),
      UpContraction.toK W' = (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) •
        SubgroupSum.veluC G ∧
      ‖((W'.Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1 ∧
      UpContraction.HomR (formalGroup W') (Lubin.quot C) ψ ∧
      coeff (Finsupp.single () 1) ψ = 1 ∧
      ‖(μ : K)‖ = ∏ c ∈ C.H.erase 0, ‖(c : K)‖ := by
  obtain ⟨κ, hκ⟩ := exists_kernel_of_finSub a b hpf.out hp5 C hCp
  have hκG : κ.G = G := by
    rw [← hG]; apply Finset.coe_injective; rw [hκ, Finset.coe_image]
  obtain ⟨A'', B'', ψ, hK, hΔ'', hψ, hψ1⟩ := model_of_finSub a b p hp5 hp1 hΔ ha C hcard κ hκ
  refine ⟨Units.mk0 _ (lie_pis_ne_zero C), shortO A'' B'', ψ, ?_, hΔ'', ⟨hψ.1, hψ.2⟩, hψ1, ?_⟩
  · show toK (shortO A'' B'') = _
    rw [hK, SubgroupSum.Kernel.curve_eq_veluC two_ne_zero κ, hκG]
  · rw [Units.val_mk0, norm_lie_pis]

section Models
variable (p : ℕ) [hpf : Fact p.Prime] [Algebra ℤ_[p] ↥(CanonicalIsogeny.integers K)]

/-- Deligne + transport: a good-reduction `W'` whose formal group maps to `G'` with Lie `1` has
`‖E_{p−1}(W')‖ ≤ max(‖a_{G'}‖, ‖p‖)`. -/
lemma norm_EpO_le (hp5 : 5 ≤ p) (W' : WeierstrassCurve ↥(CanonicalIsogeny.integers K))
    (G' : FormalGroup ↥(CanonicalIsogeny.integers K)) [G'.IsComm]
    (ψ : MvPowerSeries Unit ↥(CanonicalIsogeny.integers K))
    (hψ : UpContraction.HomR (formalGroup W') G' ψ) (hψ1 : coeff (Finsupp.single () 1) ψ = 1) :
    ‖((UpContraction.EpO p hp5 W' : ↥(CanonicalIsogeny.integers K)) : K)‖ ≤
      max ‖((hasse G' p : ↥(CanonicalIsogeny.integers K)) : K)‖ ‖(p : K)‖ := by
  have htr := UpContraction.norm_le_of_mem_span_p p
    (UpContraction.hasse_transport (formalGroup W') G' p ψ hψ)
  rw [hψ1, one_mul, one_pow, one_mul] at htr
  have hD := UpContraction.norm_le_of_mem_span_p p (HasseInv.coeff_nmul_sub_hasseA_mem' p hp5 W')
  simp only [AddSubgroupClass.coe_sub] at htr hD
  set aW : K := ((coeff (Finsupp.single () p) (FGL.nmul (formalGroup W') p) :
    ↥(CanonicalIsogeny.integers K)) : K)
  set aG : K := ((hasse G' p : ↥(CanonicalIsogeny.integers K)) : K)
  set E : K := ((UpContraction.EpO p hp5 W' : ↥(CanonicalIsogeny.integers K)) : K)
  have hD' : ‖aW - E‖ ≤ ‖(p : K)‖ := hD
  have htr' : ‖aW - aG‖ ≤ ‖(p : K)‖ := htr
  have e : E = aG + (aW - aG) - (aW - E) := by ring
  rw [e]
  refine (QuotientHasse.norm_sub_le_max' _ _).trans (max_le ?_ (hD'.trans (le_max_right _ _)))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (le_max_left _ _) (htr'.trans (le_max_right _ _)))

/-- **Integral models of all Vélu quotients, with Lie and Hasse norms.** -/
theorem velu_models (a b : ↥(CanonicalIsogeny.integers K)) (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖)
    (hΔ : ‖(((shortO a b).Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1))
    (hEO : ‖((UpContraction.EpO p hp5 (shortO a b) : ↥(CanonicalIsogeny.integers K)) : K)‖ =
      ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖) :
    ∃ H ∈ SubgroupSum.subs (a : K) (b : K) p, ∀ G ∈ SubgroupSum.subs (a : K) (b : K) p,
      ∃ (μ : Kˣ) (W' : WeierstrassCurve ↥(CanonicalIsogeny.integers K)),
        UpContraction.toK W' = (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) •
          SubgroupSum.veluC G ∧
        ‖((W'.Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1 ∧
        (G = H → ‖(μ : K)‖ *
            ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖ =
              ‖(p : K)‖ ∧
          ‖((UpContraction.EpO p hp5 W' : ↥(CanonicalIsogeny.integers K)) : K)‖ *
              ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖ ≤
            max (‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖ ^
              (p + 1)) ‖(p : K)‖) ∧
        (G ≠ H → ‖(μ : K)‖ ^ p =
            ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖ ∧
          ‖((UpContraction.EpO p hp5 W' : ↥(CanonicalIsogeny.integers K)) : K)‖ ^ p =
            ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖) := by
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
  have hC₀can := canSub_can a b hT' hu ha hε hp1 hbreak
  have hH := image_mem_subs a b hp hp5 hT' C₀ hC₀T hC₀c
  -- break data in terms of `E_{p−1}`
  have hE1 : ‖((UpContraction.EpO p hp5 (shortO a b) : ↥(CanonicalIsogeny.integers K)) : K)‖ < 1 := by
    rw [hEO]; exact ha
  have hEb : ‖(p : K)‖ ^ p <
      ‖((UpContraction.EpO p hp5 (shortO a b) : ↥(CanonicalIsogeny.integers K)) : K)‖ ^ (p + 1) := by
    rw [hEO]; exact hbreak
  refine ⟨C₀.H.image (Pt a b), hH, fun G hG => ?_⟩
  by_cases hGH : G = C₀.H.image (Pt a b)
  · -- the canonical quotient
    have hCp : ∀ h ∈ C₀.H, nm a b h p = 0 := fun h hh => ((hT' h).1 (hC₀T hh)).2
    obtain ⟨μ, W', ψ, hK, hΔW, hψ, hψ1, hμ⟩ :=
      model_data a b p hp5 hp1 hΔ ha C₀ hC₀c hCp G hGH.symm
    refine ⟨μ, W', hK, hΔW, fun _ => ⟨?_, ?_⟩, fun h => absurd hGH h⟩
    · rw [hμ]
      exact prod_canonical (formalGroup (shortO a b)) p C₀ hC₀c hC₀can
    · set α := ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖
      have hle := norm_EpO_le p hp5 W' _ ψ hψ hψ1
      have hq := hasse_quot_canonical_le (formalGroup (shortO a b)) p hu ha hε hbreak C₀ hC₀c
        hC₀can
      have hα1 : α ≤ 1 := ha.le
      calc ‖((UpContraction.EpO p hp5 W' : ↥(CanonicalIsogeny.integers K)) : K)‖ * α
          ≤ max ‖((hasse (Lubin.quot C₀) p : ↥(CanonicalIsogeny.integers K)) : K)‖ ‖(p : K)‖ * α :=
            mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ = max (‖((hasse (Lubin.quot C₀) p : ↥(CanonicalIsogeny.integers K)) : K)‖ * α)
              (‖(p : K)‖ * α) := max_mul_of_nonneg _ _ (norm_nonneg _)
        _ ≤ max (α ^ (p + 1)) ‖(p : K)‖ := by
            refine max_le hq ?_
            exact (mul_le_of_le_one_right (norm_nonneg _) hα1).trans (le_max_right _ _)
  · -- a non-canonical quotient
    set C := ofSub a b hp hp5 hT' hG.1
    have hcard : C.H.card = p := card_ofSub a b hp hp5 hT' hTc hΔ' hG
    have himg : C.H.image (Pt a b) = G := image_ofSub a b hp hp5 hT' hTc hΔ' hG
    have hCT : C.H ⊆ T := ofSub_sub a b hp hp5 hT' hG.1
    have hCp : ∀ h ∈ C.H, nm a b h p = 0 := fun h hh => ((hT' h).1 (hCT hh)).2
    have hCH : ∀ c ∈ C.H, c ≠ 0 →
        ‖((hasse (formalGroup (shortO a b)) p : ↥(CanonicalIsogeny.integers K)) : K)‖ *
          ‖(c : K)‖ ^ (p - 1) ≠ ‖(p : K)‖ := by
      intro c hc hc0 hcan
      apply hGH
      refine himg.symm.trans ?_
      rw [eq_canSub a b hp5 hT' hTc hu ha hε hp1 hbreak C hCT hcard hc hc0 hcan]
    obtain ⟨μ, W', ψ, hK, hΔW, hψ, hψ1, hμ⟩ := model_data a b p hp5 hp1 hΔ ha C hcard hCp G himg
    refine ⟨μ, W', hK, hΔW, fun h => absurd h hGH, fun _ => ⟨?_, ?_⟩⟩
    · rw [hμ]
      exact prod_noncanonical (formalGroup (shortO a b)) p hu ha hε hbreak C hCp hcard hCH
    · rw [← hEO]
      exact UpContraction.quot_E_pow p hp5 (shortO a b) hε hΔ hE1 hEb C hCp hcard hCH W' ψ hψ
        (by rw [hψ1]; simp)

end Models

end QuotE
