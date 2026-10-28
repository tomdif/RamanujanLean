/-
# Quotient models for all order-`p` subgroups (explicit Vélu model)

`exists_model_of_descent`: the proof of `VeluLubin.link_of_descent`, with the explicit model
`W'' = ⟨μ,0,0,0⟩ • (Vélu curve)` exposed (instead of `Nonempty (VeluLubinLink G)`).
-/
import RamanujanTau.VeluDescent.Main
import RamanujanTau.SubgroupSum.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries FGL EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "ι" => Subring.subtype (CanonicalIsogeny.integers K)

variable [CharZero K] [DecidableEq K]

/-- **The explicit integral model of the Vélu quotient from integral descent**: `W = μ-scaled Vélu
curve` is integral, has good reduction, and `ψ : F_{W} → G` has Lie derivative `1`. -/
theorem exists_model_of_descent [CompleteSpace K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (a b : 𝒪) (κ : Velu.Kernel (a : K) (b : K)) (G : FormalGroup 𝒪)
    [G.IsComm] (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1)
    (π : MvPowerSeries Unit 𝒪) (hπ : Hom (formalGroup (shortO a b)) G π)
    (hμ0 : ((coeff (Finsupp.single () 1) π : 𝒪) : K) ≠ 0)
    (θ : MvPowerSeries Unit 𝒪)
    (hθ : sb (MvPowerSeries.map ι π) (MvPowerSeries.map ι θ) =
      C ((coeff (Finsupp.single () 1) π : 𝒪) : K) * phi κ) :
    ∃ (A'' B'' : 𝒪) (ψ : MvPowerSeries Unit 𝒪),
      toK (shortO A'' B'') = ((⟨Units.mk0 ((coeff (Finsupp.single () 1) π : 𝒪) : K) hμ0, 0, 0, 0⟩ :
        WeierstrassCurve.VariableChange K) • (κ.curve : WeierstrassCurve K)) ∧
      ‖(((shortO A'' B'').Δ : 𝒪) : K)‖ = 1 ∧ Hom (formalGroup (shortO A'' B'')) G ψ ∧
      coeff (Finsupp.single () 1) ψ = 1 := by
  set μ : K := ((coeff (Finsupp.single () 1) π : 𝒪) : K) with hμ
  set μu : Kˣ := Units.mk0 μ hμ0
  have hμn : 0 < ‖μ‖ := norm_pos_iff.2 hμ0
  set E'' : WeierstrassCurve K := (⟨μu, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • κ.curve
  -- `σ = μ φ : F_W → F_{E''}` over `K`
  have hσ : Hom (formalGroup (Velu.short (a : K) (b : K))) (formalGroup E'') (C μ * phi κ) := by
    have hsc : Hom (formalGroup κ.curve) (formalGroup E'') (C μ * X ()) := hom_scale κ.curve μu
    have h := hom_comp (velu_formal_hom κ) hsc
    have e : sb (phi κ) (C μ * X () : MvPowerSeries Unit K) = C μ * phi κ := by
      rw [sb, subst_mul (FGL.hs (hc (cc_phi κ))), subst_C, FGL.sX _ (hc (cc_phi κ))]
    rwa [← sb, e] at h
  -- `π` over `K`
  have hπK : Hom (formalGroup (Velu.short (a : K) (b : K))) (G.map ι) (MvPowerSeries.map ι π) := by
    have h := hom_map ι hπ
    rwa [formalGroup_map, ← toK, toK_shortO] at h
  set πK := MvPowerSeries.map ι π with hπKd
  have hπK0 : PowerSeries.constantCoeff (πK : PowerSeries K) = 0 := hπK.1
  have hπK1 : IsUnit (PowerSeries.coeff 1 (πK : PowerSeries K)) := by
    refine IsUnit.mk0 _ ?_
    show coeff (Finsupp.single () 1) πK ≠ 0
    rw [hπKd, coeff_map]; exact hμ0
  set ρ : MvPowerSeries Unit K := PowerSeries.substInvOfIsUnit (πK : PowerSeries K) hπK1
  have hρ0 : constantCoeff ρ = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hρπ : sb πK ρ = X () := by
    have := PowerSeries.subst_substInvOfIsUnit_left (πK : PowerSeries K) hπK0 hπK1
    rw [PowerSeries.subst_def] at this; exact this
  have hπρ : sb ρ πK = X () := by
    have := PowerSeries.subst_substInvOfIsUnit_right (πK : PowerSeries K) hπK0 hπK1
    rw [PowerSeries.subst_def] at this; exact this
  -- `θ : G → F_{E''}` over `K`
  have hθK : Hom (G.map ι) (formalGroup E'') (MvPowerSeries.map ι θ) :=
    hom_of_comp hπK hσ hθ hρ0 hρπ hπρ
  have hθ0 : constantCoeff θ = 0 := by
    have h := congrArg constantCoeff hθ
    rw [sb, cc_subst _ (hc hπK.1), constantCoeff_map, map_mul, cc_phi, mul_zero] at h
    exact Subtype.val_injective (by simpa using h)
  have hθ1 : coeff (Finsupp.single () 1) θ = 1 := by
    have h := congrArg (coeff (Finsupp.single () 1)) hθ
    rw [lin_sb (cc_map ι hθ0) hπK.1, coeff_C_mul, lie_phi, mul_one, coeff_map, coeff_map] at h
    apply Subtype.val_injective
    have := mul_right_cancel₀ hμ0 (h.trans (one_mul μ).symm)
    simpa using this
  -- the inverse `ψ = θ⁻¹` over `𝒪`
  have hθu : IsUnit (PowerSeries.coeff 1 (θ : PowerSeries 𝒪)) := by
    show IsUnit (coeff (Finsupp.single () 1) θ); rw [hθ1]; exact isUnit_one
  set ψ : MvPowerSeries Unit 𝒪 := PowerSeries.substInvOfIsUnit (θ : PowerSeries 𝒪) hθu
  have hψ0 : constantCoeff ψ = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hψθ : sb θ ψ = X () := by
    have := PowerSeries.subst_substInvOfIsUnit_left (θ : PowerSeries 𝒪) hθ0 hθu
    rw [PowerSeries.subst_def] at this; exact this
  have hθψ : sb ψ θ = X () := by
    have := PowerSeries.subst_substInvOfIsUnit_right (θ : PowerSeries 𝒪) hθ0 hθu
    rw [PowerSeries.subst_def] at this; exact this
  -- `F_{E''}` is integral: `F_{E''} = θ(G(ψ X, ψ Y))`
  set F₀ : MvPowerSeries (Fin 2) 𝒪 :=
    sb (FGL.ev G (sb (X 0 : MvPowerSeries (Fin 2) 𝒪) ψ) (sb (X 1 : MvPowerSeries (Fin 2) 𝒪) ψ)) θ
  have hF₀ : (formalGroup E'').toPowerSeries = MvPowerSeries.map ι F₀ := by
    have hθψK : sb (MvPowerSeries.map ι ψ) (MvPowerSeries.map ι θ) = X () := by
      rw [← map_sb ι hψ0, hθψ, map_X]
    rw [law_eq_conj hθK (cc_map ι hψ0) hθψK]
    have hg0 : constantCoeff (sb (X 0 : MvPowerSeries (Fin 2) 𝒪) ψ) = 0 := cc0 _ (hc VeluLubin.cX0) hψ0
    have hg1 : constantCoeff (sb (X 1 : MvPowerSeries (Fin 2) 𝒪) ψ) = 0 := cc0 _ (hc VeluLubin.cX1) hψ0
    rw [map_sb ι (cc_ev G hg0 hg1), map_ev' ι G hg0 hg1, map_sb ι VeluLubin.cX0, map_sb ι VeluLubin.cX1]
    simp
  -- integrality of `a₄'' = μ⁻⁴ A'`, `a₆'' = μ⁻⁶ B'`
  have hE : E'' = shortO (μ⁻¹ ^ 4 * κ.A') (μ⁻¹ ^ 6 * κ.B') := by
    ext
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₁, Velu.Kernel.curve]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₂, Velu.Kernel.curve]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₃, Velu.Kernel.curve]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₄, Velu.Kernel.curve, μu]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₆, Velu.Kernel.curve, μu]
  have h2n : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3n : ‖(3 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hA'' : ‖μ⁻¹ ^ 4 * κ.A'‖ ≤ 1 := by
    have h := Ψ_map F₀ (formalGroup E'') hF₀ 4
    rw [hE, coeff4_Ψ, norm_mul, norm_neg, h2n, one_mul] at h
    exact h
  have hB'' : ‖μ⁻¹ ^ 6 * κ.B'‖ ≤ 1 := by
    have h := Ψ_map F₀ (formalGroup E'') hF₀ 6
    rw [hE, coeff6_Ψ, norm_mul, norm_neg, h3n, one_mul] at h
    exact h
  set W'' : WeierstrassCurve 𝒪 := shortO ⟨μ⁻¹ ^ 4 * κ.A', hA''⟩ ⟨μ⁻¹ ^ 6 * κ.B', hB''⟩
  have hWK : toK W'' = E'' := by
    rw [hE]; ext <;> simp [W'', toK, shortO]
  -- `θ : G → F_{W''}` over `𝒪`, an isomorphism
  have hθG : Hom G (formalGroup W'') θ := by
    refine hom_of_map ι Subtype.val_injective hθ0 ?_
    rw [formalGroup_map, ← toK, hWK]; exact hθK
  have hψ : Hom (formalGroup W'') G ψ := hom_inv hθG hψ0 hψθ hθψ
  have hψ1 : coeff (Finsupp.single () 1) ψ = 1 := by
    have h := PowerSeries.coeff_one_substInvOfIsUnit (θ : PowerSeries 𝒪) hθu
    have hu : hθu.unit = 1 := Units.ext (by simp [IsUnit.unit_spec]; exact hθ1)
    rw [hu, inv_one] at h
    exact h
  -- good reduction
  have hΔ'' : ‖((W''.Δ : 𝒪) : K)‖ = 1 :=
    norm_Δ_eq_one_of_iso p hp5 hp1 _ _ G hu ha θ hθG (by rw [hθ1]; simp)
  exact ⟨_, _, ψ, hWK, hΔ'', hψ, hψ1⟩

end AllQuotients
