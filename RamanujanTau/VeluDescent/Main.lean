/-
# Integral descent for the Vélu map, and Step 2 of I2 with the Vélu–Lubin link (short curves)

**`exists_integral_descent`**: for a short curve `W = shortO a b` over `𝒪` (`K` complete, algebraically
closed, ultrametric, characteristic `0`, `‖2‖ = ‖3‖ = 1`, `4a³ + 27b² ≠ 0`), a finite subgroup
`S ⊆ 𝔪` of `F_W` whose points are the Vélu kernel `κ` (`κ.G = Pt(S)`), and a homomorphism
`π = pis S : F_W → G` over `𝒪` (e.g. Lubin's quotient), there is `θ ∈ 𝒪⟦T⟧` with
  `θ ∘ π = μ · φ_κ`,   `μ = π'(0)`.
Proof: `μ φ` is a homomorphism `F_W → F_{E''}` (`E''` the Vélu curve scaled by `μ`), and
`w_{E''}(μ φ) = μ³ w'(φ) = π³ ε(π)` (`exists_eps`); so `θ' = μ φ ∘ π⁻¹` satisfies
`w_{E''}(θ') = T³ ε` and `integral_of_w` applies.

**`exists_step2_with_link`**: Step 2 of I2 together with `VeluLubinLink`, for short curves, with no
extra hypotheses (`VeluLubin.exists_step2_with_velu` + `exists_integral_descent`).
-/
import RamanujanTau.VeluDescent.Epsilon
import RamanujanTau.VeluDescent.Integral

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin EllipticI2 CanonicalIsogeny QuotientHasse

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "ι" => Subring.subtype (CanonicalIsogeny.integers K)

section Descent
variable [CompleteSpace K] [CharZero K] [DecidableEq K]

/-- `G(E'')(μφ, μ³ w'(φ)) = 0`, i.e. `w_{E''}(μ φ) = μ³ w'(φ)`. -/
lemma w_scale {A B : K} (κ : Velu.Kernel A B) {μ : K} (hμ : μ ≠ 0) :
    sb (C μ * phi κ) (w (shortO (μ⁻¹ ^ 4 * κ.A') (μ⁻¹ ^ 6 * κ.B')) : MvPowerSeries Unit K) =
      C (μ ^ 3) * wphi κ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  set W'' := shortO (μ⁻¹ ^ 4 * κ.A') (μ⁻¹ ^ 6 * κ.B')
  have hσ0 : constantCoeff (C μ * phi κ) = 0 := by rw [map_mul, cc_phi, mul_zero]
  have e1 := G_wt (W := W'') hσ0
  rw [wt, PowerSeries.subst_def] at e1
  have hG := G_phi κ h2
  have hA4 : C (μ⁻¹ ^ 4 * κ.A') * C μ ^ 4 = (C κ.A' : MvPowerSeries Unit K) := by
    rw [← map_pow, ← map_mul]; congr 1; field_simp
  have hB6 : C (μ⁻¹ ^ 6 * κ.B') * C μ ^ 6 = (C κ.B' : MvPowerSeries Unit K) := by
    rw [← map_pow, ← map_mul]; congr 1; field_simp
  have e2 : G (WM W'' Unit) (C μ * phi κ) (C (μ ^ 3) * wphi κ) = 0 := by
    simp only [G, WM, W'', shortO, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_zero,
      zero_mul, add_zero, map_pow] at hG ⊢
    simp only [Velu.Kernel.curve, Velu.short_a₁, Velu.short_a₂, Velu.short_a₃, Velu.short_a₄,
      Velu.short_a₆, map_zero, zero_mul, add_zero] at hG
    linear_combination (C μ ^ 3) * hG + (C μ ^ 3 * phi κ * wphi κ ^ 2) * hA4 +
      (C μ ^ 3 * wphi κ ^ 3) * hB6
  exact G_unique (WM W'' Unit) hσ0 (FGL.cc0 _ (hc hσ0) (cc_w _)) (by rw [map_mul, cc_wphi, mul_zero])
    e1 e2

variable [IsAlgClosed K]

/-- **integral descent for the Vélu map** (`θ ∘ π = μ φ_κ`, `θ ∈ 𝒪⟦T⟧`). -/
theorem exists_integral_descent (a b : 𝒪) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (κ : Velu.Kernel (a : K) (b : K))
    (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (S.H : Set 𝒪))
    (G : FormalGroup 𝒪) (hπ : Hom (formalGroup (shortO a b)) G (Lubin.pis S))
    (hΔ : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0) (h2 : ‖(2 : K)‖ = 1) (h3 : ‖(3 : K)‖ = 1) :
    ∃ θ : MvPowerSeries Unit 𝒪,
      sb (MvPowerSeries.map ι (Lubin.pis S)) (MvPowerSeries.map ι θ) =
        C ((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) * phi κ := by
  set μ : K := ((coeff (Finsupp.single () 1) (Lubin.pis S) : 𝒪) : K) with hμ
  have hμ0 : μ ≠ 0 := by
    rw [hμ, coeff_pis, SubmonoidClass.coe_finsetProd]
    exact Finset.prod_ne_zero_iff.2 fun h hh => fun e => Finset.ne_of_mem_erase hh (Subtype.ext e)
  set μu : Kˣ := Units.mk0 μ hμ0
  set A'' := μ⁻¹ ^ 4 * κ.A'
  set B'' := μ⁻¹ ^ 6 * κ.B'
  set E'' : WeierstrassCurve K := (⟨μu, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • κ.curve
  have hE : E'' = shortO A'' B'' := by
    ext
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₁, Velu.Kernel.curve]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₂, Velu.Kernel.curve]
    · simp [E'', shortO, WeierstrassCurve.variableChange_a₃, Velu.Kernel.curve]
    · simp [E'', A'', shortO, WeierstrassCurve.variableChange_a₄, Velu.Kernel.curve, μu]
    · simp [E'', B'', shortO, WeierstrassCurve.variableChange_a₆, Velu.Kernel.curve, μu]
  -- `σ = μ φ : F_W → F_{E''}`
  set σ := C μ * phi κ with hσd
  have hσ : Hom (formalGroup (Velu.short (a : K) (b : K))) (formalGroup (shortO A'' B'')) σ := by
    have hsc : Hom (formalGroup κ.curve) (formalGroup E'') (C μ * X ()) := hom_scale κ.curve μu
    have h := hom_comp (velu_formal_hom κ) hsc
    have e : sb (phi κ) (C μ * X () : MvPowerSeries Unit K) = C μ * phi κ := by
      rw [sb, subst_mul (FGL.hs (hc (cc_phi κ))), subst_C, FGL.sX _ (hc (cc_phi κ))]
    rw [← sb, e, hE] at h
    exact h
  have hσ0 : constantCoeff σ = 0 := hσ.1
  -- `w_{E''}(σ) = π³ ε(π)`
  obtain ⟨ε, hε⟩ := exists_eps S κ hκ hΔ
  have hwσ : sb σ (w (shortO A'' B'') : MvPowerSeries Unit K) =
      MvPowerSeries.map ι (Lubin.pis S) ^ 3 *
        sb (MvPowerSeries.map ι (Lubin.pis S)) (MvPowerSeries.map ι ε) := by
    rw [w_scale κ hμ0, ← hε]
  -- `π` over `K` and its inverse
  have hπK : Hom (formalGroup (Velu.short (a : K) (b : K))) (G.map ι)
      (MvPowerSeries.map ι (Lubin.pis S)) := by
    have h := hom_map ι hπ
    rwa [formalGroup_map, ← toK, toK_shortO] at h
  set πK := MvPowerSeries.map ι (Lubin.pis S) with hπKd
  have hπK0 : constantCoeff πK = 0 := hπK.1
  obtain ⟨ρ, hρ0, hρπ, hπρ⟩ := exists_inv πK hπK0 (by
    rw [hπKd, coeff_map]; exact Ne.isUnit hμ0)
  -- `θ' = σ ∘ π⁻¹`
  set θ' := sb ρ σ with hθ'd
  have hθπ : sb πK θ' = σ := by rw [hθ'd, sb_sb hπK0 hρ0, hρπ, X_sb]
  have hθK : Hom (G.map ι) (formalGroup (shortO A'' B'')) θ' :=
    hom_of_comp hπK hσ hθπ hρ0 hρπ hπρ
  have hθ0 : constantCoeff θ' = 0 := hθK.1
  have hlie : coeff (Finsupp.single () 1) θ' = 1 := by
    have h := congrArg (coeff (Finsupp.single () 1)) hθπ
    rw [lin_sb hθ0 hπK0, hσd, coeff_C_mul, lie_phi, mul_one, hπKd, coeff_map] at h
    exact mul_right_cancel₀ hμ0 (h.trans (one_mul μ).symm)
  have hw' : sb θ' (w (shortO A'' B'') : MvPowerSeries Unit K) =
      X () ^ 3 * MvPowerSeries.map ι ε := by
    refine sb_inj hπK0 hρ0 hπρ ?_
    rw [sb_sb hπK0 hθ0, hθπ, hwσ, sb_mul'' hπK0, sb_pow'' hπK0, sb_X hπK0]
  obtain ⟨θ, hθ⟩ := integral_of_w G A'' B'' θ' hθK hlie ε hw' h2 h3
  exact ⟨θ, by rw [hθ, hθπ]⟩

end Descent

/-! ### Step 2 of I2 with the Vélu–Lubin link -/

/-- **Step 2 of I2 with the Vélu–Lubin link, for short curves** (no extra hypotheses). -/
theorem exists_step2_with_link [CompleteSpace K] [IsAlgClosed K] (a b : 𝒪) (p : ℕ)
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖)
    (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    ∃ (G : FormalGroup 𝒪) (π πd : MvPowerSeries Unit 𝒪), IsHom (formalGroup (shortO a b)) G π ∧
      IsHom G (formalGroup (shortO a b)) πd ∧
      subst (fun _ : Unit => π) πd = FGL.nmul (formalGroup (shortO a b)) p ∧
      ‖coeff (Finsupp.single () 1) πd‖ = ‖hasse (formalGroup (shortO a b)) p‖ ∧
      Nonempty (VeluLubinLink G) := by
  classical
  have hp1 : ‖(p : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one (by have := hp.out.two_le; omega) (norm_nonneg _) ha.le hbreak
  haveI : CharZero K := charZero_of_norm p hε hp1
  obtain ⟨S, πd, h1, h2, h3, h4, -, -, -, ⟨κ, hκ⟩, hlink⟩ :=
    exists_step2_with_velu a b p hp5 hε hΔ ha hbreak
  have h2n : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3n : ‖(3 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0 := by
    intro h0
    have e : (((shortO a b).Δ : 𝒪) : K) = -16 * (4 * (a : K) ^ 3 + 27 * (b : K) ^ 2) := by
      have := congrArg (fun W : WeierstrassCurve K => W.Δ) (toK_shortO (K := K) a b)
      simp only [toK, WeierstrassCurve.map_Δ] at this
      rw [Subring.subtype_apply] at this
      rw [this, Velu.short_Δ]
    rw [e, h0, mul_zero, norm_zero] at hΔ
    exact zero_ne_one hΔ
  refine ⟨Lubin.quot S, Lubin.pis S, πd, h1, h2, h3, h4, hlink κ ?_⟩
  exact exists_integral_descent a b S κ hκ (Lubin.quot S) ⟨h1.1, h1.2⟩ hΔ' h2n h3n

end VeluDescent
