/-
# The Vélu–Lubin link, reduced to two integrality statements

Setting: `K` ultrametric of characteristic `0`, `𝒪 = integers K`, `W = y² = x³ + ax + b` over `𝒪`
(`shortO a b`), `κ` Vélu kernel data over `K` for `W_K`, `E' = κ.curve : y² = x³ + A'x + B'` and
`φ = phi κ` the formal Vélu map (`Formal.lean`: a homomorphism `F_{W_K} → F_{E'}` with `φ'(0) = 1`).

Let `π : F_W → G` be a homomorphism over `𝒪` with `μ = π'(0) ≠ 0` (e.g. Lubin's quotient by the
canonical subgroup, `‖μ‖ = ‖p‖/‖a‖`).

**`link_of_integral`**: assume
* (I1) *integral descent*: `μ φ = θ ∘ π` over `K` for some `θ ∈ 𝒪⟦T⟧`;
* (I2) *integral Vélu model*: `‖A'‖ ≤ ‖μ‖⁴`, `‖B'‖ ≤ ‖μ‖⁶`, `‖Δ(E')‖ = ‖μ‖¹²`.
Then `W'' = y² = x³ + μ⁻⁴A' x + μ⁻⁶B'` is a curve over `𝒪` with `‖Δ(W'')‖ = 1` (it is
`⟨μ,0,0,0⟩ • E'`), `θ : G → F_{W''}` is a homomorphism over `𝒪` with `θ'(0) = 1`, and its inverse
`ψ = θ⁻¹` gives `VeluLubinLink G`.
-/
import RamanujanTau.VeluLubin.Formal
import RamanujanTau.VeluLubin.Hom

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries FGL EllipticFormal EllipticI2 CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K
local notation "ι" => Subring.subtype (integers K)

/-- the short curve `y² = x³ + a x + b` over a commutative ring. -/
def shortO {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R := ⟨0, 0, 0, a, b⟩

lemma toK_shortO (a b : 𝒪) : toK (shortO a b) = Velu.short (a : K) (b : K) := by
  ext <;> simp [toK, shortO, Velu.short]

lemma lin_sb {R : Type*} [CommRing R] {f g : MvPowerSeries Unit R} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) :
    coeff (Finsupp.single () 1) (sb g f) =
      coeff (Finsupp.single () 1) f * coeff (Finsupp.single () 1) g :=
  AtkinOBrien.Lie.coeff_one_comp f g hf hg

/-- the scaling `T ↦ μ T` is a homomorphism `F_E → F_{⟨μ,0,0,0⟩ • E}`. -/
theorem hom_scale {L : Type*} [Field L] (E : WeierstrassCurve L) (u : Lˣ) :
    Hom (formalGroup E) (formalGroup ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange L) • E))
      (C (u : L) * X ()) := by
  refine ⟨by simp, ?_⟩
  have h := rescale_F E u
  rw [rescale_eq_subst] at h
  have e1 : ∀ (a : MvPowerSeries (Fin 2) L), constantCoeff a = 0 →
      subst (fun _ : Unit => a) (C (u : L) * X () : MvPowerSeries Unit L) = C (u : L) * a := by
    intro a ha
    rw [subst_mul (hs (hc ha)), subst_C, sX _ (hc ha)]
  rw [e1 (ev (formalGroup E) (X 0 : MvPowerSeries (Fin 2) L) (X 1)) (cc_ev _ cX0 cX1),
    e1 (X 0 : MvPowerSeries (Fin 2) L) cX0, e1 (X 1 : MvPowerSeries (Fin 2) L) cX1]
  have hX : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) L) = X := by
    funext i; fin_cases i <;> rfl
  rw [ev, ev]
  simp only [formalGroup_toPowerSeries]
  rw [hX, subst_self, id, ← h]
  congr 1
  funext i
  fin_cases i <;> simp [smul_eq_C_mul]

variable [CharZero K] [DecidableEq K]

/-- **The Vélu–Lubin link from integral descent and an integral Vélu model.** -/
theorem link_of_integral (a b : 𝒪) (κ : Velu.Kernel (a : K) (b : K)) (G : FormalGroup 𝒪)
    (π : MvPowerSeries Unit 𝒪) (hπ : Hom (formalGroup (shortO a b)) G π)
    (hμ0 : ((coeff (Finsupp.single () 1) π : 𝒪) : K) ≠ 0)
    (θ : MvPowerSeries Unit 𝒪)
    (hθ : sb (MvPowerSeries.map ι π) (MvPowerSeries.map ι θ) =
      C ((coeff (Finsupp.single () 1) π : 𝒪) : K) * phi κ)
    (hA : ‖κ.A'‖ ≤ ‖((coeff (Finsupp.single () 1) π : 𝒪) : K)‖ ^ 4)
    (hB : ‖κ.B'‖ ≤ ‖((coeff (Finsupp.single () 1) π : 𝒪) : K)‖ ^ 6)
    (hΔ : ‖κ.curve.Δ‖ = ‖((coeff (Finsupp.single () 1) π : 𝒪) : K)‖ ^ 12) :
    Nonempty (VeluLubinLink G) := by
  set μ : K := ((coeff (Finsupp.single () 1) π : 𝒪) : K) with hμ
  set μu : Kˣ := Units.mk0 μ hμ0
  have hμn : 0 < ‖μ‖ := norm_pos_iff.2 hμ0
  -- the integral model `W''`
  have hA'' : ‖κ.A' / μ ^ 4‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one (pow_pos hμn 4)]; exact hA
  have hB'' : ‖κ.B' / μ ^ 6‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one (pow_pos hμn 6)]; exact hB
  set W'' : WeierstrassCurve 𝒪 := shortO ⟨κ.A' / μ ^ 4, hA''⟩ ⟨κ.B' / μ ^ 6, hB''⟩
  have hWK : toK W'' = (⟨μu, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • κ.curve := by
    ext
    · simp [W'', toK, shortO, WeierstrassCurve.variableChange_a₁, Velu.Kernel.curve]
    · simp [W'', toK, shortO, WeierstrassCurve.variableChange_a₂, Velu.Kernel.curve]
    · simp [W'', toK, shortO, WeierstrassCurve.variableChange_a₃, Velu.Kernel.curve]
    · simp [W'', toK, shortO, WeierstrassCurve.variableChange_a₄, Velu.Kernel.curve, μu]
      ring
    · simp [W'', toK, shortO, WeierstrassCurve.variableChange_a₆, Velu.Kernel.curve, μu]
      ring
  have hΔ'' : ‖((W''.Δ : 𝒪) : K)‖ = 1 := by
    have e : ((W''.Δ : 𝒪) : K) = (toK W'').Δ := by rw [toK, WeierstrassCurve.map_Δ]; rfl
    have hu : (((⟨μu, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K).u⁻¹ : Kˣ) : K) = μ⁻¹ := by
      simp [μu]
    rw [e, hWK, WeierstrassCurve.variableChange_Δ, norm_mul, hΔ, norm_pow, hu, norm_inv, ← mul_pow,
      inv_mul_cancel₀ hμn.ne', one_pow]
  -- `σ = μ φ : F_W → F_{W''}` over `K`
  have hsc : Hom (formalGroup κ.curve) (formalGroup (toK W'')) (C μ * X ()) := by
    rw [hWK]; exact hom_scale κ.curve μu
  have hσ : Hom (formalGroup (Velu.short (a : K) (b : K))) (formalGroup (toK W''))
      (C μ * phi κ) := by
    have h := hom_comp (velu_formal_hom κ) hsc
    have e : sb (phi κ) (C μ * X () : MvPowerSeries Unit K) = C μ * phi κ := by
      rw [sb, subst_mul (hs (hc (cc_phi κ))), subst_C, sX _ (hc (cc_phi κ))]
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
  -- `θ : G → F_{W''}` over `K`, then over `𝒪`
  have hθK : Hom (G.map ι) (formalGroup (toK W'')) (MvPowerSeries.map ι θ) :=
    hom_of_comp hπK hσ hθ hρ0 hρπ hπρ
  have hθ0 : constantCoeff θ = 0 := by
    have h := congrArg constantCoeff hθ
    rw [sb, cc_subst _ (hc hπK.1), constantCoeff_map, map_mul, cc_phi, mul_zero] at h
    exact Subtype.val_injective (by simpa using h)
  have hθG : Hom G (formalGroup W'') θ := by
    refine hom_of_map ι Subtype.val_injective hθ0 ?_
    rw [formalGroup_map]; exact hθK
  have hθ1 : coeff (Finsupp.single () 1) θ = 1 := by
    have h := congrArg (coeff (Finsupp.single () 1)) hθ
    rw [lin_sb (cc_map ι hθ0) hπK.1, coeff_C_mul, lie_phi, mul_one, coeff_map, coeff_map] at h
    apply Subtype.val_injective
    have := mul_right_cancel₀ hμ0 (h.trans (one_mul μ).symm)
    simpa using this
  -- the inverse `ψ = θ⁻¹ : F_{W''} → G`
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
  have hψ : Hom (formalGroup W'') G ψ := hom_inv hθG hψ0 hψθ hθψ
  have hψ1 : coeff (Finsupp.single () 1) ψ = 1 := by
    have h := PowerSeries.coeff_one_substInvOfIsUnit (θ : PowerSeries 𝒪) hθu
    have hu : hθu.unit = 1 := Units.ext (by simp [IsUnit.unit_spec]; exact hθ1)
    rw [hu, inv_one] at h
    exact h
  exact ⟨⟨W'', hΔ'', ψ, hψ, by rw [hψ1]; simp⟩⟩

end VeluLubin
