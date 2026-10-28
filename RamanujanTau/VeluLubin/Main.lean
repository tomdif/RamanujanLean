/-
# The Vélu–Lubin link from integral descent alone

`K` complete, algebraically closed, ultrametric, characteristic `0`; `p ≥ 5` prime, `‖p‖ < 1`;
`W : y² = x³ + ax + b` over `𝒪`; `κ` Vélu kernel data for `W_K`; `φ = phi κ` the formal Vélu map;
`G` a formal group over `𝒪` of height exactly `2`; `π : F_W → G` a homomorphism with `μ = π'(0) ≠ 0`.

**`link_of_descent`**: if (integral descent) `μ·φ = θ ∘ π` over `K` for some `θ ∈ 𝒪⟦T⟧`, then
`VeluLubinLink G`. Compared to `link_of_integral`, the integrality of the Vélu model is now proved:
* `θ : G → F_{E''}` over `K` (`E'' = ⟨μ,0,0,0⟩ • E'`), and `F_{E''} = θ(G(ψX, ψY))` with
  `ψ = θ⁻¹ ∈ 𝒪⟦T⟧`; so the invariant differential `Ψ_{E''} = 1 - 2a₄''Tw - 3a₆''w²` has integral
  coefficients, whence `‖a₄''‖, ‖a₆''‖ ≤ 1` (`coeff4_Ψ`, `coeff6_Ψ`, `‖2‖ = ‖3‖ = 1`);
* `‖Δ(E'')‖ = 1` by good reduction from the formal group (`GoodRed.norm_Δ_eq_one_of_iso`).
-/
import RamanujanTau.VeluLubin.GoodRed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries FGL EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse

/-! ### The invariant differential of a short curve -/

section Psi
variable {R : Type*} [CommRing R] (A B : R)

lemma coeff6_w_sq : PowerSeries.coeff 6 (w (shortO A B) ^ 2) = 1 := by
  rw [w_eq_X3_mul_v, mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, cc_v, one_pow]

lemma Ψ_short : FGL.Ψ (formalGroup (shortO A B)) (FGL.T : MvPowerSeries Unit R) =
    1 - 2 * C A * X () * (w (shortO A B) : MvPowerSeries Unit R) -
      3 * C B * (w (shortO A B) : MvPowerSeries Unit R) ^ 2 := by
  rw [Ψ_formalGroup]
  simp [shortO]

/-- `[T⁴] Ψ = -2a₄`. -/
lemma coeff4_Ψ : coeff (Finsupp.single () 4) (FGL.Ψ (formalGroup (shortO A B)) FGL.T) = -2 * A := by
  rw [Ψ_short]
  show PowerSeries.coeff 4 (1 - 2 * PowerSeries.C A * PowerSeries.X * w (shortO A B) -
    3 * PowerSeries.C B * w (shortO A B) ^ 2) = _
  have h1 : PowerSeries.coeff 4 (2 * PowerSeries.C A * PowerSeries.X * w (shortO A B)) = 2 * A := by
    rw [show (2 : PowerSeries R) * PowerSeries.C A * PowerSeries.X * w (shortO A B) =
      PowerSeries.C (2 * A) * (PowerSeries.X * w (shortO A B)) by simp [map_ofNat]; ring,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_three_w, mul_one]
  have h2 : PowerSeries.coeff 4 (3 * PowerSeries.C B * w (shortO A B) ^ 2) = 0 := by
    rw [show (3 : PowerSeries R) * PowerSeries.C B * w (shortO A B) ^ 2 =
      PowerSeries.C (3 * B) * w (shortO A B) ^ 2 by simp [map_ofNat],
      PowerSeries.coeff_C_mul, coeff_w_sq_of_lt _ (by norm_num), mul_zero]
  rw [map_sub, map_sub, h1, h2, PowerSeries.coeff_one]; simp

/-- `[T⁶] Ψ = -3a₆`. -/
lemma coeff6_Ψ : coeff (Finsupp.single () 6) (FGL.Ψ (formalGroup (shortO A B)) FGL.T) = -3 * B := by
  rw [Ψ_short]
  show PowerSeries.coeff 6 (1 - 2 * PowerSeries.C A * PowerSeries.X * w (shortO A B) -
    3 * PowerSeries.C B * w (shortO A B) ^ 2) = _
  have h1 : PowerSeries.coeff 6 (2 * PowerSeries.C A * PowerSeries.X * w (shortO A B)) = 0 := by
    rw [show (2 : PowerSeries R) * PowerSeries.C A * PowerSeries.X * w (shortO A B) =
      PowerSeries.C (2 * A) * (PowerSeries.X * w (shortO A B)) by simp [map_ofNat]; ring,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_five_w]
    simp [shortO]
  have h2 : PowerSeries.coeff 6 (3 * PowerSeries.C B * w (shortO A B) ^ 2) = 3 * B := by
    rw [show (3 : PowerSeries R) * PowerSeries.C B * w (shortO A B) ^ 2 =
      PowerSeries.C (3 * B) * w (shortO A B) ^ 2 by simp [map_ofNat],
      PowerSeries.coeff_C_mul, coeff6_w_sq, mul_one]
  rw [map_sub, map_sub, h1, h2, PowerSeries.coeff_one]; simp

end Psi

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K
local notation "ι" => Subring.subtype (integers K)

/-- `Ψ` of a base-changed law. -/
lemma Ψ_map (F₀ : MvPowerSeries (Fin 2) 𝒪) (G : FormalGroup K) (hG : G.toPowerSeries =
    MvPowerSeries.map ι F₀) (n : ℕ) :
    ‖coeff (Finsupp.single () n) (FGL.Ψ G (FGL.T : MvPowerSeries Unit K))‖ ≤ 1 := by
  have e : FGL.Ψ G (FGL.T : MvPowerSeries Unit K) =
      MvPowerSeries.map ι (subst ![(X () : MvPowerSeries Unit 𝒪), 0] (pd 1 F₀)) := by
    rw [FGL.Ψ, hG, map_subst (FGL.hs FGL.cc_T0), pd_map']
    congr 1
    funext i; fin_cases i <;> simp
  rw [e, coeff_map]
  exact (coeff (Finsupp.single () n) (subst ![(X () : MvPowerSeries Unit 𝒪), 0] (pd 1 F₀))).2

/-- `‖n‖ = 1` for `n` prime to `p` when `‖p‖ < 1`. -/
lemma norm_nat_eq_one (p : ℕ) [hp : Fact p.Prime] (hp1 : ‖(p : K)‖ < 1) (n : ℕ) (hn : ¬ p ∣ n) :
    ‖(n : K)‖ = 1 := by
  letI := charP_k (K := K) p hp1
  have h : red (K := K) (n : 𝒪) ≠ 0 := by
    rw [map_natCast]; intro h; exact hn ((CharP.cast_eq_zero_iff _ p n).1 h)
  have := red_ne_zero.1 h
  simpa using this

variable [CharZero K] [DecidableEq K]

/-- **The Vélu–Lubin link from integral descent.** -/
theorem link_of_descent [CompleteSpace K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (a b : 𝒪) (κ : Velu.Kernel (a : K) (b : K)) (G : FormalGroup 𝒪)
    [G.IsComm] (hu : ‖topc G p‖ = 1) (ha : ‖hasse G p‖ < 1)
    (π : MvPowerSeries Unit 𝒪) (hπ : Hom (formalGroup (shortO a b)) G π)
    (hμ0 : ((coeff (Finsupp.single () 1) π : 𝒪) : K) ≠ 0)
    (θ : MvPowerSeries Unit 𝒪)
    (hθ : sb (MvPowerSeries.map ι π) (MvPowerSeries.map ι θ) =
      C ((coeff (Finsupp.single () 1) π : 𝒪) : K) * phi κ) :
    Nonempty (VeluLubinLink G) := by
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
    have hg0 : constantCoeff (sb (X 0 : MvPowerSeries (Fin 2) 𝒪) ψ) = 0 := cc0 _ (hc cX0) hψ0
    have hg1 : constantCoeff (sb (X 1 : MvPowerSeries (Fin 2) 𝒪) ψ) = 0 := cc0 _ (hc cX1) hψ0
    rw [map_sb ι (cc_ev G hg0 hg1), map_ev' ι G hg0 hg1, map_sb ι cX0, map_sb ι cX1]
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
  exact ⟨⟨W'', hΔ'', ψ, hψ, by rw [hψ1]; simp⟩⟩

end VeluLubin
