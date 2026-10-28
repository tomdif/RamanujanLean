/-
# Upper bounds on the Vélu discriminants (no height hypothesis)

* `exists_integral_model`: `AllQuotients.exists_model_of_descent` without the height-two hypotheses:
  the `μ`-scaled Vélu curve is integral (good reduction is not claimed).
* **`norm_Δ_velu_le`**: for every order-`p` `FinSub` `C` of `F_W` (`W` short, any height),
  `‖Δ(veluC Pt(C))‖ ≤ ‖Lie π_C‖^12 = (∏_{c ∈ C∖0} ‖c‖)^12`.
* **`norm_Δ_veluC_le_one`**: if all points of `G` have integral coordinates, `‖Δ(veluC G)‖ ≤ 1`.
-/
import RamanujanTau.OrdQuot.Lift

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open MvPowerSeries FGL EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin AllQuotients

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "ι" => Subring.subtype (CanonicalIsogeny.integers K)

section Model
variable [CharZero K] [DecidableEq K]

/-- **the `μ`-scaled Vélu curve is integral** (any height). -/
theorem exists_integral_model [CompleteSpace K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (a b : 𝒪) (κ : Velu.Kernel (a : K) (b : K)) (G : FormalGroup 𝒪)
    [G.IsComm]
    (π : MvPowerSeries Unit 𝒪) (hπ : Hom (formalGroup (shortO a b)) G π)
    (hμ0 : ((coeff (Finsupp.single () 1) π : 𝒪) : K) ≠ 0)
    (θ : MvPowerSeries Unit 𝒪)
    (hθ : sb (MvPowerSeries.map ι π) (MvPowerSeries.map ι θ) =
      C ((coeff (Finsupp.single () 1) π : 𝒪) : K) * phi κ) :
    ∃ (A'' B'' : 𝒪),
      toK (shortO A'' B'') = ((⟨Units.mk0 ((coeff (Finsupp.single () 1) π : 𝒪) : K) hμ0, 0, 0, 0⟩ :
        WeierstrassCurve.VariableChange K) • (κ.curve : WeierstrassCurve K)) := by
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
  exact ⟨_, _, hWK⟩

/-- **the `Lie π_C`-scaled Vélu quotient by `Pt(C)` has an integral model** (any height). -/
theorem exists_model_velu [CompleteSpace K] [IsAlgClosed K] (a b : ↥(CanonicalIsogeny.integers K))
    (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hp1 : ‖(p : K)‖ < 1)
    (hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0)
    (C : Lubin.FinSub (formalGroup (shortO a b))) (κ : Velu.Kernel (a : K) (b : K))
    (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (C.H : Set 𝒪)) :
    ∃ (A'' B'' : ↥(CanonicalIsogeny.integers K)),
      toK (shortO A'' B'') = ((⟨Units.mk0 _ (lie_pis_ne_zero C), 0, 0, 0⟩ :
        WeierstrassCurve.VariableChange K) • (SubgroupSum.veluC κ.G : WeierstrassCurve K)) := by
  have h2n : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3n : ‖(3 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hπ : Hom (formalGroup (shortO a b)) (Lubin.quot C) (Lubin.pis C) :=
    ⟨Lubin.cc_pis C, Lubin.pis_hom C⟩
  obtain ⟨θ, hθ⟩ := VeluDescent.exists_integral_descent a b C κ hκ (Lubin.quot C) hπ hΔ' h2n h3n
  obtain ⟨A'', B'', hK⟩ := exists_integral_model p hp5 hp1 a b κ (Lubin.quot C) (Lubin.pis C) hπ
    (lie_pis_ne_zero C) θ hθ
  refine ⟨A'', B'', ?_⟩
  rw [hK, SubgroupSum.Kernel.curve_eq_veluC two_ne_zero κ]

/-- **`‖Δ(veluC Pt(C))‖ ≤ (∏_{c ∈ C∖0} ‖c‖)^12`** for every order-`p` `FinSub` `C` (any height). -/
theorem norm_Δ_velu_le [CompleteSpace K] [IsAlgClosed K] (a b : ↥(CanonicalIsogeny.integers K))
    (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hp1 : ‖(p : K)‖ < 1)
    (hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0)
    (C : Lubin.FinSub (formalGroup (shortO a b))) (κ : Velu.Kernel (a : K) (b : K))
    (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (C.H : Set 𝒪)) :
    ‖(SubgroupSum.veluC κ.G).Δ‖ ≤ (∏ c ∈ C.H.erase 0, ‖(c : K)‖) ^ 12 := by
  obtain ⟨A'', B'', hK⟩ := exists_model_velu a b p hp5 hp1 hΔ' C κ hκ
  have e := congrArg (fun W : WeierstrassCurve K => ‖W.Δ‖) hK
  simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
  rw [EllipticI2.norm_Δ_scale, Units.val_mk0] at e
  set μ := ((coeff (Finsupp.single () 1) (Lubin.pis C) : 𝒪) : K)
  have hμ : 0 < ‖μ‖ := norm_pos_iff.2 (lie_pis_ne_zero C)
  have hle : ‖(((shortO A'' B'').Δ : 𝒪) : K)‖ ≤ 1 := ((shortO A'' B'').Δ).2
  rw [e, inv_pow] at hle
  have h12 : 0 < ‖μ‖ ^ 12 := by positivity
  rw [inv_mul_le_iff₀ h12, mul_one] at hle
  rw [← norm_lie_pis]
  exact hle

end Model

/-! ### Integral points give integral Vélu quotients -/

section Etale
variable [DecidableEq K]

lemma ofNat_mem_O (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : K) ∈ CanonicalIsogeny.integers K := by
  exact_mod_cast natCast_mem (CanonicalIsogeny.integers K) n

/-- **integral points give integral Vélu coefficients** `aC G`, `bC G`. -/
theorem aC_bC_le_one {A B : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (h2 : ‖(2 : K)‖ = 1)
    (G : Finset (Velu.short A B).Point)
    (hG : ∀ Q ∈ G, ‖Velu.xc Q‖ ≤ 1 ∧ ‖Velu.yc Q‖ ≤ 1) :
    ‖SubgroupSum.aC G‖ ≤ 1 ∧ ‖SubgroupSum.bC G‖ ≤ 1 := by
  set O := CanonicalIsogeny.integers K
  have hAO : A ∈ O := hA
  have hBO : B ∈ O := hB
  have hx : ∀ Q ∈ G.erase 0, Velu.xc Q ∈ O := fun Q hQ => (hG Q (Finset.mem_of_mem_erase hQ)).1
  have hy : ∀ Q ∈ G.erase 0, Velu.yc Q ∈ O := fun Q hQ => (hG Q (Finset.mem_of_mem_erase hQ)).2
  have htQ : ∀ Q ∈ G.erase 0, Velu.Kernel.tQ (A := A) (B := B) Q ∈ O := fun Q hQ => by
    simp only [Velu.Kernel.tQ]
    exact add_mem (mul_mem (ofNat_mem_O 6) (pow_mem (hx Q hQ) 2)) (mul_mem (ofNat_mem_O 2) hAO)
  have ht : SubgroupSum.tSum G ∈ O := sum_mem htQ
  have hw : SubgroupSum.wSum G ∈ O := by
    refine sum_mem fun Q hQ => add_mem ?_ (mul_mem (hx Q hQ) (htQ Q hQ))
    simp only [Velu.Kernel.uQ]
    exact mul_mem (ofNat_mem_O 4) (pow_mem (hy Q hQ) 2)
  have hdiv : ∀ x ∈ O, x / 2 ∈ O := fun x hx' => by
    show ‖x / 2‖ ≤ 1
    rw [norm_div, h2, div_one]; exact hx'
  have haC : SubgroupSum.aC G ∈ O := sub_mem hAO (hdiv _ (mul_mem (ofNat_mem_O 5) ht))
  have hbC : SubgroupSum.bC G ∈ O := sub_mem hBO (hdiv _ (mul_mem (ofNat_mem_O 7) hw))
  exact ⟨haC, hbC⟩

/-- **integral points give an integral Vélu quotient**: `‖Δ(veluC G)‖ ≤ 1`. -/
theorem norm_Δ_veluC_le_one {A B : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (h2 : ‖(2 : K)‖ = 1)
    (G : Finset (Velu.short A B).Point)
    (hG : ∀ Q ∈ G, ‖Velu.xc Q‖ ≤ 1 ∧ ‖Velu.yc Q‖ ≤ 1) : ‖(SubgroupSum.veluC G).Δ‖ ≤ 1 := by
  set O := CanonicalIsogeny.integers K
  obtain ⟨haC, hbC⟩ := aC_bC_le_one hA hB h2 G hG
  have haC : SubgroupSum.aC G ∈ O := haC
  have hbC : SubgroupSum.bC G ∈ O := hbC
  have hΔ : (SubgroupSum.veluC G).Δ ∈ O := by
    rw [SubgroupSum.veluC, Velu.short_Δ]
    exact mul_mem (neg_mem (ofNat_mem_O 16)) (add_mem (mul_mem (ofNat_mem_O 4) (pow_mem haC 3))
      (mul_mem (ofNat_mem_O 27) (pow_mem hbC 2)))
  exact hΔ

end Etale

end OrdQuot
