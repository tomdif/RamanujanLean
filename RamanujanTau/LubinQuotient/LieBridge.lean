/-
# Feeding Lubin's construction into `AtkinOBrien.Lie.lie_dual`

With `π = pis S` and the dual `π̌` from `exists_dual`, the hypotheses `hcomp` and `hW` of
`AtkinOBrien.Lie.lie_dual` are discharged: `π̌ ∘ π = [p]`, and `ι(π) = X · ∏_{h ∈ H∖0} (X − ι h) · U`
with `‖U(0)‖ = 1`.
-/
import RamanujanTau.LubinQuotient.Quotient
import RamanujanTau.AtkinOBrien.Lie

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O] [IsDomain O] [DecidableEq O]

variable {F : FormalGroup O} [F.IsComm] (S : FinSub F)

variable {K : Type*} [NormedField K]

/-- the image of `π` over `K` factors as `X · ∏_{h ∈ H∖0} (X − ι h) · U` with `‖U(0)‖ = 1`. -/
theorem pis_factor_map (ι : O →+* K) (hι : ∀ r, ‖ι r‖ ≤ 1) :
    ∃ U : PowerSeries K, ‖PowerSeries.constantCoeff U‖ = 1 ∧
      MvPowerSeries.map ι (pis S) =
        (((Polynomial.X * ∏ i : {h // h ∈ S.H.erase 0}, (Polynomial.X - Polynomial.C (ι i.1)) :
          Polynomial K) : PowerSeries K) * U) := by
  obtain ⟨U, hU, hpi⟩ := pis_factor S
  refine ⟨MvPowerSeries.map ι U, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mp hU
    have hc : PowerSeries.constantCoeff (MvPowerSeries.map ι U : PowerSeries K) = ι (u : O) := by
      rw [hu]; exact constantCoeff_map ι U
    rw [hc]
    have h1 := hι u
    have h2 := hι ↑u⁻¹
    have h3 : ‖ι (u : O)‖ * ‖ι (↑u⁻¹ : O)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    nlinarith [norm_nonneg (ι (u : O)), norm_nonneg (ι (↑u⁻¹ : O))]
  · rw [hpi, map_mul, map_prod]
    congr 1
    rw [← Finset.mul_prod_erase S.H _ S.zero_mem]
    rw [Polynomial.coe_mul, Polynomial.coe_X]
    have h0 : MvPowerSeries.map ι (X () - C 0 : MvPowerSeries Unit O) = PowerSeries.X := by
      simp [map_X]; rfl
    rw [h0]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod,
      ← Finset.prod_coe_sort (S.H.erase 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_X,
      Polynomial.coe_C, map_sub, map_X, map_C]
    rfl

/-- **`v(Lie π̌) = v` for Lubin's dual isogeny**: `AtkinOBrien.Lie.lie_dual` applied to
`π = ∏_{h ∈ H} F(X, h)` and its dual `π̌` (`π̌ ∘ π = [p]`, which exists since `H ⊆ F[p]`). -/
theorem lie_dual_lubin (ι : O →+* K) (hι : ∀ r, ‖ι r‖ ≤ 1) (p : ℕ)
    (hp : ∀ h ∈ S.H, pt (fun _ : Unit => h) (FGL.nmul F p) = 0)
    (a : K) (hcan : ‖a‖ * ∏ h ∈ S.H.erase 0, ‖ι h‖ = ‖(p : K)‖) (hp0 : (p : K) ≠ 0) :
    ∃ πd : MvPowerSeries Unit O, subst (fun _ : Unit => pis S) πd = FGL.nmul F p ∧
      ‖ι (coeff (Finsupp.single () 1) πd)‖ = ‖a‖ := by
  obtain ⟨πd, hπd, -⟩ := exists_dual S p hp
  have hcc : constantCoeff πd = 0 := by
    have := congrArg constantCoeff hπd
    rwa [FGL.cc_subst _ (fun _ => cc_pis S), FGL.cc_nmul] at this
  obtain ⟨U, hU0, hW⟩ := pis_factor_map S ι hι
  refine ⟨πd, hπd, AtkinOBrien.Lie.lie_dual ι p F (pis S) πd (cc_pis S) hcc hπd
    (fun i : {h // h ∈ S.H.erase 0} => ι i.1) U hU0 hW a ?_ hp0⟩
  rw [← hcan, Finset.prod_coe_sort (S.H.erase 0) (fun h => ‖ι h‖)]

end Lubin
