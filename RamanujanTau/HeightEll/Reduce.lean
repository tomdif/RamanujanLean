/-
# Height `≤ 2`: over any field, and over the integers of an ultrametric field

* `coeff_p2_ne_zero_field`: `HeightEll.coeff_p2_ne_zero` without `IsAlgClosed` (base change to the
  algebraic closure).
* `topc_norm_eq_one`: for `W` over `𝒪 = integers K` with `‖p‖ < 1`, `‖Δ‖ = 1` and `‖a‖ < 1`
  (`a = hasse = coeff_p [p]`), the coefficient of `T^{p²}` has `‖topc‖ = 1` (reduce to
  `Frac(𝒪/𝔪)`, a field of characteristic `p`).
-/
import RamanujanTau.HeightEll.Main
import RamanujanTau.QuotientHasse.Reduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeightEll
open MvPowerSeries EllipticFormal

/-- coefficients of `[p]` commute with base change. -/
lemma coeff_nmul_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (W : WeierstrassCurve R)
    (n : ℕ) (e : Unit →₀ ℕ) :
    coeff e (FGL.nmul (formalGroup (W.map f)) n) = f (coeff e (FGL.nmul (formalGroup W) n)) := by
  rw [← formalGroup_map, FGL.nmul_map, coeff_map]

/-- **height `≤ 2` over any field of characteristic `p ≥ 5`**. -/
theorem coeff_p2_ne_zero_field {k : Type*} [Field k] (W : WeierstrassCurve k) (p : ℕ)
    [hp : Fact p.Prime] [CharP k p] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (ha : coeff (Finsupp.single () p) (FGL.nmul (formalGroup W) p) = 0) :
    coeff (Finsupp.single () (p ^ 2)) (FGL.nmul (formalGroup W) p) ≠ 0 := by
  set f := algebraMap k (AlgebraicClosure k)
  haveI : CharP (AlgebraicClosure k) p := charP_of_injective_algebraMap f.injective p
  have hΔ' : (W.map f).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero_iff _ f.injective).2 hΔ
  have ha' : FGL.aH p (formalGroup (W.map f)) = 0 := by
    show coeff _ _ = 0; rw [coeff_nmul_map, ha, map_zero]
  have h := coeff_p2_ne_zero (W.map f) p hp5 hΔ' ha'
  rw [coeff_nmul_map] at h
  intro h0; exact h (by rw [h0, map_zero])

section Integers
open QuotientHasse CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- **height `≤ 2` over `𝒪`**: `‖p‖ < 1`, `‖Δ‖ = 1`, `‖a‖ < 1` give `‖coeff_{p²} [p]‖ = 1`. -/
theorem topc_norm_eq_one (W : WeierstrassCurve 𝒪) (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hp1 : ‖(p : K)‖ < 1) (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1)
    (ha : ‖((hasse (formalGroup W) p : 𝒪) : K)‖ < 1) :
    ‖((topc (formalGroup W) p : 𝒪) : K)‖ = 1 := by
  set k := FractionRing (𝒪 ⧸ mI (K := K))
  set ρ : 𝒪 →+* k := (algebraMap (𝒪 ⧸ mI (K := K)) k).comp red
  have hinj : Function.Injective (algebraMap (𝒪 ⧸ mI (K := K)) k) := IsFractionRing.injective _ _
  have hρ : ∀ x : 𝒪, ρ x = 0 ↔ ‖(x : K)‖ < 1 := by
    intro x
    rw [RingHom.comp_apply, map_eq_zero_iff _ hinj, red_eq_zero]
  haveI : CharP k p := by
    apply (CharP.charP_iff_prime_eq_zero hp.out).2
    rw [← map_natCast ρ, hρ]; simpa using hp1
  have hΔ' : (W.map ρ).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, Ne, hρ, not_lt]; exact hΔ.ge
  have ha' : coeff (Finsupp.single () p) (FGL.nmul (formalGroup (W.map ρ)) p) = 0 := by
    rw [coeff_nmul_map, hρ]; exact ha
  have h := coeff_p2_ne_zero_field (W.map ρ) p hp5 hΔ' ha'
  rw [coeff_nmul_map, Ne, hρ, not_lt] at h
  exact le_antisymm (topc (formalGroup W) p).2 h

end Integers

end HeightEll
