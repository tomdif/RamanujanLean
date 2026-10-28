/-
# Hasse invariant = E_{p−1} mod p, unconditionally

Deligne's congruence for the Tate curve (`TateFormal.hasseH_TateBar`) discharges the hypothesis `hT` of
`HasseInv.Modular`.
-/
import RamanujanTau.HasseInv.Modular
import RamanujanTau.TateFormal.Deligne

set_option autoImplicit false

namespace HasseInv
open EllipticFormal

variable (p : ℕ) [hp : Fact p.Prime]

theorem hassePoly_eq_hasseBar (hp5 : 5 ≤ p) : hassePoly p = ModP.hasseBar p hp5 :=
  (hassePoly_eq_hasseBar_iff p hp5).mpr (TateFormal.hasseH_TateBar p hp5)

/-- **`a = Ā(c₄, −c₆)` in characteristic `p`.** -/
theorem aH_eq_hasseBar' (hp5 : 5 ≤ p) {R : Type*} [CommRing R] [CharP R p] (W : WeierstrassCurve R) :
    FGL.aH p (formalGroup W) = evW W (ModP.hasseBar p hp5) :=
  aH_eq_hasseBar p hp5 (TateFormal.hasseH_TateBar p hp5) W

/-- **`a ≡ E_{p−1}(E, ω) (mod p)`** for every Weierstrass curve over a `ℤ_p`-algebra. -/
theorem coeff_nmul_sub_hasseA_mem' (hp5 : 5 ≤ p) {R : Type*} [CommRing R] [Algebra ℤ_[p] R]
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single () p) (FGL.nmul (formalGroup W) p) -
      MvPolynomial.aeval ![W.c₄, -W.c₆] (ModP.hasseA p hp5) ∈ Ideal.span {(p : R)} :=
  coeff_nmul_sub_hasseA_mem p hp5 (TateFormal.hasseH_TateBar p hp5) W

end HasseInv
