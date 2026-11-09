/-
# All ten fifth-order mock theta identities from Ramanujan's Lost Notebook

Notation (all in `ℤ⟦q⟧`, `q = X`):
* `Pinf r M = (q^r; q^M)_∞`, `Ring.inverse` is `1/·` on units;
* `Φ = RankProof.Phi 1`, `Ψ = RankProof.Phi 2`; Andrews–Garvan's mock theta functions are
  `Φ_AG(q) = Φ − 1 = −1 + Σ_{n≥0} q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n)` and `Ψ_AG(q) = Ψ − 1`;
* `expand 2` is `q ↦ q²`; `negQ` is `q ↦ −q`.

The ten functions are those of `MockTheta5Defs`/`Watson`/`MockTheta5All.Defs`:
`f₀ = MockTheta5.JTP.f0`, `f₁ = MockTheta5.JTP.f1`, `F₀ = Watson.F0w`, `F₁ = F1w`, `φ₀ = phi0w`, `φ₁ = phi1w`,
`ψ₀ = psi0w`, `ψ₁ = psi1w`, `χ₀ = MockTheta5.Formal.chi0`, `χ₁ = chi1w`.

All ten are unconditional; see `docs/MOCK_THETA5_ALL.md` for the reduction chain.
-/
import RamanujanTau.MockTheta5All.F0
import RamanujanTau.MockTheta5All.F1

set_option autoImplicit false

namespace MockTheta5All
open PowerSeries Watson RankProof

/-- **(1) MTC₀** `f₀(q) = ϑ₄(q⁵)G(q) − 2Φ_AG(q²)`. -/
theorem mock_theta_f0 :
    MockTheta5.JTP.f0 =
      Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 1 5 * Pinf 4 5) - 2 * (expand 2 two_ne_zero (Phi 1) - 1) :=
  MTC.mock_theta_conjecture_f0

/-- **(2) MTC₁** `q f₁(q) = q ϑ₄(q⁵)H(q) − 2Ψ_AG(q²)`. -/
theorem mock_theta_f1 :
    X * MockTheta5.JTP.f1 =
      X * (Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 2 5 * Pinf 3 5)) - 2 * (expand 2 two_ne_zero (Phi 2) - 1) :=
  MTC.mock_theta_conjecture_f1

/-- **(3)** `F₀(q) − 1 = Φ_AG(q) − q (q¹⁰;q¹⁰)_∞/((q⁴;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁶;q¹⁰)_∞)`. -/
theorem mock_theta_F0 :
    F0w = Phi 1 - X * (Pinf 10 10 * Ring.inverse (Pinf 4 10 * Pinf 5 10 * Pinf 6 10)) :=
  mtc_F0

/-- **(4)** `F₁(q) = q⁻¹Ψ_AG(q) + (q¹⁰;q¹⁰)_∞/((q²;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁸;q¹⁰)_∞)`, multiplied by `q`. -/
theorem mock_theta_F1 :
    X * F1w = (Phi 2 - 1) + X * (Pinf 10 10 * Ring.inverse (Pinf 2 10 * Pinf 5 10 * Pinf 8 10)) :=
  mtc_F1

/-- **(5)** `φ₀(−q) = −Φ_AG(q) + (q⁴,q⁵,q⁶,q¹⁰;q¹⁰)_∞/((q²;q¹⁰)²_∞(q³;q¹⁰)_∞(q⁷;q¹⁰)_∞(q⁸;q¹⁰)²_∞)`. -/
theorem mock_theta_phi0 :
    negQ phi0w = -(Phi 1 - 1) +
      Pinf 4 10 * Pinf 5 10 * Pinf 6 10 * Pinf 10 10 *
        Ring.inverse (Pinf 2 10 ^ 2 * Pinf 3 10 * Pinf 7 10 * Pinf 8 10 ^ 2) :=
  mtc_phi0

/-- **(6)** `φ₁(−q) = Ψ_AG(q) − q (q²,q⁵,q⁸,q¹⁰;q¹⁰)_∞/((q;q¹⁰)_∞(q⁴;q¹⁰)²_∞(q⁶;q¹⁰)²_∞(q⁹;q¹⁰)_∞)`. -/
theorem mock_theta_phi1 :
    negQ phi1w = (Phi 2 - 1) -
      X * (Pinf 2 10 * Pinf 5 10 * Pinf 8 10 * Pinf 10 10 *
        Ring.inverse (Pinf 1 10 * Pinf 4 10 ^ 2 * Pinf 6 10 ^ 2 * Pinf 9 10)) :=
  mtc_phi1

/-- **(7)** `ψ₀(q) = Φ_AG(q²) + q (q,q⁹,q¹⁰;q¹⁰)_∞/((q²,q³,q⁷,q⁸;q¹⁰)_∞)`. -/
theorem mock_theta_psi0 :
    psi0w = (expand 2 two_ne_zero (Phi 1) - 1) +
      X * (Pinf 1 10 * Pinf 9 10 * Pinf 10 10 * Ring.inverse (Pinf 2 10 * Pinf 3 10 * Pinf 7 10 * Pinf 8 10)) :=
  mtc_psi0

/-- **(8)** `ψ₁(q) = q⁻¹Ψ_AG(q²) + (q³,q⁷,q¹⁰;q¹⁰)_∞/((q,q⁴,q⁶,q⁹;q¹⁰)_∞)`, multiplied by `q`. -/
theorem mock_theta_psi1 :
    X * psi1w = (expand 2 two_ne_zero (Phi 2) - 1) +
      X * (Pinf 3 10 * Pinf 7 10 * Pinf 10 10 * Ring.inverse (Pinf 1 10 * Pinf 4 10 * Pinf 6 10 * Pinf 9 10)) :=
  mtc_psi1

/-- **(9)** `χ₀(q) − 2 = 3Φ_AG(q) − (q⁵;q⁵)²_∞ J_{5,2}/J_{5,1}²` (Watson 1937 route). -/
theorem mock_theta_chi0 :
    MockTheta5.Formal.chi0 - 2 =
      3 * (Phi 1 - 1) - MockTheta5.JTP.eQ ^ 2 * CrankProof.Jab 5 2 * Ring.inverse (CrankProof.Jab 5 1) ^ 2 :=
  Watson.chi0_identity

/-- **(10)** `χ₁(q) = 3q⁻¹Ψ_AG(q) + (q,q⁴,q⁵;q⁵)_∞/((q²;q⁵)²_∞(q³;q⁵)²_∞)`, multiplied by `q`. -/
theorem mock_theta_chi1 :
    X * chi1w = 3 * (Phi 2 - 1) +
      X * (Pinf 1 5 * Pinf 4 5 * Pinf 5 5 * Ring.inverse (Pinf 2 5 ^ 2 * Pinf 3 5 ^ 2)) :=
  mtc_chi1

/-! ### the remaining Lost Notebook relations, proved along the way -/

/-- Ramanujan's (B₁) `qχ₁(q) = 2qF₁(q) + φ₁(−q)`. -/
theorem ramanujan_B1 : X * chi1w = 2 * X * F1w + negQ phi1w := by
  rw [negQ_phi1w]; exact watson_B1

/-- Ramanujan's (B₀) `χ₀(q) = 2F₀(q) − φ₀(−q)`. -/
theorem ramanujan_B0 : MockTheta5.Formal.chi0 = 2 * F0w - negQ phi0w := by
  rw [negQ_phi0w, ← chiA_eq]; exact chi0_R1_watson

end MockTheta5All
