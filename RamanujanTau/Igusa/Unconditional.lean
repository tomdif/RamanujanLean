/-
# The Igusa layer without the `RamanujanODE` hypothesis

`RamanujanODEProof.ramanujanODE` proves Ramanujan's three q-series differential equations, so the Igusa
results and step (K) hold unconditionally.
-/
import RamanujanTau.Igusa.Katz
import RamanujanTau.RamanujanODE.Main

set_option autoImplicit false

namespace Igusa
open KatzForms MvPolynomial ModP Filter Topology

section Hasse
variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p)

/-- **Igusa** (unconditional): `Ā(t,1)` has no double root `t₀` with `t₀³ ≠ 1`. -/
theorem igusa_chartT' {t₀ : F} (ht : t₀ ^ 3 ≠ 1) :
    ¬ (Polynomial.X - Polynomial.C t₀) ^ 2 ∣ chartT (AF F p hp5) :=
  igusa_chartT hp5 RamanujanODEProof.ramanujanODE ht

theorem igusa_chartS' : ¬ Polynomial.X ^ 2 ∣ chartS (AF F p hp5) :=
  igusa_chartS hp5 RamanujanODEProof.ramanujanODE

/-- supersingular points exist (unconditional). -/
theorem exists_ss' [IsAlgClosed F] :
    ∃ x : Fin 2 → F, eval x (AF F p hp5) = 0 ∧ x 0 ^ 3 - x 1 ^ 2 ≠ 0 :=
  exists_ss hp5 RamanujanODEProof.ramanujanODE

end Hasse

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ} [hp : Fact p.Prime] [IsAlgClosed K]

/-- **Step (K), unconditional**: Katz-series integrality ⟺ sup norm `≤ 1` on `{‖E‖ ≥ ‖r‖}`. -/
theorem katz_iff_hasse' [CompleteSpace K] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p) (k₀ : ℕ)
    (r : K) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (b : ℕ → MvPolynomial (Fin 2) K) (hbB : ∀ i, b i ∈ katzPiece φ (Bz p hp5 k₀) i)
    (hb : Tendsto (fun i => gnorm (b i) / ‖r‖ ^ i) atTop (𝓝 0)) :
    (∀ i, gnorm (b i) ≤ ‖r‖ ^ i) ↔
      ∀ W : WeierstrassCurve K, IsTest W → ‖r‖ ≤ ‖eval (pt W) (Eh φ hp5)‖ →
        ‖kval (Eh φ hp5) b (pt W)‖ ≤ 1 :=
  katz_iff_hasse φ hφ hpK hp5 RamanujanODEProof.ramanujanODE k₀ r hr0 hr1 b hbB hb

end Igusa
