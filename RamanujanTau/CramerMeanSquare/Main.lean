/-
# The Cramér–Tong mean square of `∑_{n≤x} τ(n)` with the exact constant (logarithmic form)

Write `S(x) = ∑_{1≤n≤x} τ(n)` and `B = ∑_{n≥1} τ(n)² n^{−25/2}` (`= 1.58281…`).
Evidence level (1): Lean, axiom-clean, unconditional; Deligne is not used.

* `tau_cramer_log`:  `(∫₁^X S(x)² x^{−25/2} dx) / log X → B/(4π²)`;
* `tau_cramer_mellin`: `δ ∫₁^∞ S(x)² x^{−25/2−2δ} dx → B/(8π²)` as `δ → 0⁺`;
* `tau_cramer_limsup`, `tau_cramer_liminf`: with `C₀ = B/(50π²)`,
  `liminf_{X→∞} X^{−25/2} ∫₁^X S² ≤ C₀ ≤ limsup_{X→∞} X^{−25/2} ∫₁^X S²`;
* `tau_cramer_constant`: **if** `X^{−25/2} ∫₁^X S²` converges, the limit is `B/(50π²)`.
  (Existence of that limit, the classical Cramér–Tong theorem, is not proved here.)
* `tau_mean_square_uniform` (the new analytic input): Carlson–Potter
  `(1/T)∫₀ᵀ |L(Δ,σ+it)|² dt → Σ τ(n)² n^{−2σ}` **uniformly** in `σ ∈ [31/5, 25/4]`.

Build: `nice -n 10 lake build RamanujanTau.CramerMeanSquare.Main`.  See `docs/CRAMER_MEAN_SQUARE.md`.
-/
import RamanujanTau.CramerMeanSquare.Partial

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL

/-- **Cramér–Tong, logarithmic form, exact constant**:
`∫₁^X S(x)² x^{−25/2} dx ~ (B/(4π²)) log X`. -/
theorem tau_cramer_log :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2 : ℝ))) / Real.log X) atTop
      (𝓝 ((∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (4 * π ^ 2))) :=
  tau_cramer_log_core

/-- **Exact Mellin constant**: `δ ∫₁^∞ S(x)² x^{−25/2−2δ} dx → B/(8π²)`. -/
theorem tau_cramer_mellin :
    Tendsto (fun δ : ℝ => δ * ∫ x in Ioi (1 : ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2) - 2 * δ)) (𝓝[>] 0)
      (𝓝 ((∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (8 * π ^ 2))) :=
  delta_Phi_tendsto

/-- `∫₁^X S² > c X^{25/2}` for arbitrarily large `X` whenever `c < B/(50π²)`. -/
theorem tau_cramer_limsup {c : ℝ}
    (hc : c < (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (50 * π ^ 2)) :
    ∀ Y : ℝ, ∃ X : ℝ, Y ≤ X ∧
      c * X ^ (25 / 2 : ℝ) < ∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 := by
  intro Y
  obtain ⟨X, h1, h2⟩ := ((frequently_gt hc).and_eventually (eventually_ge_atTop Y)).exists
  exact ⟨X, h2, h1⟩

/-- `∫₁^X S² < c X^{25/2}` for arbitrarily large `X` whenever `c > B/(50π²)`. -/
theorem tau_cramer_liminf {c : ℝ}
    (hc : (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (50 * π ^ 2) < c) :
    ∀ Y : ℝ, ∃ X : ℝ, Y ≤ X ∧
      ∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 < c * X ^ (25 / 2 : ℝ) := by
  intro Y
  obtain ⟨X, h1, h2⟩ := ((frequently_lt hc).and_eventually (eventually_ge_atTop Y)).exists
  exact ⟨X, h2, h1⟩

/-- **The Cramér constant**: if `X^{−25/2} ∫₁^X S(x)² dx` converges, its limit is `B/(50π²)`. -/
theorem tau_cramer_constant {C : ℝ}
    (h : Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2) / X ^ (25 / 2 : ℝ)) atTop (𝓝 C)) :
    C = (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (50 * π ^ 2) :=
  const_of_tendsto h

/-- **Uniform Carlson–Potter mean value** on `σ ∈ [31/5, 25/4]`. -/
theorem tau_mean_square_uniform : ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
    ∀ σ : ℝ, 31 / 5 ≤ σ → σ ≤ 25 / 4 → ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T -
        ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))| ≤ E T :=
  mean_square_unif

end RamanujanTau.CramerMeanSquare

#print axioms RamanujanTau.CramerMeanSquare.tau_cramer_log
#print axioms RamanujanTau.CramerMeanSquare.tau_cramer_mellin
#print axioms RamanujanTau.CramerMeanSquare.tau_cramer_limsup
#print axioms RamanujanTau.CramerMeanSquare.tau_cramer_liminf
#print axioms RamanujanTau.CramerMeanSquare.tau_cramer_constant
#print axioms RamanujanTau.CramerMeanSquare.tau_mean_square_uniform
#print axioms RamanujanTau.CramerMeanSquare.approx_tauL_unif
#print axioms RamanujanTau.CramerMeanSquare.abel_param
#print axioms RamanujanTau.CramerMeanSquare.R_unif
#print axioms RamanujanTau.CramerMeanSquare.Psi_eq
#print axioms RamanujanTau.CramerMeanSquare.abel_L
#print axioms RamanujanTau.CramerMeanSquare.karamata_ab
#print axioms RamanujanTau.CramerMeanSquare.J_identity
