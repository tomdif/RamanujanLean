/-
# The weight-12 Poincaré series `P₁` and the remaining named hypotheses

`poincare z = e(z) + ∑_{c ≥ 1} ∑_{d ∈ ℤ, (c,d) = 1} (cz+d)^{-12} e(d̄/c - 1/(c(cz+d)))`
(the sum over `Γ_∞ \ SL₂(ℤ)` of `j(γ,z)^{-12} e(γz)`, using `γz = a/c - 1/(c(cz+d))`, `a ≡ d̄ mod c`).
Numerically `poincare = 2.8402873751… · Δ` (`scripts/taubound/check_poincare_def.py`).

Remaining inputs for the unconditional sub-Hecke bound, stated as named hypotheses:

* `PoincareIsCuspForm`: `poincare` is (the restriction to `ℍ` of) a weight-12 cusp form for `SL₂(ℤ)`;
* `PoincareUnfolding`: any cusp form equal to `poincare` has the unfolded coefficients
  (`HasPoincareCoeffs`) — the Rankin–Petersson unfolding computation;
* `PoincareFirstCoeffNeZero`: `1 + ∑_{c≥1} c^{-12} S(1,1;c) K(1,c;1) ≠ 0`
  (numerically `= 2.8402873751…`, i.e. `1 + 2π ∑ S(1,1;c) J₁₁(4π/c)/c`).

`tau_isBigO_47_8_of_poincare_hyps`: these three imply `τ(n) = O(n^{47/8+ε})`.
-/
import RamanujanTau.TauBound.Main
import RamanujanTau.TauBound.Reduction

set_option autoImplicit false

namespace RamanujanTau.TauBound

open ModularForm UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups

/-- The `(c,d)` term of the Poincaré series (zero unless `gcd(c,d) = 1`). -/
noncomputable def poincareTerm (c : ℕ) (d : ℤ) (z : ℂ) : ℂ :=
  if Int.gcd c d = 1 then
    ((c : ℂ) * z + d) ^ (-12 : ℤ) *
      ee ((((d : ZMod c)⁻¹).val : ℂ) / c - 1 / ((c : ℂ) * ((c : ℂ) * z + d)))
  else 0

/-- The weight-12 Poincaré series `P₁(z)`. -/
noncomputable def poincare (z : ℂ) : ℂ :=
  ee z + ∑' c : ℕ, ∑' d : ℤ, poincareTerm (c + 1) d z

/-- `P₁` is a cusp form of weight 12 for `SL₂(ℤ)`. -/
def PoincareIsCuspForm : Prop := ∃ f : CuspForm 𝒮ℒ 12, ∀ z : ℍ, f z = poincare z

/-- The unfolding computation of the Fourier coefficients of `P₁`. -/
def PoincareUnfolding : Prop :=
  ∀ f : CuspForm 𝒮ℒ 12, (∀ z : ℍ, f z = poincare z) → HasPoincareCoeffs f

/-- Non-vanishing of the first coefficient of `P₁`. -/
def PoincareFirstCoeffNeZero : Prop :=
  1 + ∑' c : ℕ, ((c + 1 : ℕ) : ℂ) ^ (-12 : ℤ) * kloosterman 1 1 (c + 1) * kInt 1 (c + 1) 1 ≠ 0

theorem poincareFormula_of_hyps (hA : PoincareIsCuspForm) (hB : PoincareUnfolding)
    (hC : PoincareFirstCoeffNeZero) : PoincareFormula := by
  obtain ⟨f, hf⟩ := hA
  have hco := hB f hf
  refine poincareFormula_of_cuspForm f hco ?_
  have h1 := (hco 1 le_rfl).tsum_eq
  simp only [if_true, Nat.cast_one, div_one] at h1
  intro h0
  apply hC
  rw [h1, h0]; ring

/-- **Headline (conditional).** `τ(n) = O(n^{47/8+ε})` from the three Poincaré-series inputs;
the Kloosterman-sum input is proved. -/
theorem tau_isBigO_47_8_of_poincare_hyps (hA : PoincareIsCuspForm) (hB : PoincareUnfolding)
    (hC : PoincareFirstCoeffNeZero) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((47 / 8 : ℝ) + ε) :=
  tau_isBigO_47_8_of_poincare (poincareFormula_of_hyps hA hB hC) ε hε

end RamanujanTau.TauBound
