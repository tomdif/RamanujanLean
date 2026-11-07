/-
# Wiener–Ikehara: discharge of `TauPNT.WienerIkeharaHyp`, and corollaries

* `wienerIkehara : TauPNT.WienerIkeharaHyp` — the Wiener–Ikehara Tauberian theorem (continuous
  boundary-extension form), from the ported proof `WienerIkeharaTheorem''` in
  `RamanujanTau/WienerIkehara/Wiener.lean` (port of PrimeNumberTheoremAnd, see docs/WIENER_IKEHARA.md).
* `tau_PNT_deligne`, `tau_PNT_tau_deligne` — the prime number theorem for `τ`, now conditional
  only on `[DeligneBound]`.
* `PNT_cumsum`, `PNT_psi` — the classical prime number theorem `ψ(x)/x → 1` (not in Mathlib),
  unconditional.
-/
import RamanujanTau.WienerIkehara.Wiener
import RamanujanTau.TauPNT.Main

set_option autoImplicit false

namespace RamanujanTau.WienerIkehara

open Filter Topology LSeries RamanujanTau.WI

/-- **Wiener–Ikehara Tauberian theorem.** If `f ≥ 0`, `∑ f(n)n^{-σ}` converges for `σ > 1`, and
`∑ f(n)n^{-s} − A/(s−1)` extends continuously to `Re s ≥ 1`, then `(∑_{n<N} f(n))/N → A`. -/
theorem wienerIkehara : RamanujanTau.TauPNT.WienerIkeharaHyp := by
  intro f A G hpos hsum hG hG'
  have hf : ∀ σ' : ℝ, 1 < σ' → Summable (nterm (fun n => (f n : ℂ)) σ') := by
    intro σ' hσ'
    have h := (hsum σ' hσ').norm
    refine h.congr fun n => ?_
    exact nterm_eq_norm_term.symm
  have := WienerIkeharaTheorem'' (f := f) (A := A) (G := G) (fun n => hpos n) hf hG hG'
  refine this.congr fun N => ?_
  rfl

section Deligne

variable [RamanujanTau.DeligneBound]

/-- **PNT for `τ`** (conditional only on Deligne): `∑_{p<N} τ(p)p^{−11/2} log p = o(N)`. -/
theorem tau_PNT_deligne :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime,
      RamanujanTau.EdgeNonvanishing.lam p * Real.log p) / N) atTop (𝓝 0) :=
  RamanujanTau.TauPNT.tau_PNT wienerIkehara

/-- **PNT for `τ`** (conditional only on Deligne): `∑_{p<N} τ(p) log p = o(N^{13/2})`. -/
theorem tau_PNT_tau_deligne :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, ((RamanujanTau.tau p : ℤ) : ℝ) *
      Real.log p) / (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0) :=
  RamanujanTau.TauPNT.tau_PNT_tau wienerIkehara

end Deligne

open ArithmeticFunction (vonMangoldt)

/-- **Prime number theorem** (discrete form): `(∑_{n<N} Λ(n))/N → 1`. Unconditional. -/
theorem PNT_cumsum :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, vonMangoldt n) / N) atTop (𝓝 1) := by
  have h := wienerIkehara (fun n => vonMangoldt n) 1 RamanujanTau.TauPNT.zetaAux
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
    (fun σ' hσ' => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ'))
    RamanujanTau.TauPNT.zetaAux_continuousOn ?_
  · exact h
  · intro s hs
    rw [RamanujanTau.TauPNT.zetaAux_eqOn hs]
    simp

/-- **Prime number theorem**: `ψ(x)/x → 1` as `x → ∞` (Chebyshev `ψ` from Mathlib). -/
theorem PNT_psi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have hfl : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h1 := PNT_cumsum.comp hfl
  have h2 : Tendsto (fun x : ℝ => ((⌊x⌋₊ + 1 : ℕ) : ℝ) / x) atTop (𝓝 1) := by
    have ha := tendsto_nat_floor_div_atTop (R := ℝ)
    have hb : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := ha.add hb
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    push_cast
    rw [add_div]
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp_apply]
  have hpos : (0 : ℝ) < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by positivity
  rw [Chebyshev.psi_eq_sum_Icc, ← Nat.range_succ_eq_Icc_zero, div_mul_div_cancel₀ hpos.ne']

end RamanujanTau.WienerIkehara
