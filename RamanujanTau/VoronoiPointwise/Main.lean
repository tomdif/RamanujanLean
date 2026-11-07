/-
# `VoronoiPointwise/`: the pointwise truncated Voronoi formula for `Σ_{n≤x} τ(n)`

Build: `nice -n 10 lake build RamanujanTau.VoronoiPointwise.Main`.  See `docs/VORONOI_POINTWISE.md`.

`S(x) = Σ_{n≤x} τ(n)`,  `V_N(x) = x^{23/4}/(π√2) Σ_{n≤N} τ(n) n^{−25/4} cos(4π√(nx) − π/4)`.

Headlines.

* Evidence level (1), unconditional (no Deligne):
  - `tau_voronoi_pointwise_short`: `|S − V_N| ≤ Σ_{x<n≤x+2√(x/N)}|τ(n)| + C x^{23/4} N^{1/4+δ}`
    for `1 ≤ N ≤ x` (any `0 < δ ≤ 23/4`);
  - `tau_voronoi_pointwise`: `|S − V_N| ≤ C x^{121/20+ε} N^{−1/4}` for `1 ≤ N ≤ x^{3/5}`;
  - `tau_partial_sum_pointwise`: `|S(x)| ≤ C x^{59/10+ε}` (same exponent as
    `TauPartialSumsSharp.tau_partial_sum_sharp`; `59/10` is the optimum of every
    Landau/Voronoi route fed only with Rankin–Selberg short sums, see the doc §2).
* Evidence level (2), conditional on the repo's `[DeligneBound]` (`τ(p)² ≤ 4p^{11}` at primes):
  - `abs_tau_le_rpow'`: `|τ(n)| ≤ C_δ n^{11/2+δ}` (Chebyshev + Hecke + Mordell + divisor bound);
  - `tau_voronoi_pointwise_deligne`: classical `|S − V_N| ≤ C x^{6+ε} N^{−1/2}` for `1 ≤ N ≤ x^{1/3}`;
  - `tau_partial_sum_35_6`: `|S(x)| ≤ C x^{35/6+ε}` (Hafner–Ivić exponent).
-/
import RamanujanTau.VoronoiPointwise.Corollaries
import RamanujanTau.VoronoiTrunc.Main

set_option autoImplicit false

namespace RamanujanTau.VoronoiPointwise

open Real
open RamanujanTau.VoronoiTrunc

/-- **Pointwise truncated Voronoi with the short sum explicit** (unconditional). -/
theorem tau_voronoi_pointwise_short {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 23 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 N,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)| ≤
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 2 * √(x / N)⌋₊, |(tau n : ℝ)| +
          C * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ)) := by
  obtain ⟨C, hC0, hC⟩ := pointwise_simple hδ hδ'
  refine ⟨C, hC0, fun x hx N hN hNx => ?_⟩
  have := hC x hx N hN hNx
  rwa [Vth_eq_explicit, Sre_eq] at this

/-- **Pointwise truncated Voronoi, unconditional**: `|S − V_N| ≤ C x^{121/20+ε} N^{−1/4}`
for `1 ≤ N ≤ x^{3/5}`. -/
theorem tau_voronoi_pointwise {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x ^ ((3 : ℝ) / 5) →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 N,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)| ≤
        C * (x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := voronoi_pointwise_uncond hε
  refine ⟨C, hC0, fun x hx N hN hNx => ?_⟩
  have := hC x hx N hN hNx
  rwa [Vth_eq_explicit, Sre_eq] at this

/-- **Partial sums from the pointwise formula** (unconditional): `|S(x)| ≤ C x^{59/10+ε}`. -/
theorem tau_partial_sum_pointwise {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((59 : ℝ) / 10 + ε) :=
  partial_uncond hε

/-- `|τ(n)| ≤ C_δ n^{11/2+δ}` from `DeligneBound` at primes. -/
theorem abs_tau_le_rpow' [DeligneBound] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, |(tau n : ℝ)| ≤ C * (n : ℝ) ^ (11 / 2 + δ) :=
  abs_tau_le_rpow hδ

/-- **Classical pointwise truncated Voronoi** (`[DeligneBound]`): `|S − V_N| ≤ C x^{6+ε} N^{−1/2}`
for `1 ≤ N ≤ x^{1/3}`. -/
theorem tau_voronoi_pointwise_deligne [DeligneBound] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x ^ ((1 : ℝ) / 3) →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 N,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)| ≤
        C * (x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := voronoi_pointwise_deligne hε
  refine ⟨C, hC0, fun x hx N hN hNx => ?_⟩
  have := hC x hx N hN hNx
  rwa [Vth_eq_explicit, Sre_eq] at this

/-- **`S(x) ≪ x^{35/6+ε}`** (`[DeligneBound]`). -/
theorem tau_partial_sum_35_6 [DeligneBound] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x ^ ((35 : ℝ) / 6 + ε) :=
  partial_deligne hε

lemma exponents : (35 : ℝ) / 6 < 59 / 10 ∧ (59 : ℝ) / 10 = 11 / 2 + 2 / 5 ∧
    (35 : ℝ) / 6 = 11 / 2 + 1 / 3 ∧ (121 : ℝ) / 20 - 3 / 5 * (1 / 4) = 59 / 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

end RamanujanTau.VoronoiPointwise

#print axioms RamanujanTau.VoronoiPointwise.tau_voronoi_pointwise_short
#print axioms RamanujanTau.VoronoiPointwise.tau_voronoi_pointwise
#print axioms RamanujanTau.VoronoiPointwise.tau_partial_sum_pointwise
#print axioms RamanujanTau.VoronoiPointwise.abs_tau_le_rpow'
#print axioms RamanujanTau.VoronoiPointwise.tau_voronoi_pointwise_deligne
#print axioms RamanujanTau.VoronoiPointwise.tau_partial_sum_35_6
#print axioms RamanujanTau.VoronoiPointwise.pointwise_core
#print axioms RamanujanTau.VoronoiPointwise.cheb_bound
#print axioms RamanujanTau.VoronoiPointwise.abs_tau_le_divisors
#print axioms RamanujanTau.VoronoiPointwise.short_rankin
