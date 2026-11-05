# Rankin–Selberg error `O(N^{1−δ})` for every `δ < 2/5` (Landau's method)

Lean: `RamanujanTau/RankinLandau/` (9 files, ~2300 lines). Build with
`nice -n 10 lake build RamanujanTau.RankinLandau.Main`.

## 1. Why the existing proof stops at `1/3`

`Stirling/Third.lean` (`rankinSelberg_power_saving_third`) works as follows. It takes the Riesz
mean of order `k = 2` and uses Perron on `Re s = 5/2`. It then shifts the contour to
`Re s = σ₁ > 0` (not to `−ε`), using the convexity bound
`F_b(s) ≪ |t|^{2+2ε−2σ}` on `σ₁ ≤ Re s ≤ 5/2` from `ConvexEps`. There is no dual sum. One
`k`-th difference (`riesz_kdiff`, loss `k+1`) gives `δ = (1−σ₁)/3`.

The general trade-off of this method, for a degree-`A` function (here `A = 4`), is
`δ = (1−σ)/(k+1)` subject to `A(1/2−σ)·… < k`. That gives `δ < (k+2)/(4(k+1))` for `σ < 0`
and `δ < 1/3` at `k = 2`, `σ → 0`, so `1/3` is the maximum of the method.

## 2. The argument used here (Landau 1915; Chandrasekharan–Narasimhan 1962)

Notation: `b = χ * a` (the `ζ(2s)` twist), `D_b(s) = ζ(2s)D_a(s)`, and `γₘ` is the gamma
factor. The functional equation is `Λ₀(s) = Λ₀(1−s)`.

1. **Exact dual expansion** (`DualA`, `DualB`, theorem `dual_rep`). For `k ≥ 18` and `x ≥ 1`:

       W_k(x) = Σ_{n≤x} bₙ (x−n)^k = κR_k(1) x^{k+1} − κR_k(0) x^k + Σₙ bₙ n^{−1−k} J_k(nx).

   The ingredients are:
   - Perron on `Re s = 5/2`;
   - the integrand written as `Φ = Ψ/(s(s−1))` with `Ψ` entire;
   - the holomorphic correction `H = Φ − Ψ(1)u₁ + Ψ(0)u₀`, where `u₁ = 1/(s−1) − 1/(s+2)` and
     `u₀ = 1/s − 1/(s+2)`, made holomorphic by two `dslope`s;
   - `‖H‖ ≪ (1+|t|)^{−2}` on `[−3/2, 5/2]`, from the existing Phragmén–Lindelöf bound
     `fPLM_bound` (exponent 19, hence `k ≥ 18`);
   - a contour shift to `Re s = −3/2`;
   - the residues, computed without a residue theorem: `∫(1/(α+it) − 1/(β+it))dt = π(sgn α − sgn β)`
     (`Residue.integral_inv_sub_line`, via arctan);
   - on the left line, the functional equation turns `Φ` into `x^s Q_k(s) Σ bₙ n^{s−1}`;
   - Fubini between the sum and the integral;
   - finally `J_k^{(−3/2)} = J_k^{(1/2)}`.
2. **Kernels** (`Kernel`, `KernelLine`).
   - Definitions: `Q_j(s) = R_j(s)γₘ(1−s)`, with `R_j = j! π^s(4π)^{s+m}/2 · Γ(s+j+1)⁻¹Γ(s+m)⁻¹`,
     and `J_j^{(σ)}(y) = (1/2π)∫ y^{σ+it+j}Q_j(σ+it)dt`.
   - Strip bound (`Qk_bound`): `‖Q_j(s)‖ ≪ (1+|t|)^{1−4A₀−j}` on `A₀ ≤ Re s ≤ 1/2`. It comes
     from a new uniform Γ-ratio bound (`GammaUnif`) built on `Stirling.GammaRatio`, and it works
     for arbitrarily negative `A₀`.
   - Derived results: contour shift (`Jc_shift`), the **phase-free** bound
     `‖J_j^{(σ)}(y)‖ ≪ y^{σ+j}` for any `σ > (2−j)/4` (`norm_Jc_le`), the relation
     `J_{j+1}(u+v) − J_{j+1}(u) = (j+1)∫₀^v J_j(u+w)dw` (`Jc_rel`, Fubini), and continuity.
3. **Landau differencing** (`Core`, `landau_core`, pure real analysis).
   - The bracket `k!h^k B(x) ≤ Δ_h^k W_k(x) ≤ k!h^k B(x+kh)` comes from `RankinError.bracket`.
   - Terms with `n ≤ M`: `k−1` integrations reduce to `J₁`, giving
     `|Δ^k J_k(n·)| ≤ 2k!h^{k−1}n^{k−1} sup|J₁|`.
   - Terms with `n > M`: `|Δ^k f| ≤ 2^k sup|f|`.
   - Rankin's trick (`n^{α−1} ≤ M^{α+ε}n^{−1−ε}`) replaces partial summation.
   - Parameter choice: `h = X^θ/(4k)` and `M = X^μ`.
   - Result: `B(X) = cX + O(X^θ)` whenever `1+α+μ(α+ε) ≤ 2θ` and `k+σ+μ(σ+ε) ≤ (k+1)θ`.
4. **Exponents** (`exponents_ok`).
   - Inputs: `J₁ ≪ y^{1+α}` with `α = 1/8+η` (the hypothesis), and `J_k ≪ y^{k+σ}` with
     `σ = (2−k)/4 + ξ` (proved, phase-free).
   - Admissible range: `θ = 1−δ` works iff `δ < (2k−3)/(5k−7)`, which tends to `2/5`.
     Explicit choice: `ξ = (2−5δ)/32` and `k ≥ max(18, 10/(2−5δ))`.
   - With a phase-free `J₁ ≪ y^{5/4+η}` the same bookkeeping gives only `δ < 1/3`. Only the
     *bottom* kernel needs the phase; the top kernel `J_k` is fine without it.
5. **Möbius** (`mobius_transfer`, reused) moves the result from `b` back to `a`. Cusp-form and `τ`
   wrappers are as in `Stirling/Third`.

## 3. The named hypothesis

```lean
def KernelOneBound (m : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Jc m 1 (1 / 2) y‖ ≤ C * y ^ ((9 : ℝ) / 8 + η)
```

Here `Jc m 1 (1/2) y = (1/2π)∫ y^{3/2+it} Q₁(1/2+it) dt` and
`Q₁(s) = π^{2s−1}(4π)^{2s−1}Γ(1−s)Γ(1−s+m)/(Γ(s+2)Γ(s+m))`. The integral converges absolutely,
since `|Q₁| ≍ |t|^{−2}`.

- **What it is.** A bound for an explicit Γ-integral, not involving the coefficients at all.
  It is the classical stationary-phase / Meijer-G asymptotic (Chandrasekharan–Narasimhan 1962,
  §§4–6): saddle at `|t| ≍ y^{1/4}`, size `y^{1/8}·y`.
- **Why it is not proved.** It needs the phase of Γ, i.e. Stirling for `Im log Γ` together with
  a second-derivative / stationary-phase test. Neither is in Mathlib or in the repo; the repo's
  Stirling is modulus-only.
- **Why it is needed.** The phase-free bound `norm_Jc_le` gives `y^{5/4+η}`, and this provably
  caps the method at `δ < 1/3` (§2.4).
- **Numerical evidence** (`m = 11`, scipy, trapezoid rule on `|t| ≤ max(2000, 50√y)`): for
  `y = 1, 10, …, 10⁶`, `|J₁(y)|/y^{9/8}` stays in `[0.010, 0.083]`, while `|J₁|/y^{5/4}` decays
  like `y^{−1/8}`.

## 4. Evidence levels

| statement | level |
|---|---|
| `landau_core`, `Dk_family_bound`, `Dk_W_bound` | (1) Lean, axiom-clean |
| `norm_Gamma_ratio_unif'`, `inv_Gamma_eq_prod`, `Qk_bound` | (1) |
| `norm_Jc_le`, `Jc_shift`, `Jc_rel`, `continuousOn_Jc` | (1) |
| `integral_inv_sub_line`, `H_bound`, `Phi_eq_left/right` | (1) |
| `dual_rep` (exact Voronoi-type formula for the Riesz mean) | (1) |
| `exponents_ok` | (1) |
| `landau_of_RSDataM`, `landau_RSFn`, `rankinSelberg_landau_general`, `rankinSelberg_landau`, `rankinSelberg_landau_61_100` | (2) conditional on `KernelOneBound m` (an argument; `#print axioms` = propext, Classical.choice, Quot.sound) |
| `KernelOneBound m` itself | (3) literature + (4) numerics |

## 5. What remains

- **To remove the hypothesis.** Prove `KernelOneBound`. Estimate: 800–1500 lines, in three
  steps:
  1. complex Stirling with error, `log Γ(s) = (s−½)log s − s + ½log 2π + O(1/|s|)`, uniformly
     in a strip, together with its derivative (digamma `= log s + O(1/|s|)`);
  2. a van der Corput second-derivative bound for `∫ e^{iφ(t)}g(t)dt`;
  3. splitting at `|t| ≍ y^{1/4}`.
- **To reach `δ = 2/5` exactly** (not just every `δ < 2/5`). This needs the sharp
  `J₁ ≪ y^{9/8}` (no `η`) and `J_k ≪ y^{k+(2−k)/4}·…` with the phase as well, i.e. the full
  C–N kernel lemma.
