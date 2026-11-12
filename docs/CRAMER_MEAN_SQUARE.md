# Cramér–Tong mean square of `∑_{n≤x} τ(n)` with the exact constant (Lean)

> **Current status (2026-11-12).** The Cramér limit and the L² truncated Voronoi formula are now proved in `VoronoiTrunc`; see [VORONOI_TRUNC](VORONOI_TRUNC.md). The missing convergence below describes the earlier logarithmic-mean method.

> **Update (2026-11-05):** the truncated Voronoi formula (L² form), the Cramér limit X^{−25/2}∫₁^X S² → B/(50π²) and exact Ω±(x^{23/4}) are proved in `VoronoiTrunc`; see [VORONOI_TRUNC](VORONOI_TRUNC.md).

Lean: `RamanujanTau/CramerMeanSquare/` (8 files, about 2000 lines). No `sorry`, no
`native_decide`, no new axiom, no named hypothesis. Build with
`nice -n 10 lake build RamanujanTau.CramerMeanSquare.Main` (exit 0). `#print axioms` on every
headline gives `[propext, Classical.choice, Quot.sound]`. **Evidence level (1).** Deligne is not
used. The public entry point is included in the `RamanujanTau.lean` import graph.

This closes gap (2) of `docs/VORONOI.md` ("exact Cramér constant") in its logarithmic form.

## 1. Statements

`S(x) = ∑_{1≤n≤x} τ(n)` (in Lean `∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)`),
`B = ∑_{n≥1} τ(n)² n^{−25/2} = 1.582807…`.

```lean
-- namespace RamanujanTau.CramerMeanSquare   (Main.lean)
theorem tau_cramer_log :
    Tendsto (fun X => (∫ x in 1..X, S x ^ 2 * x ^ (-(25/2))) / log X) atTop (𝓝 (B / (4 * π^2)))

theorem tau_cramer_mellin :
    Tendsto (fun δ => δ * ∫ x in Ioi 1, S x ^ 2 * x ^ (-(25/2) - 2*δ)) (𝓝[>] 0) (𝓝 (B / (8 * π^2)))

theorem tau_cramer_limsup {c} (hc : c < B / (50 * π^2)) :
    ∀ Y, ∃ X ≥ Y, c * X ^ (25/2) < ∫ x in 1..X, S x ^ 2
theorem tau_cramer_liminf {c} (hc : B / (50 * π^2) < c) :
    ∀ Y, ∃ X ≥ Y, ∫ x in 1..X, S x ^ 2 < c * X ^ (25/2)
theorem tau_cramer_constant {C}
    (h : Tendsto (fun X => (∫ x in 1..X, S x ^ 2) / X ^ (25/2)) atTop (𝓝 C)) :
    C = B / (50 * π^2)

theorem tau_mean_square_uniform : ∃ E, Tendsto E atTop (𝓝 0) ∧
    ∀ σ, 31/5 ≤ σ → σ ≤ 25/4 → ∀ T ≥ 1,
      |(∫ t in 0..T, ‖L(Δ, σ+it)‖^2) / T − ∑' n, τ(n)^2 n^(−2σ)| ≤ E T
```

In words:

- **`tau_cramer_log`** (the sharp statement): `∫₁^X S(x)² x^{−25/2} dx ~ (B/4π²) log X`.
- **`tau_cramer_mellin`**: the Mellin form, `δ Φ(δ) → B/(8π²)`, `Φ(δ) = ∫₁^∞ S² x^{−25/2−2δ}`.
  This sharpens `Voronoi.tau_critical_mean_square_mellin` (`Φ ≍ 1/δ`) to an asymptotic.
- **`tau_cramer_limsup/liminf`**: `liminf X^{−25/2}∫₁^X S² ≤ B/(50π²) ≤ limsup X^{−25/2}∫₁^X S²`.
- **`tau_cramer_constant`**: *if* `X^{−25/2}∫₁^X S²` converges, the limit is `B/(50π²)`.
- **`tau_mean_square_uniform`**: the Carlson–Potter mean value, uniform in `σ` on a compact
  interval. This is the new analytic input; `MeanSquareFull` has the limit only for fixed `σ`.

### What is *not* proved

The requested `tau_cramer : (∫₁^X S²)/X^{25/2} → B/(50π²)` is **not** proved. It does not
follow from the logarithmic asymptotic: `∫₁^X S² x^{−25/2} ~ A log X` is a Cesàro-type average
of `X^{−25/2}∫₁^X S²` (`J_identity` below). It says that this ratio is `B/(50π²)` on logarithmic
average, but not that the ratio converges. The convergence is the classical Cramér–Tong theorem
(Tong 1956), whose proof uses the truncated Voronoi formula with an `L²` remainder (gap (1) of
`docs/VORONOI.md`, still open). What is proved here is the sharp logarithmic form, the
liminf/limsup sandwich, and the identification of the constant: whatever proof of convergence is
added later, the constant is forced to be `B/(50π²)`.

## 2. Constants

- `Φ(δ) = (2π)⁻¹ ∫_ℝ Ψ_{23/4+δ}`, with `Ψ_σ(u) = |L(σ+iu)/(σ+iu)|²` (Voronoi, Plancherel).
- By the functional equation and Stirling, for `σ = 6−y` and `y = 1/4−δ`:
  `Ψ_σ(t) ≈ (2π)^{−4y} t^{4y−2} |L(6+y+it)|²`. Here `4y−2 = −1−4δ` and `6+y = 25/4−δ`.
- The uniform mean value `∫₀ᵀ |L(25/4−δ+it)|² ≈ RS(25/2−2δ)·T → B·T`, combined with Abel
  summation, gives `4δ ∫_{t₀}^∞ t^{−1−4δ}|L|² → B`.
- Hence `δΦ(δ) → (2π)⁻¹ · 2 · (2π)⁻¹ · B/4 = B/(8π²)`. The factor 2 comes from evenness.
- Laplace in `u = log x`: `Φ(δ) = ∫₀^∞ e^{−2δu} g(u) du`, with `g(u) du = S² x^{−25/2} dx`.
  Karamata with `ρ = 1` gives `∫₁^X S² x^{−25/2} ~ 2 · (B/8π²) · log X = (B/4π²) log X`.
- Summation by parts, `J(X) = X^{−25/2} I(X) + (25/2)∫₁^X x^{−27/2} I(x) dx`, shows that
  `I(X) ~ C X^{25/2}` forces `(25/2) C = B/(4π²)`, i.e. `C = B/(50π²)`.

## 3. Proof structure

| file | content |
|---|---|
| `Approx.lean` | `approx_tauL_unif`: `MeanSquare.approx_tauL` with the constant `C = K_c(3 + AJ/π)` chosen before `σ` (it depends only on the Perron shift and the convexity loss). The proof is copied, with the quantifier moved. |
| `Unif.lean` | `mean_square_unif`. Parameters fixed once for `σ ∈ [31/5, 25/4]`: shift `17/25`, `ε = 1/100`, length `X = T^{3/2}`. Approximation error `≤ 2C T^{−3/100}`; off-diagonal `≤ 9 RS(12.01)(1+log T) T^{183/200}`; diagonal `0 ≤ RS(2σ) − Σ|bₙ|² ≤ Σ τ²n^{−62/5}(1−φ(n/X)²) → 0`. None of these bounds depends on `σ`. |
| `Gamma.lean` | `R_unif`: `R(y,t) = Q(6−y,6+y,t)²(t/|6−y+it|)² → 1` uniformly in `y ∈ [0,1/4]`, via the explicit bounds `E_n⁻¹w^{−n} ≤ Q ≤ E_n w^{n+1}`. `Psi_eq`: the functional equation for `Ψ`. |
| `Abel.lean` | `abel_param`: suppose `|∫_a^T f_η − c_η T| ≤ εT + D` uniformly for small `η`, and `c_η → c₀`. Then `η∫_a^∞ t^{−1−η} f_η → c₀`. Proved by integration by parts and explicit power integrals. |
| `Limit.lean` | `delta_Phi_tendsto`. Split `∫_ℝ Ψ = ∫_{[−t₀,t₀]} + 2∫_{t₀}^∞`. The compact part is `O(1)` and is killed by `δ`. The tail is sandwiched by `(1±ε)`. |
| `Tauber.lean` | Logarithmic blocks `aₙ = ∫_{eⁿ}^{eⁿ⁺¹} S²x^{−25/2}`. `e^{−t}Σaₙe^{−nt} ≤ Φ(t/2) ≤ Σaₙe^{−nt}`. Then `EisensteinReal.karamata` with `ρ = 1`, and the floor-of-`log X` sandwich. |
| `Partial.lean` | `J_identity`: `I` has right derivative `S²` everywhere, because `S` is right-continuous; FTC is applied with right derivatives. Then `frequently_gt/lt` and `const_of_tendsto`. |
| `Main.lean` | headlines in explicit form, `#print axioms` |

Reused results:
- `Voronoi`: `integral_hR_eq`, `integral_Fs_sq`, `even_split`, `integrable_Psi`, `Psi`,
  `tau_mean_square_convergent`, `psiR`, `iI_psiR`, `intOn_S2`;
- `MeanSquare`: `perron_c`, `shift_identity`, `mv_poly`, `bsm`, `sum_tau_sq_rpow_le`,
  `tendsto_log_rpow_div`;
- `MeanSquareLeft`: `norm_tauL_fe`, `Qr`, `Qr_mul`, `Qr_succ`, `Qr_frac_bounds`;
- `HeckeConvex.tauL_convexity_strip`;
- `EisensteinReal.karamata`.

## 4. Numerical check (evidence level (4))

The check uses PARI `ramanujantau`, `n ≤ 2·10⁴`, with integrals computed exactly on the step
function. `B ≈ 1.582808`, `B/(4π²) = 0.040093` and `B/(50π²) = 0.0032074`.

| X | `X^{−25/2}∫₁^X S²` |
|---|---|
| 10³ | 0.0031065 |
| 5·10³ | 0.0031897 |
| 10⁴ | 0.0033193 |
| 2·10⁴ | 0.0032606 |

The ratio oscillates around `B/(50π²)`, which is consistent with `tau_cramer_constant` and the
liminf/limsup sandwich. The slope of `∫₁^X S²x^{−25/2}` against `log X` is `0.0401`
(`docs/VORONOI.md` §5).

## 5. Gaps

- **Existence of `lim X^{−25/2}∫₁^X S²`** (the Cramér–Tong theorem proper) is open here. It
  needs the truncated Voronoi formula with an `L²` remainder, or a dyadic `∫_X^{2X} S² ≍ X^{25/2}`
  together with some regularity.
- The uniform mean value is proved on `σ ∈ [31/5, 25/4]`, which is all that is needed. The same
  argument gives any compact subinterval of `(37/6, 13/2]`. Below `37/6` the fixed-`σ` bootstrap
  of `MeanSquareFull` would have to be made uniform as well.
- `τ` only. Generalizing to other level-one eigenforms requires `HeckeConvexGeneral` versions of
  `approx_tauL` and `norm_tauL_fe`.

## 6. Literature (from memory, not checked)

- H. Cramér (1922): the divisor-problem mean square.
- K.-C. Tong (1956): mean square of Voronoi-type error terms with the constant.
- A. Ivić (1990s): the Cramér–Tong constants for cusp-form coefficient sums.
- The Mellin–Landau–Karamata route via a uniform Carlson–Potter theorem, with no Voronoi formula
  and no Deligne, was not checked against the literature. No novelty claim is made.
