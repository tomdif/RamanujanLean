# Deligne-free results: edge non-vanishing of `L(Δ×Δ, s)` and sign changes of `τ(p)`

Lean: `RamanujanTau/TauPNTUncond/` (7 files, about 1750 lines). There is no `sorry`, no new axiom
and no `native_decide`, and there are no named hypotheses. Build with
`nice -n 10 lake build RamanujanTau.TauPNTUncond.Main` (exits 0). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all 19 headlines (evidence level 1).

The public entry point is included in the `RamanujanTau.lean` import graph.

Notation (normalized): `λ(p) = τ(p)p^{−11/2}`, `R(s) = ∑ τ(n)² n^{−11−s}`,
`L(s) = L(Δ, s + 11/2)`, Satake parameters `α_p, β_p`, `A_k(p) = α_p^k + β_p^k`.

## Headline results

| statement | Lean | evidence |
|---|---|---|
| `exp ∑ cR(n) n^{−s} = ζ(2s)R(s)` on `Re s > 1`, `cR(p^k) = A_k(p)²/k ≥ 0` | `exp_LSeries_cR` | (1) |
| `‖H(σ)³H(σ+it)⁴H(σ+2it)‖ ≥ 1` for `σ > 1`, `H = ζ(2s)R(s)` | `one_le_norm_comb` | (1) |
| **`ζ(2s)R(s) ≠ 0` at `s = 1+it`, `t ≠ 0`** (continued) | `HH_ne_zero_edge` | (1) |
| **`R(1+it) ≠ 0`, i.e. `L(Δ×Δ, 1+it) ≠ 0`, `t ≠ 0`** | `Rcont_ne_zero_edge` | (1) |
| **`L(Sym²Δ, 1+it) ≠ 0`, `t ≠ 0`; `L(Sym²Δ, s) → KK(1) ≠ 0` as `s → 1`** | `Lsym2_ne_zero_edge`, `Lsym2_tendsto_one` | (1) |
| `(s−1)ζ(2s)R(s)` has no zero on `Re s ≥ 1` | `KK_ne_zero` | (1) |
| `−KK'/KK` is continuous on `Re s ≥ 1` and equals `∑ Λ_{Δ×Δ}(n)n^{−s} − 1/(s−1)` | `continuousOn_negLogDerivK`, `negLogDerivK_eq` | (1) |
| Landau's theorem for log-derivatives (general, see below) | `landau_abscissa` | (1) |
| `\|A_k(p)\| ≤ 2C p^{11k/40}` uniformly (Weil exponent) | `weil_AA` | (1) |
| **`∑_p λ(p)²/p = ∞`** | `not_summable_lam_sq` | (1) |
| prime powers of `Λ_Δ` converge absolutely at `s = 5/8` | `summable_vH_58` | (1) |
| **`τ(p) > 0` for infinitely many primes, and `τ(p) < 0` for infinitely many** | `tau_prime_sign_changes_uncond` | (1) |
| **`∑_{n<N} Λ_{Δ×Δ}(n) ~ N`** (Rankin–Selberg PNT) | `rs_PNT` | (1) |
| **`∑_{p<N} λ(p)² log p ~ N`** | `rs_prime_PNT` | (1) |
| `∑_{p<N} log p ~ N` | `theta_PNT` | (1) |
| **`∑_{p<N} λ(p²) log p = o(N)`** (PNT for `Sym²`) | `sym2_prime_PNT` | (1) |

Here `Λ_{Δ×Δ}(p^k) = A_k(p)² log p` (`vR`) is the von Mangoldt function of `ζ(2s)R(s)`.

```lean
theorem HH_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : HH (1 + (t : ℂ) * I) ≠ 0
--   HH s = RStar s * invGam s   (= ζ(2s) R(s) on Re s > 1)
theorem Rcont_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : Rcont (1 + (t : ℂ) * I) ≠ 0
theorem Lsym2_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : Lsym2 (1 + (t : ℂ) * I) ≠ 0
--   Lsym2 s = HH s / riemannZeta s
theorem tau_prime_sign_changes_uncond :
    (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ 0 < tau p) ∧ (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ tau p < 0)
theorem rs_prime_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, lam p ^ 2 * Real.log p) / N)
      atTop (𝓝 1)
theorem sym2_prime_PNT :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, uu p 2 * Real.log p) / N)
      atTop (𝓝 0)
```

## Proofs

### 1. `log ζ(2s)R(s)` without Deligne (`RSLog.lean`)

- By `rs_local`, the local factor is `((1−Y)²(1−α²Y)(1−β²Y))⁻¹` with `Y = p^{−s}`.
  `list_log` applied to `[Y, Y, α²Y, β²Y]` gives the logarithm `∑_k A_k²Y^k/k`, because
  `2 + α^{2k} + β^{2k} = A_k²`.
- Absolute convergence on `Re s > 1`:
  - `k = 1` is Rankin: `∑_p λ²p^{−σ} < ∞`.
  - `k ≥ 2`: put `x = ‖α‖²p^{−σ} ≤ 2^{1−σ}`. Then `x² ≤ (2λ²+2)p^{1−2σ}`, using `‖α‖² ≤ p` and
    `‖α‖² ≤ 2λ²+2`. This makes the sum geometric in `k`, and the sum over `p` is Rankin's at
    `2σ−1 > 1`.

### 2. Edge non-vanishing: the 3–4–1 argument (`Edge.lean`)

- `HH = R*/γ` is holomorphic on `ℂ ∖ {0,1}`. It uses the completed `R*` from `RankinSelbergFE`.
- `KK(s) = ((s−1)R*₀(s) − ‖Δ‖²(s−1)/s + ‖Δ‖²)/γ(s)` is holomorphic for `s ≠ 0`. It equals
  `(s−1)HH(s)` for `s ≠ 0, 1`, and `KK(1) = ‖Δ‖²γ(1)⁻¹ ≠ 0`.
- Positivity: since `cR ≥ 0` and `Re(3 + 4w + w²) = 2(1 + Re w)² ≥ 0` for `|w| = 1`, the bound
  `‖HH(σ)³HH(σ+it)⁴HH(σ+2it)‖ = exp(Re …) ≥ 1` holds.
- Suppose `HH(1+it) = 0`. Then `HH(σ+it) = O(σ−1)`. Also `HH(σ) = KK(σ)/(σ−1) = O(1/(σ−1))`, and
  `HH(σ+2it) = O(1)` because `1+2it ∉ {0,1}`. So the product is `O(σ−1) → 0`, a contradiction.
- No zero of `ζ(2s)` can create a pole here, since `HH` is built from `R*` directly.
- Corollaries:
  - `R(1+it) = HH/ζ(2+2it) ≠ 0`.
  - `L(Sym²Δ, s) := HH(s)/ζ(s)` is nonzero at `1+it`, using `ζ(1+it) ≠ 0` from Mathlib. Its
    limit at `s = 1` is `KK(1) ≠ 0`.

### 3. Landau's theorem (`Landau.lean`, general)

`landau_abscissa` makes the following assumptions:

- `a ≥ 0`, and the abscissa of `b` is at most `θ`;
- `L` is entire, with `L(σ) ≠ 0` for real `σ ∈ (θ, 1]`;
- `ε² = 1`;
- `ε(−L'/L) = ∑ a n^{−s} + ∑ b n^{−s}` on `Re s > 1`.

The conclusion is that the abscissa of `∑ a n^{−s}` is at most `θ`.

Proof:

1. Suppose not, and let `x₀` be the abscissa. Then `L' + εWL = 0` on `Re s > x₀`, by the identity
   theorem.
2. Since `L(x₀) ≠ 0`, the function `−εL'/L − ∑b` is a holomorphic extension of `∑a` to a ball
   `B(x₀, r)`.
3. Take the Taylor expansion at `c = x₀ + r/4` (Mathlib's `Complex.hasSum_taylorSeries_on_ball`)
   and evaluate it at `x₀ − r/4`. By `LSeries_iteratedDeriv`, every term of the double series
   `∑_k ∑_n (r/2)^k (log n)^k a(n) n^{−c}/k!` is nonnegative.
4. Tonelli (`summable_prod_of_nonneg`) then gives `∑_n a(n) n^{−(x₀ − r/4)} < ∞`, which
   contradicts the choice of `x₀`.

### 4. Sign changes (`Weil.lean`, `Signs.lean`)

- **Weil at prime powers.** From `StepanovAS.tau_isBigO_23_4_unconditional` with `ε = 1/40`, we
  get `|λ(p^k)| ≤ Cp^{11k/40}`. The Hecke relation gives `A_{k+2} = λ(p^{k+2}) − λ(p^k)`
  (`AA_add_two`).
- **`∑_p λ(p)²/p = ∞`.** For `σ > 1`, `‖ζ(2σ)R(σ)‖ = exp ∑ cR(n)n^{−σ}`. If `∑λ²/p < ∞`, this
  stays bounded. The `k = 2` terms are bounded by `A_2² ≤ 2λ⁴+8 ≤ 8C²p^{11/20}λ²+8` together with
  Rankin at `29/20`. The terms with `k ≥ 3` are bounded by `A_k² ≤ 4C²p^{11k/20}`. On the other
  hand, `ζ(2σ)R(σ) = KK(σ)/(σ−1) → ∞`.
- **No eventual sign.** Suppose `ελ(p) ≥ 0` for all `p ≥ P`. Write `εΛ_Δ = a + b`, where:
  - `a(p) = |λ(p)| log p` for `p ≥ P`;
  - `b` consists of the primes `p < P` and the prime powers.

  `b` converges at `5/8`: for `k = 2` use Rankin at `49/40`; for `k ≥ 3` use Weil, which gives
  `p^{−41/40}` geometrically. `L(σ) > 0` for real `σ` by `HeckeL.tauL_pos`, since `Δ(iy) > 0`. So
  Landau gives `∑_{p≥P} |λ(p)| log p · p^{−29/40} < ∞`.
- With Weil, `λ²/p ≤ C|λ|p^{−29/40}`. Hence `∑λ²/p < ∞`, a contradiction.

The positivity `L(σ) > 0` on the whole real axis is what makes both signs work. With `ε = −1`, a
real zero of `L` would otherwise be a singularity with positive residue that Landau's argument
cannot exclude. The Weil exponent is also essential, not just a convenience: the argument needs
`|λ(p)| ≪ p^{θ}` with `θ < 1 − 5/8 = 3/8`. Hecke's trivial bound `θ = 1/2` would not suffice.
Kloosterman's `47/8`, i.e. `θ = 3/8 + ε`, is borderline. The repo's Weil bound gives
`θ = 11/40`.

### 5. Rankin–Selberg PNT (`RSPNT.lean`)

- `rs_PNT` applies `WienerIkehara.wienerIkehara` to `vR ≥ 0` with `A = 1` and
  `G = −KK'/KK`. This is where the edge non-vanishing (step 2) is used.
- The prime powers satisfy `∑_{k≥2} vR(p^k)/p^k < ∞`, by Rankin and Weil as in step 4 with an
  extra `log p ≤ 40p^{1/40}`. By Kronecker (`cesaro_zero_of_summable_div`, via Tannery's
  dominated convergence) they contribute `o(N)`. This gives `rs_prime_PNT`.
- `theta_PNT` follows from `PNT_cumsum` in the same way.
- `sym2_prime_PNT` is the difference of the two, using `λ(p²) = λ(p)² − 1`.

## Relation to other work in the repo

- `TauPNT/Signs.lean` (`tau_prime_sign_changes`, which assumes `[DeligneBound]`) is superseded by
  `tau_prime_sign_changes_uncond`.
- The Deligne-free PNT `∑_{p<N} τ(p) log p = o(N^{13/2})` was proved independently, with an error
  term, in `TauPNTError/Uncond.lean` (`tau_PNT_tau_error_uncond`). It is not duplicated here.
  `rs_PNT` and the edge results above give the second ingredient of the classical Wiener–Ikehara
  route: the `(1 ± A_k)²` majorant, whose `G` is now known to be continuous.
- `TauSigns/` proves sign changes of `τ(n)` over all `n`. The prime-only statement here is new
  to the repo.

## Gaps and remarks

- Sign changes over primes are qualitative: there is no count of sign changes up to `x`. A
  quantitative version would need the error-term PNT for `λ²` (the Sym² zero-free region), or the
  Sato–Tate-type moments `Sym³` and `Sym⁴`, which are not available.
- The positive proportion of primes with each sign is out of reach. It needs Sato–Tate (Barnet-Lamb–Geraghty–Harris–Taylor).
- `rs_prime_PNT` and `sym2_prime_PNT` have no error term.
- The argument in step 4 deliberately uses only second moments plus Landau. A pure moment
  argument (first and second moments plus pointwise Weil) cannot rule out `λ(p) ≥ 0` eventually,
  because a sparse set of large values is consistent with all of those facts. Landau's theorem,
  applied to the analytic continuation of `L'/L` past `Re s = 1`, is what gives the strong
  average bound `∑_{p≤x}|λ(p)| ≪ x^{5/8+ε}`, which then contradicts `∑_p λ(p)²/p = ∞`.

## Literature

- Rankin (1939) and Selberg (1940), Rankin–Selberg theory.
- Landau (1905), singularities of Dirichlet series with nonnegative coefficients.
- Shimura (1975) and Gelbart–Jacquet (1978), `L(Sym², s)`.
- Ogg, *Modular forms and Dirichlet series* (1969).
- Moreno (1972/74), prime number theorems for modular forms.
- Ram Murty (1983), oscillations of Fourier coefficients.
- Weil (1948), Kloosterman sums.
