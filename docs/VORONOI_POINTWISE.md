# Pointwise truncated Voronoi for `Σ_{n≤x} τ(n)`, and which exponent it gives

Lean: `RamanujanTau/VoronoiPointwise/` (5 files, about 1020 lines). No `sorry`, no `native_decide`,
no new axiom. Build with `nice -n 10 lake build RamanujanTau.VoronoiPointwise.Main` (exit 0).
`#print axioms` on every headline gives `[propext, Classical.choice, Quot.sound]`.
The directory is not imported by `RamanujanTau.lean`.

Notation: `S(x) = Σ_{n≤x} τ(n)`, `α(n) = τ(n) n^{−11/2}`, and

`V_N(x) = x^{23/4}/(π√2) · Σ_{n≤N} τ(n) n^{−25/4} cos(4π√(nx) − π/4)`.

All exponents below are "normalized" when written as `S ≪ x^{11/2+η}`, i.e. we quote `η`.

## 1. Answer to the question

- **`35/6` needs Deligne** (or an input of the same strength) on every route of this kind: the
  pointwise truncated Voronoi formula, or Landau/Riesz differencing. Rankin–Selberg information
  (`Σ_{n≤x}|α(n)|² = cx + O(x^θ)`, `θ = 3/5` in the repo) together with Cauchy–Schwarz on short
  intervals gives exactly `η = 1/4 + θ/4`, so `η = 2/5` (`59/10`), and **not better**.
  Even the conjecturally optimal Rankin–Selberg error `θ = 3/8` would only give `η = 11/32 > 1/3`.
- **The best unconditional exponent from this route is `59/10`.** It equals the existing
  `TauPartialSumsSharp.tau_partial_sum_sharp`, so it is not beaten. A strictly better unconditional
  exponent needs an input that is not in the repository (§2.4).
- **Conditional on the repo's `[DeligneBound]`** (only `τ(p)² ≤ 4p^{11}` at primes), the classical
  pointwise formula with error `x^{6+ε}N^{−1/2}` (for `N ≤ x^{1/3}`) and `S(x) ≪ x^{35/6+ε}` are
  proved in Lean. The step from primes to all `n`, `|τ(n)| ≤ d(n)n^{11/2}`, is also proved.

## 2. On paper

### 2.1 The classical formula

For a level-one cusp form `f = Σ a(n)qⁿ` of weight `k`, `1 ≤ N ≪ x`:

```
S_f(x) = x^{(k−1)/2+1/4} / (π√2) · Σ_{n≤N} a(n) n^{−(k/2+1/4)} cos(4π√(nx) − π/4 − kπ/2·[k≡2 mod 4])
         + O(x^{(k−1)/2+1/2+ε} N^{−1/2}) + O(Σ_{|n−x|≤h} |a(n)|),   h ≍ √(x/N).
```

(For `k = 12`, `i^k = 1` and the phase is `−π/4`, as in `VoronoiTrunc`.)

Proof sketch (Perron). Use truncated Perron at height `T` and set `h = x/T`, `N = T²/(4π²x)`.

1. **Perron truncation error.** This is `Σ_n |a(n)|(x/n)^c min(1, x/(T|x−n|))`. Split it into the
   short interval `|n − x| ≤ h` and dyadic shells `|n − x| ≍ 2^j h`. A shell of length `ℓ`
   contributes `(h/ℓ) Σ_{shell}|a(n)|`.
2. **Moving the contour.** Use the functional equation and evaluate the dual integrals by
   stationary phase. Terms with `n ≤ N` have a stationary point inside `[−T, T]` and give the main
   term. The other terms give `O(x^{(k−1)/2+1/2}N^{−1/2}log x)`.

Step 2 uses only absolute mean values `Σ|α(n)|n^{−σ}`, so Rankin–Selberg is enough there. The
coefficient bound enters only through step 1: one needs

```
E(h; x) := Σ_{x<n≤x+h} |α(n)| ≪ h x^ε    pointwise in x, for h ≍ √(x/N),
```

together with the same bound on the dyadic shells. That is Deligne on average over intervals of
length `√(x/N)`, at every `x`.

### 2.2 Exponent calculus

Bound the main term trivially: `Σ_{n≤N}|α(n)|n^{−3/4} ≪ N^{1/4}` (Rankin–Selberg suffices). Then

```
S(x)/x^{11/2} ≪ x^{1/4}N^{1/4} + x^{1/2}N^{−1/2} + E(√(x/N)).                       (∗)
```

| input for `E(h)` | `E(√(x/N))` | optimal `N` | `η` | `S ≪ x^{…}` |
|---|---|---|---|---|
| Deligne, `E ≪ h x^ε` | `x^{1/2}N^{−1/2}` | `x^{1/3}` | `1/3` | `35/6` |
| Rankin–Selberg + Cauchy–Schwarz, `E ≪ h^{1/2}(h + x^θ)^{1/2}` | `(x/N)^{1/4}x^{θ/2}` | `x^θ` | `1/4 + θ/4` | `θ = 3/5`: **`59/10`** |
| Weil–Selberg `α(n) ≪ n^{1/4+ε}`, `E ≪ h x^{1/4}` | `x^{3/4}N^{−1/2}` | `x^{2/3}` | `5/12` | `71/12` |
| `min` of the last two | the Rankin–Selberg term is the smaller one at the optimum | | `2/5` | `59/10` |

- The Rankin row: balancing `x^{1/4}N^{1/4} = x^{1/4+θ/2}N^{−1/4}` gives `N = x^θ`. At the optimum
  `x^{1/2}N^{−1/2} = x^{1/2−θ/2}` is smaller than the other two terms because `θ > 1/3`.
- The same `η = 1/4 + θ/4` comes out of Landau differencing (`docs/TAU_PARTIAL_SUMS_SHARP.md` §3,
  `D(h) = x^{1/2}h^{−1/2}`, `h = x^{(1−θ)/2}`). The pointwise Voronoi formula and Riesz differencing
  are the same method seen from two sides. Correction to that doc: an improvement `θ = 3/5 − δ`
  gives `η = 2/5 − δ/4`, not `δ/3`.
- `η = 1/3` would need `θ ≤ 1/3`. The Rankin–Selberg error term is `Ω(x^{3/8})` (proved: `RankinOmega.rankinSelberg_error_omega`),
  the generic degree-4 mean-square lower bound. So no Rankin–Selberg error term, however sharp,
  reaches `1/3` through Cauchy–Schwarz. The best conceivable is `1/4 + 3/32 = 11/32`.
- Higher moments, as a remark. Suppose `Σ_{n≤x}|α(n)|^{2j} ≪ x^{1+ε}` (this needs `sym^j`
  information, not Rankin–Selberg). Hölder gives `E ≪ h^{1−1/(2j)}x^{1/(2j)+ε}`, and then
  `η = 1/(3 − 1/j)`. For `j = 2` this is again `2/5`, and `η → 1/3` only as `j → ∞`. Reaching
  `1/3` this way amounts to Ramanujan–Petersson.

### 2.3 Conclusion for (1)

- `S(x) ≪ x^{35/6+ε}` does **not** follow from Rankin–Selberg-type information by this route.
  It needs Deligne/Ramanujan–Petersson, or an equivalent pointwise short-interval bound
  `Σ_{x<n≤x+x^{1/3}}|α(n)| ≪ x^{1/3+ε}`.
- Without Deligne the route gives `59/10 = 5.9`, the same as the repo already has.
- Nothing in the repository beats it.

### 2.4 What would beat `59/10` unconditionally (not done)

- **A better Rankin–Selberg error.** Huang (2021, from memory) has `θ = 3/5 − 1/560`. Through
  (∗) this gives `η = 2/5 − 1/2240`, i.e. `59/10 − 1/2240`. It needs `GL(3)`/`sym²` subconvexity
  input that is not in the repository.
- **Cancellation in the head sum** `Σ_{n≤N} α(n)n^{−3/4}e(2√(nx))`. This takes exponential-sum or
  spectral methods. Not attempted.

## 3. Lean statements

```lean
namespace RamanujanTau.VoronoiPointwise   -- Main.lean

-- (1) unconditional, explicit short sum; any 0 < δ ≤ 23/4, 1 ≤ N ≤ x
theorem tau_voronoi_pointwise_short {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 23 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      |∑ n ∈ Icc 1 ⌊x⌋₊, (tau n : ℝ) - x^(23/4)/(π√2) * ∑ n ∈ Icc 1 N,
          (tau n : ℝ) * n^(-25/4) * cos (4π√(n x) - π/4)| ≤
        ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + 2√(x/N)⌋₊, |(tau n : ℝ)| + C * (x^(23/4) * N^(1/4 + δ))

-- (1) unconditional pointwise formula; 1 ≤ N ≤ x^{3/5}
theorem tau_voronoi_pointwise {ε} (hε : 0 < ε) : ∃ C ≥ 0, ∀ x ≥ 1, ∀ N : ℕ, 1 ≤ N → N ≤ x^(3/5) →
      |S(x) − V_N(x)| ≤ C * (x^(121/20 + ε) * N^(-1/4))

-- (1) unconditional partial-sum bound (exponent 59/10, = TauPartialSumsSharp)
theorem tau_partial_sum_pointwise {ε} (hε : 0 < ε) :
    ∃ C, ∀ x ≥ 1, |∑ n ∈ Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x^(59/10 + ε)

-- (2) [DeligneBound]
theorem abs_tau_le_rpow' [DeligneBound] {δ} (hδ : 0 < δ) :
    ∃ C ≥ 1, ∀ n : ℕ, |(tau n : ℝ)| ≤ C * n^(11/2 + δ)
theorem tau_voronoi_pointwise_deligne [DeligneBound] {ε} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ x ≥ 1, ∀ N : ℕ, 1 ≤ N → N ≤ x^(1/3) → |S(x) − V_N(x)| ≤ C * (x^(6 + ε) * N^(-1/2))
theorem tau_partial_sum_35_6 [DeligneBound] {ε} (hε : 0 < ε) :
    ∃ C, ∀ x ≥ 1, |∑ n ∈ Icc 1 ⌊x⌋₊, (tau n : ℝ)| ≤ C * x^(35/6 + ε)
```

(`S(x) − V_N(x)` abbreviates the explicit expression of the first theorem. The Lean statements
spell it out.)

Evidence levels:

- `tau_voronoi_pointwise_short`, `tau_voronoi_pointwise`, `tau_partial_sum_pointwise`,
  `pointwise_core`, `short_rankin`, `cheb_bound`, `card_divisors_le_rpow'`: **(1)**.
- `abs_tau_le_divisors`, `abs_tau_le_rpow'`, `tau_voronoi_pointwise_deligne`,
  `tau_partial_sum_35_6`: **(2)**, conditional on `[DeligneBound]` only.

## 4. Proof (Lean)

1. **Decomposition** (`Formula.lean`, `pointwise_core`). This reuses `VoronoiTrunc`: `dual_W`,
   `DkC_WC_eq`, `bracket_signed`, `kB_zero_sub_main` and `norm_kB_twelve_le`. Riesz order is 12
   and the smoothing is `h`. For `x ≥ 1`, `6h ≤ x` and any `N`:

   ```
   S − V_N = (S − S_h) + h^{−12} It_h^{12}(E_N) + h^{−12}(tail n > N) + (h^{−12} It_h^{12} V_N − V_N)
   ```

   It differs from the L² proof (`VoronoiTrunc.pointwise_bound`) in two ways:
   - The head is cut at `N` itself, so there is no mean-value block.
   - The tail `n > N` is killed by the 12-fold smoothing:
     `h^{−12}It^{12}k₀(n,·) = h^{−12}(2π)^{−12}Δ_h^{12}k₁₂ ≪ x^{23/4}n^{−25/4}·(√x/(h√n))^{12}`.

   The Rankin-trick exponents are kept free (`β = 13/2 + δ`), where `VoronoiTrunc` had hard-coded
   `53/8` and `27/4`. The bound is:

   ```
   |S − V_N| ≤ Σ_{x<n≤x+12h}|τ(n)| + C_K(3x)^{11/2}N^{δ}St_β
             + h^{−12}(C_T/π^{12})(3x)^{12}x^{−1/4}(N+1)^{δ−23/4}St_β
             + (6+2π)/(π√2) · N^{3/4+δ}St_β (3x)^{21/4}·12h.
   ```

2. **Tie `h` to `N`** (`Simple.lean`). Put `h = √(x/N)/6`, so the smoothing interval has length
   `12h = 2√(x/N)`. Then the tail term and the Lipschitz term are both `≍ x^{23/4}N^{1/4+δ}`, and
   so is the kernel error. This gives `tau_voronoi_pointwise_short`.
3. **Short sums** (`Corollaries.lean`).
   - Unconditional: `short_rankin`, which is `TauPartialSumsSharp.short_bound` (Cauchy–Schwarz)
     fed with `RankinExact.rankinSelberg_exact_general Δ` (`O(N^{3/5})`). It gives
     `E(2u) ≪ u^{1/2}x^{29/5}`, so `E(2√(x/N)) ≪ x^{121/20}N^{−1/4}`. This dominates the
     `x^{23/4}N^{1/4+δ}` term exactly when `N ≤ x^{3/5}`.
   - Deligne: `short_deligne` gives `E(H) ≪ (H+1)(x+H)^{11/2+δ}`, so
     `E(2√(x/N)) ≪ x^{6+δ}N^{−1/2}`. This dominates `x^{23/4}N^{1/4+δ}` exactly when `N ≤ x^{1/3}`.
4. **Partial sums.**
   - Unconditional: `N = ⌊x^{3/5}⌋` gives error `x^{121/20−3/20} = x^{59/10}`, and
     `|V_N| ≤ x^{23/4}N^{1/4+ε}St/(π√2) ≪ x^{59/10+ε}`.
   - Deligne: `N = ⌊x^{1/3}⌋` gives `x^{6−1/6} = x^{35/6}` for the error and
     `x^{23/4+1/12} = x^{35/6}` for the main term.
5. **From `DeligneBound` to all `n`** (`DeligneTau.lean`).
   - `cheb_bound`: the normalized `a_k = τ(p^k)/p^{11k/2}` satisfy `a_{k+2} = t a_{k+1} − a_k` with
     `t² ≤ 4` (by the Hecke recurrence `tau_hecke_recurrence`). Write
     `a_k = Σ_{j≤k} z^j w^{k−j}` with `z, w = t/2 ± i√(1−t²/4)`; then `|z| = |w| = 1`, so
     `|a_k| ≤ k+1`. There is no edge case at `t = ±2`.
   - Mordell multiplicativity (`tau_mul_coprime`) and `Nat.recOnPosPrimePosCoprime` give
     `|τ(n)| ≤ d(n)n^{11/2}`.
   - The divisor bound `d(n) ≤ C_δn^δ` (`card_divisors_le_rpow'`) is the standard prime-by-prime
     argument. It is re-proved here; the same proof exists in `SCSSharp2/Divisor.lean`, which is
     not imported.

## 5. Numerical checks (evidence level (4); `scripts/voronoi_pointwise/check.gp`)

The script uses `τ(n)` up to `3.2·10⁵`, from `η(q)^{24}`; it checks `τ(2) = −24` and
`τ(12) = −370944`. It uses `default(nbthreads,1)` and runs in 0.8 s.

`R = |S(x) − V_N(x)|/x^{11/2}`, compared with the classical (Deligne) error scale `x^{1/2}N^{−1/2}`:

| `x` | `N` | `R` | `R/(x^{1/2}N^{−1/2})` | `abs(V_N)/x^{11/2}` | `abs(S)/x^{11/2}` |
|---|---|---|---|---|---|
| 20000.3 | 1 | 1.548 | 0.0109 | 0.504 | 1.044 |
| 20000.3 | 27 (`x^{1/3}`) | 0.712 | 0.0262 | 0.332 | 1.044 |
| 20000.3 | 141 (`x^{1/2}`) | 0.260 | 0.0218 | 0.784 | 1.044 |
| 80000.7 | 43 | 0.261 | 0.0061 | 2.986 | 2.725 |
| 80000.7 | 282 | 0.509 | 0.0302 | 2.216 | 2.725 |
| 250000.1 | 1 | 3.226 | 0.0065 | 3.563 | 0.337 |
| 250000.1 | 62 | 0.305 | 0.0048 | 0.642 | 0.337 |
| 250000.1 | 500 | 0.184 | 0.0082 | 0.153 | 0.337 |

At `N = ⌊x^{1/3}⌋`, over 200 points in `[X, 2X]`:

| `X` | mean `R/(x^{1/2}N^{−1/2})` | max |
|---|---|---|
| 10⁴ | 0.0223 | 0.078 |
| 4·10⁴ | 0.0168 | 0.057 |
| 1.5·10⁵ | 0.0137 | 0.051 |

- The ratio is bounded, and even decreasing, consistent with `tau_voronoi_pointwise_deligne`. The
  constant is small because `x^{1/2}N^{−1/2}` is a worst-case short-sum scale.
- The script also checks the exponent arithmetic exactly:
  - `11/2 + 2/5 = 59/10` and `11/2 + 1/3 = 35/6`;
  - `121/20 − 3/20 = 59/10`;
  - `1/4 + θ/4` is `2/5` at `θ = 3/5` and `11/32 > 1/3` at `θ = 3/8`.

## 6. Files

| file | content |
|---|---|
| `DeligneTau.lean` | `csum`, `cheb_bound`, `abs_tau_prime_pow_le`, `abs_tau_le_divisors`, `card_divisors_le_rpow'`, `abs_tau_le_rpow` |
| `Formula.lean` | `norm_EM_le'`, `norm_tail_le'`, `abs_Vth_sub_le'` (free Rankin exponent), `Bpw`, `pointwise_core` |
| `Simple.lean` | rpow identities, `pointwise_simple` (`h = √(x/N)/6`), `abs_Vth_le` |
| `Corollaries.lean` | `short_rankin`, `short_deligne`, `voronoi_pointwise_uncond`, `voronoi_pointwise_deligne`, `partial_uncond`, `partial_deligne` |
| `Main.lean` | explicit-form headlines, `exponents`, `#print axioms` |

## 7. Gaps

- **Range of the Deligne formula.** The classical error `x^{6+ε}N^{−1/2}` is proved only for
  `N ≤ x^{1/3}`; the classical range is `N ≪ x`. The obstruction is the one-sided Riesz smoothing:
  - Over `[x, x + 2√(x/N)]` it changes the terms `n ≍ N` by `O(1)`.
  - The trivial bound for that change is `x^{23/4}N^{1/4}`, which is below `x^6N^{−1/2}` only when
    `N ≤ x^{1/3}`.
  - The full range needs either a sharp Perron cut-off with stationary-phase evaluation at finite
    height `T`, or cancellation in `Σ_{n≍N}`. Neither is done.
  - For the partial-sum exponent only `N = x^{1/3}` matters, so `35/6` is unaffected.
- **Unconditional formula.** The error `x^{121/20+ε}N^{−1/4}` is set by the Rankin–Selberg
  short sum. Compare it with the trivial size `x^{23/4}N^{1/4}` of `V_N`:
  - their ratio is `x^{3/10}N^{−1/2}`, so the error is at least the main term for every
    `N ≤ x^{3/5}`, with equality at `N = x^{3/5}`;
  - for `N > x^{3/5}` the `x^{23/4}N^{1/4+δ}` term of `tau_voronoi_pointwise_short` dominates
    instead.

  So, without Deligne, the pointwise formula is nowhere sharper than the trivial bound on its own
  main term. It is a genuine bound (`≪ x^{59/10}`, far below the trivial `x^{13/2}`), but it does
  not isolate `V_N`. This is the content of §2 seen from the formula side. The `L²` formula
  (`VoronoiTrunc`) is what isolates `V_N` unconditionally.
- **Only `τ`.** `VoronoiTruncGeneral` (`VData`) has the same lemmas for weight `2m`. The port of
  `pointwise_core` is mechanical (exponents `23/4 → m − 1/4` etc.) and was not done. For general
  forms the unconditional exponent `(k−1)/2 + 2/5` is already `TauPartialSumsSharp.cuspForm_partial_sum_sharp`.
- `+ε` in every exponent. It comes from Rankin's trick in the head sums (`N^δ`) and from `d(n) ≪ n^δ`.
- `S(x) ≪ x^{35/6}` without `ε` (with `d(n)` replaced by `log`) is not attempted.

## 8. Literature (from memory, not checked against sources)

- The truncated Voronoi formula with error `x^{1/2+ε}N^{−1/2}`, as in Ivić, *The Riemann
  zeta-function*, Ch. 3 (divisor problem). The cusp-form analogue uses Deligne for the
  short-interval term.
- Hafner–Ivić (1989): `S_f(x) ≪ x^{(k−1)/2+1/3}` and `Ω±`, using Deligne.
- Rankin (1939): `θ = 3/5`. Huang (2021): `θ = 3/5 − 1/560`. Degree-4 mean-square `Ω(x^{3/8})`
  for the Rankin–Selberg error.
- No novelty is claimed. The `59/10` unconditional exponent is natural for Landau's method with
  Rankin's mean value and is probably classical.
