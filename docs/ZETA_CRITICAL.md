# Hardy–Littlewood (1918): the mean square of ζ on the critical line

Lean: `RamanujanTau/ZetaCritical/` (5 files, about 820 lines). Build with
`nice -n 10 lake build RamanujanTau.ZetaCritical.Main`, which exits 0. There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. `#print axioms` on every headline gives
`[propext, Classical.choice, Quot.sound]`. The public entry point is included in the `RamanujanTau.lean` import graph.

## 1. Statements (namespace `RamanujanTau.ZetaCritical`)

| result | evidence level |
|---|---|
| `zeta_critical_mean_square`: `∫₀ᵀ |ζ(1/2+it)|² dt ~ T log T` | **(1)**, Lean, axiom-clean |
| `zeta_critical_mean_square_bound`: the error is `O(T √log T)` | **(1)** |
| `Iz_eps`: the bound `2ε T log T + K T/ε` for any `0 < ε ≤ 1` | **(1)** |
| Ingham: `T log(T/2π) + (2γ−1)T + O(T^{1/2+ε})` | **not formalized**; checked numerically only, level (4) |

```lean
theorem zeta_critical_mean_square :
    Tendsto (fun T : ℝ => (∫ t in (0:ℝ)..T, ‖riemannZeta (1/2 + t * I)‖ ^ 2) /
      (T * Real.log T)) atTop (𝓝 1)

theorem zeta_critical_mean_square_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T →
    |(∫ t in (0:ℝ)..T, ‖riemannZeta (1/2 + t * I)‖ ^ 2) - T * Real.log T| ≤
      C * (T * Real.sqrt (Real.log T))

-- Iz T = ∫ t in 1..T, ‖ζ(1/2 − it)‖²,  CE = 4 + 16π
theorem Iz_eps (ε T : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hT : 2 ≤ T) :
    |Iz T - T * Real.log T| ≤ 2 * ε * (T * Real.log T) + (729 + 3 * CE) * T / ε
theorem Iz_sqrt (T : ℝ) (hT : 3 ≤ T) :
    |Iz T - T * Real.log T| ≤ (731 + 3 * CE) * (T * Real.sqrt (Real.log T))
```

Reusable byproducts, all level (1):

| theorem | statement |
|---|---|
| `avg_mv` | for real `c`, `G(u) = ∫₀ᵘ|∑_{n≤N} cₙ n^{-it}|²`: `|∫_a^b G − (b²−a²)/2·∑cₙ²| ≤ ∑_{m≠n} |c_m c_n|·2/(log n − log m)²` |
| `offdiag_ch_le` | for `cₙ = n^{−1/2}`, that off-diagonal sum is at most `20N²` (there is no log factor) |
| `sum_ch_le` | `∑_{n≤N} n^{−1/2} ≤ 2√N` |
| `sum_inv_dist_sq_le` | `∑_{n≤N, n≠m} 1/(n−m)² ≤ 4` |
| `normSq_dpoly_real` | `|P(t)|² = ∑_{m,n} c_m c_n cos((log n − log m)t)` |

## 2. Proof

**Why σ = 1/2 needs more than `ZetaMeanSquare`.** Two of the ingredients there still work at
σ = 1/2. `err_L2` is stated for `1/2 ≤ σ`, and it gives `∫₁^V|ζ(1/2−it) − P_{⌈V⌉}|² ≤ (4+16π)V`.
`riemannZeta_conj` also works. The polynomial mean value `MeanSquare.mv_poly` is the problem.
Its error `6 H_N ∑ n|bₙ|² = 6 H_N · N` is about `6 T log T`, which is larger than the main term.
Bounding each off-diagonal term `sin(Tθ)/θ` trivially also gives about `N log N`. So some
cancellation is needed. One way is the full Montgomery–Vaughan Hilbert inequality. The other is
the approximate functional equation.

**This proof uses neither.** It uses a monotone averaging sandwich.

1. `I(u) = ∫₁ᵘ|ζ|²` is nondecreasing in `u`. So `I(T) ≤ I(u)` for `u ∈ [T, T+H]`, and
   `I(T) ≥ I(u)` for `u ∈ [T−H, T]`.
2. For each `u`, `sq_compare` with weight `η` gives
   `I(u) ≤ (1+η)∫₁ᵘ|P|² + (1+1/η)CE·V` and `(1−η)∫₁ᵘ|P|² ≤ I(u) + (1+1/η)CE·V`.
   Here `N = ⌈V⌉` is fixed for the whole window, with `V = T+H` or `V = T`.
3. Average step 2 over `u` in the window. The off-diagonal integrand
   `∫_a^b ∫₀ᵘ cos(θt) dt du = (cos θa − cos θb)/θ²` is `O(1/θ²)`
   (`abs_int_Sc_le`). The pair bound `1/|θ| ≤ 1 + min(m,n)/|n−m|` (`MeanSquare.inv_log_sub_le`)
   then gives `≤ 4 + 4N/(n−m)²`, so the off-diagonal sum is at most `20N²`. After dividing by
   `H`, the off-diagonal is `O(N²/H) = O(T/ε)`.
4. The diagonal is `(b²−a²)/(2H)·H_N = (T ± H/2)·H_N`. Combine this with
   `log N ≤ H_N ≤ 1 + log N`.
5. The `∫₀¹|P|²` correction is `≤ 4N`, using `|P| ≤ ∑ n^{−1/2} ≤ 2√N`.
6. Take `H = εT/2` and `η = ε`. The bookkeeping in `upper_alg` and `lower_alg` (pure real
   arithmetic) gives `Iz_eps`. Setting `ε = (log T)^{−1/2}` gives `Iz_sqrt`. The line `1/2+it`
   comes from `ZetaMeanSquare.integral_plus_eq_minus` (`riemannZeta_conj`). The constant
   `∫₀¹|ζ(1/2+it)|²` is absorbed.

The averaging trick is classical: a monotone function is pinned by its local averages. With it,
the trivial `1/θ²` bound suffices, and no Hilbert inequality is needed.

## 3. Files

| file | content | lines |
|---|---|---|
| `Poly.lean` | `normSq_dpoly_real`, `Sc`, `Sc_ne`, `abs_int_Sc_le`, `primitive_eq`, `avg_mv` | 143 |
| `Bound.lean` | `ch`, `sum_ch_sq`, `log_le_H`, `sum_ch_le`, `primitive_one_le`, `sum_inv_dist_sq_le`, `pair_le`, `offdiag_ch_le` | 213 |
| `Algebra.lean` | `upper_alg`, `lower_alg`, `abs_alg` (real inequalities) | 108 |
| `Critical.lean` | `fz`, `fe`, `G`, `Iz`, `err_le`, `compare`, `avg_G`, `upper`, `lower`, `Iz_eps`, `Iz_sqrt` | 258 |
| `Main.lean` | the line `1/2+it` from `0`, headlines, `#print axioms` | 102 |

Reused results: `ZetaMeanSquare.{err_L2, sq_compare, norm_Pz_eq, integral_plus_eq_minus,
ceil_bounds, continuousAt_zeta_line, continuous_Pz_line, bσ, Pz}` and
`MeanSquare.{dpoly, ex, normSq_dpoly, norm_ex, inv_log_sub_le, H, H_le_one_add_log}`. Mathlib
supplies `harmonic`, `log_add_one_le_harmonic`, `sum_Ioo_inv_sq_le`, `integral_cos`,
`integral_sin` and `continuous_primitive`.

## 4. Numerics (level 4): `scripts/zeta_critical/zeta_critical.gp`

Run with `gp -q zeta_critical.gp` (`nbthreads = 1`, about 80 s). Output is in `zeta_critical.out`.

| T | I(T) | I/(T log T) | (I − T log T)/(T√log T) | I − Ingham |
|---|---|---|---|---|
| 100 | 295.6 | 0.642 | −0.77 | 3.5 |
| 500 | 2276.4 | 0.733 | −0.67 | 10.8 |
| 1000 | 5212.5 | 0.755 | −0.65 | −11.8 |

- The ratio converges slowly, at the rate `1 − 1.68/log T`. This is Ingham's second term:
  `2γ − 1 − log 2π ≈ −1.6836`.
- `I − Ingham` stays at `O(T^{1/2})` size, as it should.
- The off-diagonal weight `/N²` is 3.25 at N = 300. The proved bound is 20.
- `avg_mv` is checked as an identity for N = 5 on [3, 7]: the difference is 2e−36.

## 5. Gaps, and what is not claimed

- **Ingham's second term** `(2γ − 1 − log 2π)T` and any `o(T)` error are not formalized. This
  method cannot reach them. The averaging loses `εT log T`, and the comparison
  `| |ζ|² − |P|² |` loses `ηT log T + T/η`. Both together give `T√log T`. That is the proved
  error, and it is only `o(T log T)`.
- **Two routes to the second term.** Either would be a large project.
  - (a) The Hardy–Littlewood approximate functional equation with two sums of length
    `√(t/2π)`. On top of it: the diagonal `∑_{n≤√(t/2π)} 1/n` twice, giving
    `log(t/2π) + 2γ`, plus the χ-twisted cross terms, which need a first-derivative test.
    Mathlib has no AFE.
  - (b) Keep `N = T` but evaluate the off-diagonal `∑_{m≠n} sin(T log(n/m))/(√(mn) log(n/m))`
    asymptotically, together with the cross term `2Re∫P·(ζ−P)` exactly.
  - Estimate: route (a) is 3000+ lines (AFE with an explicit error, a stationary-phase or
    first-derivative test, and harmonic sums with γ). Route (b) is similar.
- The headline uses `∫ t in 0..T` and `‖riemannZeta (1/2 + t*I)‖^2` as written above. The proved
  error is `O(T√log T)`, not the classical `O(T)`, and not Balasubramanian's or Ingham's
  `O(T^{1/2+ε})`.

## 6. Literature (from memory; attributions not checked)

- G. H. Hardy, J. E. Littlewood, *Contributions to the theory of the Riemann zeta-function and
  the theory of the distribution of primes*, Acta Math. 41 (1918): `∫₀ᵀ|ζ(1/2+it)|² ~ T log T`.
- A. E. Ingham, *Mean-value theorems in the theory of the Riemann zeta-function*, Proc. LMS
  (1926): the second term `(2γ−1−log 2π)T` with error `O(T^{1/2} log T)`.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §7.3–7.4. Ivić, *The Riemann
  Zeta-Function*, Ch. 15. Atkinson's formula (1949) gives the exact error `E(T)`.
- Montgomery–Vaughan (1974), the Hilbert inequality. This proof avoids it.
