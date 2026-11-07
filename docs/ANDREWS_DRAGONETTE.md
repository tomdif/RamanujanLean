# Dragonette's asymptotic for the coefficients of Ramanujan's mock theta function f(q)

`f(q) = Σ q^{n²}/(−q;q)_n² = Σ α(n) qⁿ`, where `α(n) = N(0,2,n) − N(1,2,n)` (`MockTheta3.f3_rank`).

> **Later status (2026-11-04).** Several gaps listed below are closed elsewhere:
> the sign `(−1)^{n+1}α(n) > 0` holds for **every** `n ≥ 1` (`Andrews.alpha_sign`, elementary; see
> [ANDREWS_1966](ANDREWS_1966.md)), so the "explicit N" gap is moot; **M2** (Andrews 1966, error `O(√n log n)`) is
> proved unconditionally (`MockCusp.andrews_1966_sqrt_log_unconditional`; see [ANDREWS_1966_ASYMPTOTIC](ANDREWS_1966_ASYMPTOTIC.md)
> and [MOCK_THETA_CUSPS](MOCK_THETA_CUSPS.md)); **M3** (the exact formula) remains open, see
> [ANDREWS_DRAGONETTE_EXACT](ANDREWS_DRAGONETTE_EXACT.md). All of these files are now in the root import.

## Result: M1 reached. Lean-proved and axiom-clean

`RamanujanTau/Dragonette/Main.lean`, namespace `Dragonette`. Here `α n := PowerSeries.coeff n MockTheta3.f3`.

```lean
theorem dragonette :
    Tendsto (fun n : ℕ => (-1) ^ (n + 1) * (α n : ℝ) * (2 * √(n : ℝ)) / Real.exp (π * √(n / 6)))
      atTop (𝓝 1)

theorem dragonette_isEquivalent :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (α n : ℝ))
      (fun n : ℕ => (-1) ^ (n + 1) * Real.exp (π * √(n / 6)) / (2 * √(n : ℝ)))

theorem dragonette_sign : ∀ᶠ n : ℕ in atTop, 0 < (-1) ^ (n + 1) * (α n : ℝ)

theorem rank_parity_sign : ∀ᶠ n : ℕ in atTop,
    0 < (-1) ^ (n + 1) * ((#{l : n.Partition | Even (rank l)} : ℝ) - #{l | ¬ Even (rank l)})
```

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem above. The same holds for
`phi_bound` and `Oz_transform`. There is no `sorry`, no new axiom and no `native_decide`. Each file was compiled
alone with `lake build RamanujanTau.Dragonette.Main`.

**Dragonette's normalization**: `RamanujanTau/Dragonette/Literal.lean` proves
```lean
theorem dragonette_literal : IsEquivalent atTop (fun n => (α n : ℝ))
  (fun n => (-1)^(n+1) * Real.exp (π * √(n/6 - 1/144)) / (2 * √((n:ℝ) - 1/24)))
```
It is also axiom-clean. The proof uses `√(n/6) − √(n/6−1/144) → 0` and `√(n−1/24)/√n → 1`.

## Evidence levels

1. **Lean, axiom-clean.**
   - Dragonette's asymptotic (`dragonette`, `dragonette_isEquivalent`).
   - The eventual sign pattern `(−1)^{n−1} α(n) > 0` (`dragonette_sign`).
   - The rank-parity form (`rank_parity_sign`).
   - All the intermediate analytic estimates listed below.
2. **Lean, conditional on named hypotheses.** None: nothing is conditional.
3. **Paper proof only.** None beyond the literature.
4. **Numerical evidence only.** `scripts/dragonette/alpha_check.py` computes `α(n)` exactly.
   - `(−1)^{n−1} α(n) > 0` holds for every `1 ≤ n ≤ 150000`; the run takes 14 s.
   - The ratio to `e^{π√(n/6−1/144)}/(2√(n−1/24))` is 1.1025 at n=10, 0.99930 at n=100 and 1 − 8·10⁻¹⁰ at n=1000.
     At n=8000 it equals 1 to double precision.
   - So the sign pattern is numerically true for all `n ≥ 1`. In Lean it is proved only for all *sufficiently large* `n`.

## Proof architecture (circle method at the cusp q = −1)

Put `s = e^{−z}`, `z = t + iθ`, `t = π/√(24n)` and `A = nt = π²/(24t)`, so that `2A = π√(n/6)`.

1. **Coefficient integral** (`Setup.coeff_integral_f`): `2π(−1)ⁿα(n) = ∫_{−π}^{π} f(−e^{−z})e^{nz} dθ`.
   It uses `|α(k)| ≤ p(k)`, which follows from `f3_rank`, together with the `Taylor`/`fA_T` realization from
   `MockTheta3Radial`.
2. **Watson's identity** (repo `MockTheta3.Radial.watson_disc`): `f(q) = 2φ(−q) − b(q)` on the disc.
3. **Transformation of b at q → −1** (`Odd.lean`, `Theta.lean`):
   - `b(−s) = (−s;s²)_∞ · Σ_ℤ s^{n²}` (`bA_neg`).
   - The product identity `(−s;s²)_∞(s;s)_∞(s⁴;s⁴)_∞ = (s²;s²)_∞²` (`Oz_mul`, via `tprod_even_mul_odd`).
   - Then `HardyRamanujan.F_modular` is applied at `z`, `2z` and `4z`. This gives
     `(−e^{−z};e^{−2z})_∞ = e^{π²/(24z)−z/24}·Fr(z)` (`Oz_transform`).
   - Mathlib's `jacobiTheta_S_smul` gives `Jt(π²/z) = (z/π)^{1/2} Jt(z)` (`Jt_transform`).
   - So `b(−e^{−z}) = (z/π)^{−1/2}e^{π²/(24z)−z/24}·Fr(z)Jt(π²/z)`, and `Fr·Jt = 1 + O(e^{−Re π²/z})`
     (`Fr_near`).
4. **Uniform bound for the mock theta function φ** (`Euler.lean`, `Phi.lean`, `Estimates.phi_bound`). This is
   the genuinely new estimate. For `‖s‖ = e^{−t}` and `0 < t ≤ 1/32`, at **every** argument of `s`:
   `‖φ(s)‖ ≤ (−r;r²)_∞·(1/t)·e^{−1/(2400t)}`.

   Note that `(−r;r²)_∞ ~ e^{π²/(24t)}` is exactly the size of `b`, so `φ` is exponentially smaller than `b`
   everywhere on the circle. The proof has three steps:
   - **Termwise bound.** `‖1+u‖ ≥ (1−‖u‖)e^{(‖u‖+Re u)/8}`, so the n-th term is at most `c_n e^{−G_n/8}`.
   - **Lower bound on `G_n`.** Pairing `j` with `2j` gives `G_n ≥ (7/16) m r^{4m}` for `2m ≤ n`, which rests on
     `(y + Re u) + (y² + Re u²) ≥ (7/8)y²`.
   - **Euler's identity in real form.** `S(x) = Σ xⁿr^{n²}/(r²;r²)_n = (−xr;r²)_∞` is proved from the functional
     equation `S(x) = (1+xr)S(xr²)`. It is used at `x = 1` for large `n`, and at `x = 1/2` together with
     `S(1/2) ≤ S(1)e^{−r/(4(1−r²))}` for small `n`.
5. **Minor arc for b** (`Bounds.Oz_minor`): `‖(−s;s²)_∞‖ ≤ (−r;r²)_∞ e^{−1/(160t)}` for `t ≤ |θ| ≤ π`.
   The proof uses `‖1+u‖ ≤ (1+‖u‖)e^{−(‖u‖−Re u)/4}` and `Re(s/(1−s²)) ≤ (1/2)/‖1−s‖`. The latter is combined
   with the `‖1−s‖ ≥ (25/23)(1−r)` argument of `HardyRamanujan.minor_bound`.
6. **Laplace's method** (`Laplace.Jneg_tendsto`): a copy of `HardyRamanujan.J_tendsto` with `(1+iu)^{−1/2}`
   in place of `(1+iu)^{+1/2}`.
7. **Assembly** (`Main.decomp_D`): `K_n(−1)^{n+1}α(n) = (1/√π)J_n + E_n`, where `K_n = 2√n e^{−2A}`.
   The error satisfies `‖E_n‖ ≤ Err(1/t)` and `Err(u) → 0`.

### Files

| file | contents |
|---|---|
| `Dragonette/Theta.lean` | `Jt`, Jacobi transformation, bounds, link with `θA` |
| `Dragonette/Odd.lean` | `Oz = (−s;s²)_∞`, product identity, `Oz_transform`, `bA_neg` |
| `Dragonette/Laplace.lean` | `hneg`, `Jneg_tendsto` |
| `Dragonette/Euler.lean` | Euler's series `Sx`, functional equation, `Sx_half`, `Oz_ofReal` |
| `Dragonette/Phi.lean` | factor/pair/`G_lower` bounds, `norm_gA_le` |
| `Dragonette/Bounds.lean` | `Fr_near`, `factor_upper`, `Oz_norm_upper`, `Oz_minor` |
| `Dragonette/Estimates.lean` | `phi_bound`, `Oz_real_le` |
| `Dragonette/Setup.lean` | `α`, coefficient integral, saddle point, `integrand_eq`, `MD_scale`, `PD_eq` |
| `Dragonette/Literal.lean` | `dragonette_literal` (original normalization) |
| `Dragonette/Main.lean` | arc bounds, `decomp_D`, `dragonette`, `dragonette_isEquivalent`, `dragonette_sign`, `rank_parity_sign` |

About 1,900 lines in total. These files were written outside the root import; `RamanujanTau.Dragonette.Literal` (which imports
`Dragonette.Main`) has since been added to `RamanujanTau.lean`.

## The explicit sign theorem: status and analysis (follow-up)

**Literature.** Gomez–Zhu (arXiv:2008.08253, Thm 1.1) prove the following for all `n ≥ 1`:
- `α(n) = (−1)^{n+1}(√6/√(24n−1)) e^{l(n)/2} + E(n)`;
- `|E(n)| < (4.30·10²³)^{2q(n)} |D_n|² e^{l(n)/3}`, where `D_n = 1−24n`, `l = π√|D_n|/6` and
  `q = log|D_n| / |log log|D_n| − 1.1714|`.

They do **not** state the sign pattern. Their Corollary 5.2 concerns `N(r,2;n)/p(n)`. My evaluation of their
bound: main > error, and hence the sign, follows from it only once `n` is greater than about `10⁷`. At
`n = 5·10⁶` it still fails. So "sign for every `n ≥ 1`" would follow from Gomez–Zhu plus a finite check to about
`10⁷`, which nobody has done (my numerics reach `1.5·10⁵`). Masri's earlier power-saving bound and Ahlgren–Dunn
are ineffective or not stated with explicit constants, as far as their abstracts show. I found no published
statement of the all-`n` sign pattern.

**What our Lean route can give.** The sign needs `(1/√π) Re J_n > ‖E_n‖`, where `‖E_n‖ ≤ Err(u)`, `u = 1/t`
and `n = π²u²/24`.
- The dominant term of `Err` is `8πu² e^{−u/2400}`, which comes from the φ-bound rate `1/2400`.
- With an effective Laplace step (`J_n → √π` currently goes through dominated convergence),
  `Err(u) < 1/2` requires `u ≈ 6·10⁴`, i.e. **`N ≈ 1.5·10⁹`**. This is a paper-level estimate. It is
  **not** formalized: the effective Laplace bound and an explicit bound on `C0` are not in Lean.

**Why this route cannot reach a kernel-checkable N.** A kernel table of `α(n)` is feasible to a few thousand at
best. The `p(n)` packed table of `JensenThreshold/` reaches `n ≈ 1237`, and `α(n)` would also need the
Appell–Lerch recurrence `(q;q)_∞ f(q) = 1 + 4Σ(−1)ⁿq^{n(3n+1)/2}/(1+qⁿ)` proved. At `N ≈ 2000` (`u ≈ 70`)
the decay rate must be `c ≳ 0.23` in `e^{−c/t}`. Two rates are intrinsically capped below that:
- The minor-arc decay of `b` at the edge `|θ| = t` is at most `e^{−A/2}`, i.e. `c ≤ π²/48 ≈ 0.21`, so the major
  arc has to be widened.
- The decay of `φ` relative to `b` is at most `π²/24 − π²/96 ≈ 0.31`. The bound at the next cusp gives Gomez–Zhu's
  `e^{l/3}`, i.e. `c = π²/36 ≈ 0.27`.
- The elementary termwise φ bound gives `c = 1/2400`. Even an optimized saddle analysis of that termwise bound
  realistically gives about `0.05`.

Reaching `c ≈ 0.25` needs the transformation of `f` (or `φ`) at the cusps `q → ±i`, which is M2 territory
(excluded by the brief). **Conclusion: no explicit-`N` theorem was formalized.** The best statement our route
supports, on paper, is `N ≈ 1.5·10⁹`. That is far too large for any kernel check, so I stopped there rather
than formalize a useless `N`.

## Gaps

- **An explicit N for the sign theorem.** (Moot: `Andrews.alpha_sign` now proves the sign for every `n ≥ 1`.) This was not done. The analytic constants are explicit: the decay rate
  is 1/2400 in `1/t`, and `C0 = Σ p(k)2^{−k}` is bounded. However, the main-term convergence `J_n → √π` is
  proved by dominated convergence, which is ineffective. Even with an effective Laplace step, the crude rate
  `e^{−√(24n)/(2400π)}` would put N far beyond any finite check (around 10⁸ or more). Getting a usable N needs
  either sharper constants (exact Li₂-type bounds for φ) or a Rademacher-type error bound. In either case one
  then still needs a finite check up to that N, by kernel `decide` or a certificate.
- **M2, Andrews 1966** (error `O(√n)`, or `O(n^{1/2+ε})`). (Since proved with Andrews' error `O(√n log n)`:
  `MockCusp.andrews_1966_sqrt_log_unconditional`.) Not attempted here. It needs the behaviour of f at every
  even-order cusp `q → e^{2πih/2k}`. That means Watson's 1936 transformation of `f` in general (`f` is related
  to `ω` and a Mordell integral), Kloosterman-type sums `A_{2k}`, and a Farey dissection like the repo's
  `Rademacher/`. None of the general-cusp transformations of `f` exist in the repo. The q → −1 route used here
  only works because at that single cusp Watson's `f = 2φ(−q) − b` separates out an eta-quotient.
- **M3, the Andrews–Dragonette exact formula** (Bringmann–Ono 2006; Ahlgren–Dunn 2019). Not attempted. It
  needs harmonic Maass forms / Zwegers' completion, or the Ahlgren–Dunn bounds on Kloosterman sums, on top of
  M2.

## Literature checked

- Dragonette, *Trans. AMS* 72 (1952), and Andrews, *Amer. J. Math.* 88 (1966). Andrews refined the asymptotic
  and conjectured the exact formula, which Bringmann and Ono, *Invent. Math.* 165 (2006), proved.
- Effective bounds for `α(n)`, via the finite algebraic formula of Bruinier–Schwagenscheidt / Alfes, are due to
  Masri and to Gomez–Zhu, arXiv:2008.08253. Gomez–Zhu apply them to the Hou–Jagadeesan convexity conjectures for
  `N(0,2,n)` and `N(1,2,n)`.
- I did not find an explicit statement "α(n) alternates in sign for all n ≥ 1". It almost certainly follows
  from these effective bounds plus a finite check, but I did not verify that.
- The leading asymptotic `a(n) ~ −(−1)^n e^{π√(n/6)}/(2√n)` is recorded in OEIS A000025.
- The step that bounds φ uniformly on the whole circle via Euler's functional equation is my own route. I have
  not seen it stated in this form.

## Honest estimate to go further

- **Dragonette in its literal `1/144`, `1/24` normalization:** about 30 Lean lines.
- **An effective N plus a finite check:** probably 1–2k lines. It needs an effective Laplace bound and sharper
  φ constants, and the finite check might reach n ~ 10⁶ via certificates.
- **M2:** a multi-week project, starting with Watson/Gordon–McIntosh transformations of `f` at all cusps.
- **M3:** substantially beyond that.
