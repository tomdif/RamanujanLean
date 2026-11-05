# Quantitative sign changes of `τ(p)` over primes

Lean: `RamanujanTau/TauSignsQuant/` (4 files, 567 lines: `Density`, `Count`, `Proportion`, `Main`).
There is no `sorry`, no new axiom and no `native_decide`. Build with
`nice -n 10 lake build RamanujanTau.TauSignsQuant.Main` (exits 0). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all 15 headlines. Only new files were added, and
the root `RamanujanTau.lean` does not import this directory.

Notation: `λ(p) = τ(p)p^{−11/2}` (`lam`), and `ε ∈ {1, −1}`.

## Headline results

| statement | Lean | evidence |
|---|---|---|
| `∑_{p : ελ(p)<0} \|λ(p)\| log p · p^{−σ} = ∞` for every `σ < 29/40` | `not_summable_signed_part` | (1) |
| `∑_{p : ελ(p)<0} p^{−β} = ∞` for every `β < 9/20` | `not_summable_rpow_signed` | (1) |
| **`∑_{τ(p)>0} p^{−β} = ∞` and `∑_{τ(p)<0} p^{−β} = ∞`, every `β < 9/20`** | `not_summable_tau_pos`, `not_summable_tau_neg` | (1) |
| **for every `θ < 9/20`: `#{p<x : τ(p)>0} ≥ x^θ` for arbitrarily large `x`; the same for `τ(p)<0`** | `tau_pos_count_frequently`, `tau_neg_count_frequently` | (1) |
| general: `∑_{P(n)} n^{−β} = ∞`, `0<θ<β` ⟹ `count P x ≥ x^θ` infinitely often | `count_frequently_of_not_summable` | (1) |
| `∑_{p<N} λ(p) log p = o(N)` | `S1_small` | (1) |
| **if `\|λ(p)\| ≤ M` for all primes `p < N`, and `N ≥ N₀(M)`, then `∑_{p<N, ±τ(p)>0} log p ≥ N/(3M²)`** | `signed_mass_of_bound_upto`, `tau_pos_mass_of_bound_upto`, `tau_neg_mass_of_bound_upto` | (1), with a finitary hypothesis inside the statement |
| `[DeligneBound]`: `∑_{p<N, ±τ(p)>0} log p ≥ N/12` for `N ≥ N₀` | `tau_pos_mass_deligne`, `tau_neg_mass_deligne` | (2) |
| `[DeligneBound]`: `#{p<N : ±τ(p)>0} · log N ≥ N/12` for `N ≥ N₀` | `tau_pos_count_deligne`, `tau_neg_count_deligne` | (2) |

```lean
theorem not_summable_tau_pos {β : ℝ} (hβ : β < 9 / 20) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ 0 < tau p then (p : ℝ) ^ (-β) else 0)
theorem tau_pos_count_frequently {θ : ℝ} (hθ : θ < 9 / 20) (X : ℕ) :
    ∃ x, X ≤ x ∧
      (x : ℝ) ^ θ ≤ (((Finset.range x).filter (fun p => p.Prime ∧ 0 < tau p)).card : ℝ)
theorem tau_pos_mass_of_bound_upto {M : ℝ} (hM : 0 < M) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (∀ p : ℕ, p < N → p.Prime → |lam p| ≤ M) →
      (N : ℝ) / (3 * M ^ 2) ≤ ∑ p ∈ Finset.range N with (p.Prime ∧ 0 < tau p), Real.log p
theorem tau_pos_count_deligne [DeligneBound] : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / 12 ≤ ((Finset.range N).filter (fun p => p.Prime ∧ 0 < tau p)).card * Real.log N
```

The negative-sign versions have the same form, with `tau p < 0`.

So the strongest **unconditional** quantitative statement proved is the following. Each sign
class of primes has upper counting exponent at least `9/20`. That is,
`limsup log #{p<x : ±τ(p)>0} / log x ≥ 9/20`, and in fact the sign class is not even
`p^{−β}`-summable for any `β < 9/20`. This is a limsup (Ω-type) result, not a lower bound valid
for every large `x`.

## Proofs

### 1. Landau with an absolutely convergent wrong-sign part (`Density.lean`)

`TauPNTUncond.not_eventually_signed_uncond` assumed that `ελ(p) ≥ 0` for all `p ≥ P`. We weaken
this hypothesis to: the wrong-sign part `∑_{ελ<0} |λ| log p · p^{−σ}` converges for some
`σ < 29/40`. The proof then runs as follows.

1. Set `σ₁ = max(σ, 5/8)`.
2. Define `a(p) = ελ(p) log p` when `ελ(p) ≥ 0`, so `a ≥ 0`. Let `b = εΛ_Δ − a`, which consists of
   the wrong-sign primes plus the prime powers.
3. `b` is absolutely convergent at `σ₁`. For the wrong-sign primes this is the hypothesis; for the
   prime powers it is `summable_vH_58`.
4. `L(Δ, s + 11/2) > 0` on the real axis by `HeckeL.tauL_pos`.
5. `landau_abscissa` then gives that `∑ a(n)n^{−σ₂}` converges for `σ₂ = (σ₁ + 29/40)/2`.
6. Hence `∑_p |λ(p)| log p · p^{−σ₂} < ∞`.
7. Weil (`weil_uu`, `|λ(p)| ≤ C p^{11/40}`) gives `λ²/p ≤ C|λ| p^{−29/40} ≤ C|λ| p^{−σ₂}`. This
   contradicts `Weil.not_summable_lam_sq`, which says `∑_p λ(p)²/p = ∞`.

Converting to `∑ p^{−β}`: put `δ = (9/20 − β)/2` and `σ = β + 11/40 + δ < 29/40`. By Weil and
`log p ≤ p^δ/δ`, we get `|λ| log p · p^{−σ} ≤ (C/δ) p^{−β}`.

The exponent is `9/20 = 1 − 2·(11/40)`. It equals `1 − 2θ_W`, where `θ_W` is the Weil exponent of
`|λ(p)| ≪ p^{θ_W}` that the repo has unconditionally (`τ(n) = O(n^{23/4+1/40})`).

### 2. From non-summability to counts (`Count.lean`)

Suppose `count P x < x^θ` for all `x ≥ X`. Let `q_m = Nat.nth P m`; the set `{P}` is infinite,
since otherwise the series would be a finite sum. Then:

- `count P q_m = m`, so `m < q_m^θ`;
- therefore `q_m > m^{1/θ}`;
- therefore `q_m^{−β} ≤ m^{−β/θ}`, which is summable because `β/θ > 1`;
- `nth` is injective with range `{P}` (`Function.Injective.summable_iff`).

This contradicts the non-summability.

### 3. Positive proportion from a finitary Ramanujan bound (`Proportion.lean`)

- If `|λ| ≤ M`, then pointwise `λ²/M + ελ ≤ 2M·[ελ > 0]`.
- Multiply by `log p` and sum over `p < N`.
- `rs_prime_PNT` gives `∑ λ² log p ≥ 5N/6`.
- `S1_small`, the dlVP error term of `TauPNTError.tau_PNT_error_uncond`, gives
  `|∑ λ log p| ≤ N/(6M)`.
- Together these give `2M·∑_{ελ>0} log p ≥ 2N/(3M)`.

The hypothesis concerns only the primes `p < N`. So the theorem is unconditional and says exactly
this: at a large `N`, either both signs carry a log-proportion of at least `1/(3M²)` below `N`, or
some prime `p < N` violates `|τ(p)| ≤ M p^{11/2}`. With Deligne (`M = 2`), each sign carries at
least `1/12` of `θ(N) ~ N`.

## What is blocked, and why

1. **A lower bound for every large `x`, unconditionally** (for example
   `#{p ≤ x : τ(p) > 0} ≫ x^θ / log x` for all large `x`, for any fixed `θ > 0`). **Blocked.** The
   moment route needs `∑_{p≤x} λ(p) log p` to be smaller than the available lower bound for
   `∑_{p≤x} |λ(p)| log p`.
   - Without Deligne, the best pointwise information is `|λ| ≤ C p^{11/40}`. That gives only
     `∑ |λ| log p ≥ ∑ λ² log p / max|λ| ≫ x^{29/40}`.
   - The first moment is known only to be `≪ x exp(−b√log x)`, the de la Vallée-Poussin region.
   - That error term swamps `x^{29/40}`. Hölder against a fourth moment would fix this, but
     `∑ λ(p)⁴ log p ≪ x` needs `L(Sym²×Sym²)` or `Sym⁴` theory, which is not available. Weil
     bounds on `λ⁴` give back the same `x^{3/4−ε}`.
   - Short intervals `[x, x+h]` fail for the same reason. The Rankin–Selberg PNT
     (`rs_prime_PNT`) also has no error term, so `h ≥ δx` would be needed even under Deligne.
2. **An effective Landau theorem.** Landau's argument is the only unconditional route here that
   beats the Weil loss. It needs analytic continuation of `L'/L` to `σ < 29/40` along the real
   axis.
   - A finite-window version would say "if `λ ≥ 0` on `(y, Y]`, then `Y ≤ F(y)`". This would give
     `≫ log log x`-type counts of sign changes, valid for all `x`.
   - It cannot be obtained from the Taylor-at-`c` argument. Centres `c < 1` require the Dirichlet
     series to converge at `c`, and that fails once the signs above `Y` are unknown.
   - An effective version needs Turán power-sum / Pintz–Kaczorowski explicit-formula machinery
     (zeros of `L(Δ, s)` near the real segment, and zero-density estimates), which is not in the
     repo.
3. **Positive proportion, unconditionally.** Blocked by the absence of Deligne. Up to `N`, it is
   equivalent to Ramanujan holding below `N` (section 3). The natural target, density `1/2` for
   each sign, needs Sato–Tate (Barnet-Lamb–Geraghty–Harris–Taylor).
4. **Improving `9/20`.** The exponent is exactly `1 − 2θ_W`.
   - Kloosterman/Weil-type `θ = 1/4 + ε` at primes would give `1/2 − ε`.
   - Deligne (`θ = 0`) gives exponent `1`, and positive proportion by section 3.
   - The Landau threshold itself (`5/8`, from Rankin at `k = 2`) is not the bottleneck.

## Literature

- Landau (1905); Ram Murty, *Oscillations of Fourier coefficients of modular forms*, Math. Ann. 262
  (1983).
- Kaczorowski–Pintz, oscillation theorems via effective Landau.
- Kowalski–Lau–Soundararajan–Wu, *On modular signs* (2010).
- Matomäki–Radziwiłł (2015), sign changes in short intervals (these use Deligne).
