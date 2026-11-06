# t-aspect subconvexity for `L(Δ, s)`: feasibility, the chosen route, and what is built

> **Update (2026-11-06):** sharpened to SCS(1/22, 1/2) and δ = 1/231 in `SCSSharp.tauL_subconvex_sharp`; see [SCS_SHARP](SCS_SHARP.md).

> **Update (2026-11-05):** subconvexity is now proved unconditionally (`SCSProof.tauL_subconvex`, δ = 1/832000, `tauL_subconvex_3_5`) by a different route than b1–b4 below, which [SCS_PROOF](SCS_PROOF.md) shows cannot work as stated.

**Status (2026-11-05).** Subconvexity, `|L(Δ,6+it)| ≪ (1+|t|)^{1/2−δ}` for some `δ > 0`, is
**not proved**, neither unconditionally nor under `[DeligneBound]`. Deligne's bound does not help;
§6 explains why. This document gives:

1. a feasibility analysis of the candidate routes;
2. the route chosen for this repository;
3. the rigorous GL(2) inputs built in `RamanujanTau/Subconvexity/`. All of them are Lean,
   axiom-clean, and have no hypotheses;
4. a map of what remains, with line estimates.

Build (only these files): `nice -n 10 lake build RamanujanTau.Subconvexity.Main` exits 0.
`#print axioms` prints `[propext, Classical.choice, Quot.sound]` for every headline. A grep finds
no `sorry`, `native_decide` or `axiom` in the directory. Nothing outside `RamanujanTau/Subconvexity/`
and this file was modified.

## 0. Normalization and the target

Let `λ(n) = τ(n) n^{−11/2}`. Then `L(Δ, 6+it) = Σ λ(n) n^{−1/2−it}`, and the analytic conductor is
`≍ t²`. Convexity `≪ t^{1/2+ε}` is `HeckeConvex.tauL_convexity`.

All routes start from the same reduction. A smoothed approximate functional equation (AFE) gives

    L(6+it) = Σ_n λ(n) n^{−1/2−it} V(n/t) + ε(t) Σ_n λ(n) n^{−1/2+it} V(n/t) + O(t^{−A}),

with `V` essentially supported on `n ≤ t^{1+ε}`. A dyadic split then reduces subconvexity to:

> **(S)** for `t^{1−2δ} ≤ N ≤ t^{1+ε}` and a smooth bump `w`:
> `S(N) := Σ_n λ(n) n^{−it} w(n/N) ≪ N^{1/2} t^{1/2−δ}`.

The trivial bound is `S(N) ≪ N` (Rankin, `Σ_{n≤N}|λ(n)| ≪ N`), and it already gives (S) for
`N ≤ t^{1−2δ}`. The whole problem is the range `N ≍ t`, where (S) asks for
`S(N) ≪ N^{1−δ}`.

## 1. Route (b): short-interval mean square from the Parseval/ray machinery

**The idea.** If `∫_{T−H}^{T+H} |L(6+it)|² dt ≪ H T^ε` for `H = T^θ` with `θ < 1`, then
`|L(6+iT)| ≪ T^{θ/2+ε}`. That step needs a pointwise-from-mean lemma of Gabriel / Ivić Lemma 7.1
type.

**What the repo has.** The repo has the exact Plancherel identity along rays,

    ∫ |Λ(6+it)|² e^{2at} dt = 2π ∫_ℝ e^{−12u} |Δ(i e^{ia} e^{−u})|² du        (|a| < π/2),

and Good's main term `∫₀ᵀ|L|² ~ 2cT log T`. The main term comes from Zagier's horocycle limit
(`CriticalMeanSquareAsymp`).

**Why the existing machinery cannot localize, even with a power-saving rate.**

* **(i) Real rotation angles give only Laplace weights.** Write `a = π/2 − δ`. The identity
  controls `F(δ) = ∫ |L(6+it)|² t^{11} e^{−2δt} (1+o(1)) dt`, which is a Laplace transform. Suppose
  even that `F(δ) = M(δ) + O(δ^{−12+η})`, with power saving from Rankin's `O(N^{3/5})` or
  Sarnak-type horocycle rates. A window `[T, T+H]` is then still not controlled. To bound
  `∫_T^{T+H}|L|²` one needs a combination `Σ c_j e^{−2δ_j t}` that majorizes
  `1_{[T,T+H]}(t) t^{−11}`. In the variable `u = e^{−t/T}` this is a polynomial majorant of an
  interval of length `≍ H/T`. Such a polynomial has degree `≳ T/H` and coefficients of size
  `e^{c T/H}`, so the error terms `c_j δ_j^{−12+η}` blow up unless `H ≫ T/log T`. That gives
  `∫_T^{T+T/log T} ≪ T`, which is nothing. Positivity alone gives only "mass in a window ≤ main
  term", which is the trivial bound.
* **(ii) Complex rotation angles, or dilations, give off-diagonal terms.** These do produce
  oscillating weights `e^{−2δt} λ^{it}`. But the right side becomes a correlation
  `∫ Δ(z) conj Δ(λz) y^{12}` along a hypercycle. Expanding it produces exactly the shifted sums
  `Σ_n λ(n) λ(n+h)`.
* **(iii) The horocycle version makes (ii) exact.** `Subconvexity.hasSum_shifted_parseval` (Lean):

      ∫₀¹ |Δ(x+iy)|² e(−hx) dx = Σ_n τ(n) τ(n+h) e^{−2π(2n+h)y}.

  So the `h`-th Fourier coefficient of `y¹²|Δ|²` along a horocycle is the shifted convolution sum
  `D_h`. Zagier's horocycle equidistribution and its rates are statements about `h = 0` only.
  Localizing to windows of length `H` needs `D_h` with power saving for `1 ≤ |h| ≤ T^{1+ε}/H`.

**Conclusion for (b).** Route (b) is viable only together with a power-saving shifted-convolution
bound:

> **SCS(η, B):** `Σ_n λ(n) λ(n+h) W(n/N) ≪ N^{1−η+ε} h^B`, uniformly for `1 ≤ h ≤ N`, for `W` in a
> fixed class of smooth bumps with derivative bounds.

Granting SCS(η, B), the off-diagonal of the Fejér-smoothed mean square is computed as follows.
Use a kernel `k ≥ 0` with `k̂` supported in `[−1,1]`. Only pairs with `|m−n| ≤ N/H` survive, and

    off-diagonal ≪ (H/N) Σ_{1≤h≤N/H} N^{1−η+ε} h^B ≪ N^{1−η+ε} (N/H)^B.

This is `≪ H` once `H ≥ T^{1−η/(1+B)+ε}`. Then `|L(6+iT)| ≪ T^{1/2 − η/(2(1+B)) + ε}`.

**SCS without spectral theory.** SCS can be proved without Maass forms, using Selberg's
Poincaré-series argument together with Weil's Kloosterman bound. The Weil bound is already
**unconditional in this repo**: `StepanovAS.weilPrimeBound`, together with
`KloostermanL`/`WeilKloosterman`. The argument:

* Let `P_h(z,s) = Σ_{Γ∞\Γ} Im(γz)^s e(h Re γz)`.
* Unfolding against the bounded `Γ`-invariant function `y¹²|Δ|²` gives
  `⟨y¹²|Δ|², P_h(·,s̄)⟩ = Γ(s+11) Σ τ(n)τ(n+h) (4π(n+h/2))^{−s−11}`.
* The Fourier expansion of `P_h` has Kloosterman–Bessel terms, and `Σ_c |S(h,m;c)| c^{−2σ}`
  converges for `σ > 3/4` by Weil.
* So `D_h(s)` is holomorphic on `Re s > 3/4` with polynomial growth in `|Im s|`. The polynomial
  growth comes from integration by parts in the Bessel-type integral.
* Mellin inversion then gives **SCS(1/4, B)** with a small `B`.

Granting that I recall the `h`-dependence correctly, and taking `B ≤ 1/2` conservatively, this yields
**`δ = 1/12`**: `|L(Δ,6+it)| ≪ t^{5/12+ε}`.

The ingredients are all bounds; no stationary-phase main terms are needed:

* the Poincaré series and its Fourier expansion (Poisson in `d mod c`);
* Weil's bound (done);
* Rankin–Selberg unfolding, which `RankinSelberg/` already does for `h = 0`;
* the AFE;
* the Fejér mean value;
* a pointwise-from-mean lemma.

## 2. Route (a): Voronoi summation, exponential sums and stationary phase (Jutila 1987; Booker–Milinovich–Ng 2019; Aggarwal 2020)

**Voronoi input, done in Lean.** For `a ā − bq = 1` the matrix `γ = [[−ā, b],[q, −a]]` gives
`Δ(−ā/q + i/(qt)) = t¹² Δ(a/q + it/q)` (`twF_inv`). From this:

* the completed twists `Λ(x,s) = ∫₀^∞ Δ(x+it/q) t^{s−1} dt` are entire;
* `Λ(−ā/q, 12−s) = Λ(a/q, s)`, which is `twLambda_functional_equation`;
* `Λ(x,s) = (2π/q)^{−s} Γ(s) L(Δ,x,s)`, which is `twLambda_eq`.

This is the functional equation from which every GL(2) Voronoi formula with additive twists is
derived.

**What Wilton alone gives: convexity, not more.** Take `S(N)` with `N ≍ t`. Split `[N,2N]` into
`√t` blocks of length `M = N/√t`. On each block `n^{−it} = e(αn) g(n)`, where `g` has total
variation `≤ tM²/N² = 1`. Wilton (`wilton_bound`, normalized `Σ_{n≤x} λ(n) e(nα) ≪ x^{1/2} log x`
uniformly in `α`) bounds each block by `√N log N`. So `S(N) ≪ √t √N log N`, which is exactly
convexity. The same computation gives `S(N) ≪ N^{1−δ}` only for `N ≥ t^{1+2δ}`, the easy range.

**A trivially bounded Voronoi transform also gives exactly convexity.** This is a heuristic
computation, not formalized. Take Farey arcs around `a/q` with `q ≤ Q`. Arc length is
`M_q ≍ N/(qQ)` because `f'' ≍ 1/N` for `f(n) = −(t/2π)log n`. On an arc, Voronoi plus stationary
phase gives a dual sum of length `≍ q²M²/N` with amplitude `≍ q^{−1/2} N^{1/4}`, so

    |S_arc| ≪ q N^{−1/2} M_q^{3/2} = N q^{−1/2} Q^{−3/2}.

There are `≍ φ(q)` arcs per denominator, so the total is `Σ_{q≤Q} q · N q^{−1/2}Q^{−3/2} ≍ N` for
every `Q`. The saving to `t^{1/3}` therefore has to come from cancellation in the dual sums or
in the sum over `a`. Jutila gets it from a mean-value step over the arcs. Aggarwal's simple δ-method
gets it by conductor lowering, Poisson in the second variable, Cauchy–Schwarz and a second Poisson.
Both need genuine stationary-phase asymptotics, with main terms, for the Bessel transforms.

**Major-arc decay, done in Lean.** `smooth_twist_decay` gives

    Σ τ(n) e(an/q) e^{−2πny} = Δ(a/q+iy),   ‖·‖ ≤ A (qy)^{−12} e^{−2π/(q²y)}   once 1/(q²y) ≥ Y.

That is, smooth sums of length `X` twisted by `e(an/q)` with `q ≤ X^{1/2−ε}` are `O(X^{−∞})`. This
is the exponential-weight case of Voronoi.

## 3. Choice of route

Route (a) needs a full stationary-phase lemma with main term and uniform error for
`∫ w(x) e(g(x)) J_{11}(4π√(mx)/q) dx`. On top of that it needs a delicate cancellation step.

Route (b), in the form "Selberg–Weil SCS ⇒ short-interval mean square ⇒ pointwise", needs only
upper bounds for oscillatory integrals, plus infrastructure the repo largely has: the Weil bound,
Rankin–Selberg unfolding, the Parseval identities, and the Stirling bounds used in
`MeanSquareLeft`.

**Recommended route: (b) via Selberg's Poincaré series + the repo's Weil bound.**

The target is `|L(Δ,6+it)| ≪ t^{1/2−δ}` with `δ = η/(2(1+B))`, where `η = 1/4−ε` from Weil;
`δ ≈ 1/12` if `B ≤ 1/2`. Route (a) stays the fallback. Its Voronoi input is now in place.

## 4. What is built (evidence level 1: Lean, axiom-clean, no hypotheses)

| File | Lines | Content |
|---|---|---|
| `Subconvexity/Wilton.lean` | 300 | the twisted coefficient integral and Wilton's uniform bound |
| `Subconvexity/TwistedFE.lean` | 315 | the modular relation for `a/q`, the StrongFEPair, the twisted functional equation, the Dirichlet series, major-arc decay |
| `Subconvexity/Shifted.lean` | 109 | the shifted Parseval identity on horocycles |
| `Subconvexity/Main.lean` | 31 | imports and `#print axioms` |

Headline statements:

* `tau_twist_integral n hy α : τ(n) e(nα) = ∫₀¹ 𝕢(x+iy)^{−n} Δ(x+α+iy) dx`.
* **`wilton_bound`**: `∃ C ≥ 0, ∀ α : ℝ, ∀ M ≥ 1, ‖Σ_{n≤M} τ(n) e(nα)‖ ≤ C M⁶ log(1+2M)`.
* `twF_inv hq a ā b (h : a ā − b q = 1) ht : twF q (−ā/q) (1/t) = t¹² · twF q (a/q) t`, where
  `twF q x t = Δ(x + i t/q)`.
* `twLambda_entire`: `Λ(a/q,·)` and `Λ(−ā/q,·)` are entire.
* **`twLambda_functional_equation`**: `Λ(−ā/q, 12−s) = Λ(a/q, s)` for all `s ∈ ℂ`.
* `twLambda_eq hq x (hs : 7 < Re s)`: `Λ(x,s) = (2π/q)^{−s} Γ(s) LSeries (n ↦ τ(n)e(nx)) s`.
* **`smooth_twist_decay`**: `∃ A Y`, for all `q ≥ 1` and `a ā − bq = 1`, and all `y > 0` with
  `1/(q²y) ≥ Y`:
  `HasSum (n ↦ τ(n)e(na/q)e^{−2πny}) (Δ(a/q+iy))` and
  `‖Δ(a/q+iy)‖ ≤ A (qy)^{−12} e^{−2π/(q²y)}`.
* **`hasSum_shifted_parseval h hy`**:
  `Σ_n τ(n)τ(n+h) e^{−4πny} = ∫₀¹ Δ(x+iy) conj Δ(x+iy) 𝕢(x+iy)^{−h} dx`.

## 5. What remains, with line estimates

Route (b), recommended. Lean line estimates assume the repo's existing infrastructure.

| # | Step | Status | Est. lines |
|---|---|---|---|
| b1 | Poincaré series `P_h(z,s)` on `Re s > 1`: convergence, `Γ`-invariance, unfolding against `y¹²|Δ|²` (generalize `RankinSelberg` from `E(z,s)`) | todo | 600–900 |
| b2 | Fourier expansion of `P_h` by Poisson in `d mod c`: Kloosterman sums `S(h,m;c)` times the integrals `∫(1+u²)^{−s} e(−muy − h/(c²y(u+i))) du` | todo | 800–1200 |
| b3 | Weil ⇒ `P_h` holomorphic and `L¹(Γ\H)` on `Re s > 3/4`, bounds polynomial in `\|Im s\|` (integration by parts in `u`); the prime Weil bound is **done** (`StepanovAS.weilPrimeBound`), and the composite-`c` bound for `S(1,n;c)` exists (`WeilKloosterman.kloostermanBound_half_of_weil`). General `S(h,m;c)` needs a short extension (about 150 lines) | todo; Weil done | 500–800 |
| b4 | Continuation of `D_h(s)` and smooth SCS(1/4−ε, B) by Mellin inversion | todo | 300–500 |
| b5 | Smoothed AFE for `L(Δ,6+it)`, uniform in `t`: `Γ(12−s)/Γ(s)` bounds (`MeanSquareLeft.GammaAsymp`, Stirling) and contour shift (`MeanSquare.Shift`) | todo | 600–900 |
| b6 | Fejér-smoothed short-interval mean value: diagonal `H log T`, off-diagonal via SCS, cross terms with the dual AFE sum | todo | 600–900 |
| b7 | Pointwise-from-mean lemma (`\|L(6+iT)\|² ≪ log T ∫\|L(6+iT+iv)\|² e^{−\|v\|} dv + O(1)`), e.g. Cauchy on discs plus the functional equation, or a Gabriel-type convexity theorem | todo | 400–700 |
| b8 | Assembly: `δ = η/(2(1+B))` | todo | 200 |
| | **total** | | **≈ 4,000–6,000** |

A cheaper **conditional** milestone: steps b5–b8 with SCS(η, B) taken as a named hypothesis class
(`ShiftedConvolutionBound η B`). That gives `|L(Δ,6+it)| ≪ t^{1/2−η/(2(1+B))+ε}`. It is about
2,000–2,700 lines. The hypothesis is a standard theorem (Good; Selberg–Weil; DFI δ-method), not a
restatement of the conclusion. In particular a wrong exponent would not follow from it.

Route (a), fallback, given the twisted functional equation:

| # | Step | Est. lines |
|---|---|---|
| a1 | Phragmén–Lindelöf convexity for `L(Δ,a/q,s)`, uniform in `q` (adapt `HeckeConvexGeneral`) | 400–600 |
| a2 | Smooth Voronoi formula with a `J_{11}` Hankel kernel (Mellin–Barnes, contour shift; adapt `TauPartialSumsSharp/Dual`) | 800–1200 |
| a3 | Bessel-transform bounds and stationary phase with main term and uniform error (extend `KernelPhase`) | 1500–2500 |
| a4 | Farey dissection, or Aggarwal's simple δ (Poisson via Mathlib, Cauchy–Schwarz) | 800–1500 |
| a5 | AFE (= b5) and assembly | 800–1100 |
| | **total** | **≈ 4,500–7,000** |

A cheap corollary, not done: block partial summation from `wilton_bound` gives
`Σ_{n≤x} τ(n) n^{−it} ≪ (1+|t|)^{1/2} x⁶ log x`. That is about 300 lines. It is convexity
strength, nontrivial only for `x ≥ t^{1+ε}`, so it was skipped.

## 6. Why `[DeligneBound]` does not help

The routes above use coefficient sizes only on average, through Rankin's `Σ_{n≤N} |λ(n)|² ≍ N`,
which is already unconditional. Pointwise bounds `|λ(n)| ≤ d(n)` would only remove `N^ε` losses in
step a4 or b6. The obstruction is cancellation in `Σ λ(n) n^{−it}` at length `≍ t`. That
cancellation is a statement about the oscillation of `n^{−it}` against GL(2) automorphy: Voronoi,
or shifted sums. It is not about the size of `λ`. So a "conditional on Deligne" version would be
no shorter.

## 7. Literature

* J. R. Wilton, *A note on Ramanujan's arithmetical function τ(n)*, Proc. Cambridge Philos. Soc.
  25 (1929): `Σ_{n≤x} τ(n) e(nα) ≪ x⁶ log x`.
* A. Selberg, *On the estimation of Fourier coefficients of modular forms*, Proc. Sympos. Pure Math.
  8 (1965): Poincaré series, Kloosterman zeta, Weil ⇒ `3/4`.
* A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29 (1982):
  mean square with `O((T log T)^{2/3})` error ⇒ `L(f,k/2+it) ≪ t^{1/3}(log t)^{5/6}`.
* M. Jutila, *Lectures on a Method in the Theory of Exponential Sums*, Tata/Springer (1987):
  transformation formulae and `t^{1/3+ε}` by Voronoi, Farey arcs and stationary phase.
* T. Meurman, J. reine angew. Math. 384 (1988): extension to Maass forms.
* A. R. Booker, M. B. Milinovich, N. Ng, *Subconvexity for modular form L-functions in the t
  aspect*, Adv. Math. 341 (2019): an explicit modification of Jutila's method (as I recall it).
* K. Aggarwal, *Weyl bound for GL(2) in t-aspect via a simple delta method*, J. Number Theory
  (2020); K. Aggarwal, S. K. Singh, *t-aspect subconvexity for GL(2) L-functions* (2017 preprint).
* W. Duke, J. Friedlander, H. Iwaniec, *A quadratic divisor problem*, Invent. Math. 115 (1994):
  the δ-method, an alternative proof of SCS from Voronoi + Weil.

Citations are from memory and were not checked against the papers in this session. The exponent
claims in §1 and §2 are standard. The specific constant `B` in SCS(1/4, B) should be checked
against Selberg 1965 or Iwaniec, *Spectral Methods*, Ch. 3, before step b4 is formalized.
