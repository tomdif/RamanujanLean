# Arithmetic side of Selberg's mollifier for L(Δ,s)

> **Current status (2026-11-12).** The zero-free and cancellation steps are now available in [SYM2_ZERO_FREE](SYM2_ZERO_FREE.md) and [SELBERG_DELANGE](SELBERG_DELANGE.md). The quadratic-form and positive-proportion chain is complete under `DeligneBound` alone; see [HAFNER_PROPORTION](HAFNER_PROPORTION.md).
> Earlier gap lists below describe the original method or checkpoint.

Module: `RamanujanTau/SelbergCoeffs/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.SelbergCoeffs.Main` (exit 0, about 1.1k lines).

* Every headline prints `[propext, Classical.choice, Quot.sound]`.
* There is no `sorry`, no new axiom and no `native_decide`.
* `DeligneBound` enters only as an explicit instance argument `[DeligneBound]`.

This is milestone 3 of `docs/HAFNER_PROPORTION.md`. Only part of it is done: the coefficients,
their bounds, Selberg's α²-lemma, and the structure of the quadratic form. **The bound ≪ 1/log y
for the diagonal quadratic form of (MV2) is not proved** (see §4).

## 1. Exact choices (normalization)

* λ(n) = τ(n) n^{−11/2}, so L(Δ,s) = Σ λ(n) n^{−s} = ∏_p (1 − λ(p)p^{−s} + p^{−2s})^{−1}. In the
  repo's variable this is s_repo = s + 11/2, so the critical line Re s = 1/2 is Re s_repo = 6.
* **α(n)**, the coefficients of L(Δ,s)^{−1/2} (`Global.alpha`):
  * α is multiplicative.
  * α(p^k) = `alphaLoc (λ(p)) k`, the k-th coefficient of (1 − λ(p)X + X²)^{1/2}.
  * Construction: write 1 − lX + X² = (1 − aX)(1 − bX) with a + b = l and ab = 1. Then
    (1 − aX)^{1/2} = S(aX/4), where S(X) = √(1−4X) = 1 − 2X·C(X) and C is Mathlib's Catalan
    series.
  * The coefficients do not depend on which pair (a, b) is chosen, and they are real. This holds
    because square roots with constant term 1 are unique in the domain ℂ⟦X⟧ (`sqrt_unique`).
  * First values: α(p) = −λ(p)/2 and α(p²) = 1/2 − λ(p)²/8.
* **Selberg's mollifier** (`Mollifier.bSel`) is

      b(n) = α(n) (1 − log n / log y)  for 1 ≤ n ≤ y,      b(n) = 0 otherwise,      y = ⌊T^θ⌋.

  This is Selberg's original choice (Titchmarsh §10.9) carried over to Δ, as in Hafner (1983).
  * The analytic hypothesis `SelbergMollHyp` takes any fixed 0 < θ ≤ 1/12.
  * The bound θ ≤ 1/12 makes the size window y^{2+2η} ≤ T^{1/4} of `SelbergHyp` hold both for
    η = 0 (Deligne) and for η = 1/2 (no Deligne).
  * With Deligne alone, θ ≤ 1/8 would do.

## 2. What is proved

Evidence levels: (1) Lean, axiom-clean; (2) Lean, conditional on a named class or hypothesis;
(3) paper only; (4) numerics.

| statement | Lean name | level |
|---|---|---|
| (Σ_k α(p^k)X^k)² = 1 − λ(p)X + X², coefficientwise | `alphaLoc_sq_sum` | 1 |
| α ∗ α = μ_Δ, where μ_Δ(p^k) = 1, −λ(p), 1, 0, 0, … are the coefficients of L^{−1} | `alpha_mul_alpha` | 1 |
| λ ∗ μ_Δ = δ (Hecke relations `uu_rec`) | `lamN_mul_muD` | 1 |
| **λ ∗ α ∗ α = δ**, i.e. α really is L^{−1/2} | `lamN_mul_alpha_mul_alpha` | 1 |
| \|α(p^k)\| ≤ R^k for any Satake pair with ‖a‖, ‖b‖ ≤ R | `abs_alphaLoc_le_pow` | 1 |
| if λ(p)² ≤ 4, then \|α(p^k)\| ≤ 1 for **all** k | `abs_alphaLoc_le_one` | 1 |
| **\|α(n)\| ≤ 1 for all n** | `abs_alpha_le_one [DeligneBound]` | 2 |
| **α(n)² ≤ n, so \|α(n)\| ≤ n^{1/2}, with no Deligne** | `alpha_sq_le_self`, `abs_alpha_le_sqrt` | 1 |
| b(1) = 1; \|b(n)\| ≤ \|α(n)\| | `bSel_one`, `norm_bSel_le_abs_alpha` | 1 |
| \|b(n)\| ≤ 1·n^0 | `norm_bSel_le_one [DeligneBound]` | 2 |
| \|b(n)\| ≤ 1·n^{1/2} | `norm_bSel_le_sqrt` | 1 |
| `SelbergMollHyp` ⇒ `SelbergHyp` (β = 1, η = 0) | `selbergHyp_of_moll [DeligneBound]` | 2 |
| `SelbergMollHyp` ⇒ `SelbergHyp` (β = 1, η = 1/2) | `selbergHyp_of_moll_uncond` | 1 |
| `SelbergMollHyp` ⇒ N₀(3T) ≥ c·N(3T) | `tauL_positive_proportion_of_moll` | 2 (on `SelbergMollHyp`) |
| R(σ) = Σλ(n)²n^{−σ} ≤ Kσ/(σ−1) for σ > 1 (Abel summation of Rankin's Σ_{n≤x}λ(n)² ≪ x) | `rs_real_le` | 1 |
| **Selberg's lemma: Σ_{n≤N} α(n)²/n ≤ C(log N + 1)^{1/4}** | `sum_alpha_sq_div_le [DeligneBound]` | 2 |
| Σ_{h,k≤Y} x_h x_k/[h,k] = Σ_{d≤Y} φ(d)(Σ_{h≤Y, d\|h} x_h/h)², which is ≥ 0 | `selberg_diag`, `selberg_form_nonneg` | 1 |
| b₀ = α·1_{[1,y]} gives (λ ∗ b₀ ∗ b₀)(N) = δ(N) for all N ≤ y | `lamN_mul_trunc_mul_trunc` | 1 |

The checked formulas were also verified numerically (level 4):

* the local Rankin–Selberg twist ρ_p(s;1) = λ(p)/(1 + p^{−s}) used in §3;
* α(p²) = 1/2 − l²/8.

### Answers to the coefficient-bound questions

* **Under Deligne:** \|α(n)\| ≤ 1, which is stronger than d(n).
  * The majorant of Σ_k α(p^k)X^k is (2 − √(1−X))².
  * Its coefficients are 1, 1, and then 8C_{k−1}/4^k ≤ 1/2 for k ≥ 2, where
    (k)C_{k−1} = centralBinom(k−1) ≤ 4^{k−1}.
* **Without Deligne:** \|α(p^k)\| ≤ ‖a_p‖^k, where a_p is the larger Satake parameter.
  * The repo's `EdgeNonvanishing.alpha_sq_le` gives ‖a_p‖² ≤ p, using only Rankin's linear bound.
    Hence α(n)² ≤ n.
  * Any pointwise bound \|λ(p)\| ≤ Cp^δ gives ‖a_p‖ ≤ max(1, \|λ(p)\|)-type bounds through
    `abs_alphaLoc_le_pow`.
  * The repo has no pointwise exponent below 1/2 for the Satake parameter itself. So
    \|α(n)\| ≤ n^{1/2} is what we have unconditionally. It is enough for the size clauses of
    `SelbergHyp`, since η = 1/2 ≤ 1.
  * It is **not** enough for the mean-value estimates: there the prime-power terms Σ_k α(p^k)²p^{−k}
    diverge without Deligne. Every moment computation in §3 below assumes \|α(p^k)\| ≤ 1.
* Rankin–Selberg *averages* control the primes, through Σ_p λ(p)²p^{−σ}. They do not control the
  higher prime powers. Averaging over p of the k ≥ 2 terms would need Σ_p ‖a_p‖^{2k}p^{−k} < ∞,
  which is Ramanujan on average for Sym^k. Not attempted.

## 3. The quadratic form in the diagonal of (MV2) (level 3, paper)

Notation: M(s)² = Σ_{n≤y²} c(n)n^{−s} with c = b ∗ b (real). On the line we use the repo's
`HeckeAFE3.tauL_normSq_afe`:

    |L(6+it)|² = 2 Σ_{m,n} λ(m)λ(n)(mn)^{−1/2}(n/m)^{it} W_t(4π²mn),
    |M²(6+it)|² = Σ_{h,k} c(h)c(k)(hk)^{−1/2}(k/h)^{it}.

**Where the diagonal comes from.** Integrate over t ∈ [T, 3T]. The diagonal is nk = mh. Put
g = (h,k), h = gh₁, k = gk₁. Then m = k₁r and n = h₁r, and √(hk)·√(mn) = r·[h,k]. So

    Diag(T) = 2 Σ_{h,k≤y²} c(h)c(k)/[h,k] · Σ_r λ(h₁r)λ(k₁r)/r · ∫_T^{3T} W_t(4π²h₁k₁r²) dt.

This is the "Rankin–Selberg-weighted" form.

**Evaluating the r-sum.** The Dirichlet series Σ_r λ(h₁r)λ(k₁r)r^{−s} equals
R(s)·∏_{p^a‖h₁k₁} ρ_p(s;a), where R(s) = Σλ(n)²n^{−s} = ζ(s)L(Sym²Δ,s)/ζ(2s). The local factor is

    ρ_p(s;a) = Σ_j λ(p^{j+a})λ(p^j)p^{−js} / Σ_j λ(p^j)²p^{−js},   ρ_p(s;1) = λ(p)/(1+p^{−s}).

Shift the Mellin contour of W_t. The double pole at w = 0 gives

    Diag(T) = 2r₀ ∫_T^{3T} Q_t dt + (off-diagonal of the error),
    Q_t = Σ_{h,k} c(h)c(k)/[h,k] · ρ(h₁)ρ(k₁) · [log(t/2π) − ½ log(h₁k₁) + γ_Δ + (ρ'/ρ)(h₁) + (ρ'/ρ)(k₁)].

Here r₀ = Res_{s=1}R = L(1,Sym²Δ)/ζ(2) (the repo's `rsc`/`c0`), and ρ(m) = ∏_{p^a‖m}ρ_p(1;a).

**What (MV2) needs.** It needs Q_t ≪ 1 uniformly for t ∈ [T, 3T]. Since log t ≍ log y, the
essential estimate is

    (QF)   Q⁰(c) := Σ_{h,k≤y²} c(h)c(k)ρ(h/(h,k))ρ(k/(h,k)) / [h,k]  ≪  1/log y,

together with the companion log-weighted forms, which must be ≪ 1. Without the ρ weights,
Q⁰ is the form Σc(h)c(k)/[h,k] that `selberg_diag` diagonalizes. With them, it diagonalizes in the
same way with a multiplicative gcd-weight w(g) = g/ρ-type in place of g, giving
Σ_d (μ ∗ w)(d)(Σ_{d|h} c(h)ρ(h)/h)². (This needs care at primes with λ(p) = 0. Not formalized.)

**Why (QF) should hold.** c ≈ the coefficients μ_Δ of L^{−1}, smoothed by the
(1 − log/log y) weights. Then Σ_h c(h)ρ(h)h^{−1−s} ≈ ∏_p(1 − λ(p)²p^{−1−s} + …) ≈ 1/R(1+s),
which vanishes to first order at s = 0. Selberg's smoothing turns that zero into the saving
1/log y.

Making this rigorous needs the analytic behaviour of R(1+s)^{−1}L-type products near s = 0 with
a smooth y^s/(s² log y) kernel:

* a contour shift slightly to the left of Re s = 0. This needs a zero-free region (or at least
  polynomial bounds) for ζ·L(Sym²Δ) near Re s = 1. The repo has non-vanishing *on* the line
  (`EdgeNonvanishing`), but no region; **or**
* Selberg's elementary route (Titchmarsh §10.13–10.16) through prime sums. For Δ that needs
  Mertens-type asymptotics Σ_{p≤x}λ(p)²/p = log log x + c + o(1), i.e. an error term in
  `rs_prime_PNT`, which the repo only has as o(x).

`sum_alpha_sq_div_le` is the size input both routes need: Σ α²/n ≪ (log y)^{1/4}, the analogue of
the corresponding ζ-lemma in Titchmarsh §10.13.

## 4. Gaps (honest)

1. **(QF) is not proved**, neither as an asymptotic nor as an upper bound. Neither are its
   log-weighted companions. This is the core of the diagonal of (MV2).
2. The reduction "Diag(T) = 2r₀∫Q_t + error" (§3) is paper only. It needs:
   * a Mellin analysis of the repo's `Wsq` (compare `GoodSecondTerm.diag_err_D`, which does the
     h = k = 1 case);
   * the identity of the local factors ρ_p(s;a) (verified numerically for a = 1);
   * Hecke multiplicativity λ(h₁r)λ(k₁r).
3. Selberg's lemma is proved only as an upper bound with the sharp exponent 1/4, and only under
   Deligne. The lower bound ≫ (log N)^{1/4} needs Σ_{p≤x}λ(p)²p^{−σ} ≥ log(1/(σ−1)) − C, i.e. a
   lower bound on R(σ)(σ−1). That follows from the repo's RS asymptotics, but is not done.
4. Deligne is used for \|α(p^k)\| ≤ 1 (all moment sums) and for λ(p)² ≤ 4 (the local
   inequality (1 + u/4)⁴ ≤ (1 + u)(1 + 3u²/8), with u ≤ 4/p). Without Deligne only the size
   clauses are available (η = 1/2).
5. The off-diagonal of (MV2) (two-sided SCS) and (SK) are untouched (milestones 2 and 4).

Estimate to finish milestone 3 in the strong sense (QF), at level 2 on `[DeligneBound]`:

* a zero-free-region-free route via Selberg's elementary method, given a Mertens error term for
  λ(p)²: about 1.5–2.5k more lines;
* the Mertens error term itself, from `RankinError`'s O(x^{3/5}) plus a prime-power sieve:
  about 0.5–1k more lines.

## 5. Literature

- A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid. Akad. Oslo (1942).
- E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§10.9–10.22.
- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983) 21–37.
- R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n)…*, Proc. Camb. Phil.
  Soc. 35 (1939); A. Selberg, *Bemerkungen über eine Dirichletsche Reihe…* (1940).

## 6. 2026-11-06: Rankin–Selberg Mertens theorems (`RamanujanTau/SelbergCoeffs2/`)

Build: `nice -n 10 lake build RamanujanTau.SelbergCoeffs2.Main` (exit 0, about 920 lines).

* All 10 headlines print `[propext, Classical.choice, Quot.sound]`.
* There is no sorry, no new axiom and no native_decide.
* **Everything below is level 1 and unconditional: `DeligneBound` is not used.**

| statement | Lean name |
|---|---|
| λ(n)² log n = Σ_{dm=n} ΛR(d)λ(m)², where ΛR = vR − 2Λ(√n)·1_{n=□} | `rsb_mul_log` (complex form `logMul_rsB_eq`) |
| Σ_{n≤N} \|ΛR(n)\| ≤ BN | `cheb_LamR` |
| Σ_{n not prime} \|ΛR(n)\|/n < ∞ | `summable_LamR_nonprime` |
| ΛR(p) = λ(p)² log p | `LamR_prime` |
| \|Σ_{n≤N} ΛR(n)/n − log N\| ≤ E for N ≥ 1 | `mertens1_LamR` |
| **\|Σ_{p≤N} λ(p)² log p/p − log N\| ≤ E for N ≥ 1** | `mertens1_prime` |
| **Σ_{p≤N} λ(p)²/p − log log N → c_Δ** | `mertens2`, with `cMertens = 1 + Σ_k h_k` |
| \|Σ_{p≤N} λ(p)²/p − log log N\| ≤ C for all N | `mertens2_bound` |

### Route (Mertens' 1874 argument)

1. **Log-derivative identity.**
   * R(s) = exp(Σ cR(n)n^{−s})/ζ(2s) holds by the repo's `HH_exp` and `HH_eq`.
   * Differentiating gives −R′/R = L(vR, s) − 2L(Λ, 2s).
   * Coefficients are then compared with Mathlib's `LSeries.eq_of_LSeries_eventually_eq`.
2. **Summation by parts.**
   * Put S(N) = Σ_{n≤N} λ(n)² log n and F(N) = Σ_{n≤N} λ(n)². The repo's `rs_partial`
     (`RankinExact`) gives F(N) = cN + O(N^{3/5}).
   * Summation by parts (`abel_Ioc`) gives S(N) = F(N) log N + O(N) = cN log N + O(N).
3. **Convolution.**
   * Writing S(N) = Σ_d ΛR(d)F(N/d) gives S(N) = cN Σ_{d≤N} ΛR(d)/d + O(N^{3/5}Σ\|ΛR(d)\|d^{−3/5}).
   * The last sum is ≪ N^{2/5}, by Chebyshev and the majorization lemma `sum_mul_le_of_partial`.
   * The constant is positive: c > 0 by `RankinError.petNormSq_pos`.
4. **Mertens II.** Summation by parts against 1/log k. The remainder terms h_k satisfy
   \|h_k\| ≤ 1/(k² log²2) + E(1/log k − 1/log(k+1)), which is summable.

**Prime powers without Deligne.** The terms Σ_{p, k≥2} vR(p^k)/p^k < ∞ come from the repo's
`summable_vR_nonprime`. Its input is the unconditional bound \|τ(p^k)\| p^{−11k/2} ≪ p^{11k/40}
(`TauPNTUncond.weil_uu`, Rankin plus the Satake parameters). The square part 2Λ(√n) is trivial.
So **no prime-power term needs `DeligneBound`.**

**Not done (cheap follow-up).** The explicit rate Σ_{p≤N}λ(p)²/p = log log N + c_Δ + O(1/log N).
All the ingredients are present (tail of Σh_k ≪ 1/N + E/log N, and \|PP(N)/log(N+1) − 1\| ≪ 1/log N).
Only the tsum-tail bookkeeping is missing, about 150 lines.

### Task 2: the Q⁰ bound for (MV2). NOT DONE. This corrects §3–§4.

§3/§4 above said that Selberg's elementary route needs only a Mertens error term. **That was too
optimistic.** Mertens is now proved, with O(1) error at the log-density level, and the analysis
below shows what (QF) actually needs.

**Structure of the form.** Q⁰(c) = Σ_d w(d)·y_d² with y_d = Σ_{d\|h} c(h)ρ(h/d)/h-type sums,
where c = b∗b and b = α·(1 − log n/log y). The generating function of c·ρ is

    Σ_{a,b} α(a)α(b)ρ(ab) a^{−1−s₁} b^{−1−s₂} ≈ R(1+s₁)^{−1/2} R(1+s₂)^{−1/2} · H(s₁,s₂).

Here H is holomorphic near 0 under Deligne. The factor R(1+s)^{−1/2} ~ (s/r₀)^{1/2} has a
**branch point** at s = 0, and (QF) needs the sharp saving (log y)^{−1/2} from *each* factor.

**What that saving requires.** Either

* (a) a **zero-free region** for ζ(s)L(Sym²Δ,s) to the left of Re s = 1, so that R^{−1/2} is
  defined there, followed by Selberg–Delange contour integration. This is Selberg's actual
  ζ-argument (Titchmarsh §10.13 uses ζ ≠ 0 in σ ≥ 1 − A/log t). The repo has only non-vanishing
  *on* Re s = 1 (`Lsym2_ne_zero_edge`, `Rcont_ne_zero_edge`); **or**
* (b) a real-variable **Hall–Tenenbaum / Halász log-density mean-value theorem**: for real
  multiplicative f with Σ_{p≤x} f(p)/p = −½ log log x + O(1), one has Σ_{n≤x} f(n)/n ≪ (log x)^{−1/2}.
  * Applied to f = α·ρ and its log-weighted variants.
  * This needs exactly `mertens2_bound` (now available) and \|f(p^k)\| ≤ 1-type bounds
    (`DeligneBound`).
  * It still needs the two-variable smoothing analysis and the companion forms.

Route (b) is the realistic Lean route, conditional on `[DeligneBound]`. It would add a
Hall–Tenenbaum-type theorem plus the mollifier bookkeeping: estimated 3–5k lines. A simpler sanity
target on the way is the two-sided Selberg lemma Σ_{n≤N}α(n)²/n ≍ (log N)^{1/4}: the lower bound
should follow from `mertens2_bound` by a standard truncated-Euler-product argument (not checked),
estimated 0.3–0.5k lines.

## 7. 2026-11-06 (later): Mertens rate, two-sided Selberg lemma, logarithmic mean values (`RamanujanTau/SelbergCoeffs3/`)

Build: `nice -n 10 lake build RamanujanTau.SelbergCoeffs3.Main` (exit 0, about 700 lines).

* All 6 headlines print `[propext, Classical.choice, Quot.sound]`.
* There is no sorry, no new axiom and no native_decide.

| statement | Lean name | level |
|---|---|---|
| \|Σ_{p≤N} λ(p)²/p − log log N − c_Δ\| ≤ C/log N for N ≥ 2 | `mertens2_rate` | 1 (unconditional) |
| f ≥ 0 multiplicative, f(p^k) ≤ B, Σ_{p≤M} f(p)/p ≤ κ log log M + C ⇒ Σ_{n≤N} f(n)/n ≤ e^{C+2B}(log N)^κ | `logmean_upper` | 1 |
| the same for real signed f, with \|f\| in the hypotheses (bounds \|Σ f(n)/n\|; no cancellation) | `logmean_upper_abs` | 1 |
| f ≥ 0, κ ≥ 0, f(p) ≤ 2, Σ_{p≤M} f(p)log p/p ≤ A log M, Σ_{p≤M} f(p)/p ≥ κ log log M − C ⇒ Σ_{n≤N} f(n)/n ≥ c(log N)^κ | `logmean_lower` | 1 |
| **c(log N)^{1/4} ≤ Σ_{n≤N} α(n)²/n ≤ C(log N)^{1/4}** | `selberg_two_sided [DeligneBound]` | 2 |

### Proofs in brief

* **Mertens rate.** Use `TT_decomp`. The tail Σ_{k>N} h_k is bounded through finite telescoping
  sums (1/k² ≤ 1/(k−1) − 1/k, and w_k − w_{k+1}) followed by a limit. Then
  0 ≤ log log(N+1) − log log N ≤ 1/log N, and \|P(N) − log(N+1)\| ≤ E + 1.
* **Upper bound.** Mathlib's `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
  needs only *local* summability. Each local factor satisfies 1 + f(p)/p + 2B/p² ≤ exp(…).
* **Lower bound.** Restrict to squarefree numbers built from the primes ≤ M, with N ≥ M^K. The
  identity ∏(1+u) = Σ_{S⊆P}∏_S u is Mathlib's `prod_one_add`, and S ↦ ∏S is injective by
  `Nat.primeFactors_prod`.
  * The tail ∏S > N is removed by Rankin's trick with δ = 1/log M. Using p^δ − 1 ≤ e·δ log p
    gives tail ≤ e^{−K+eA}·∏(1+u) ≤ ½∏(1+u).
  * Then 1 + u ≥ e^{u−u²} on [0,1] (from `Real.exp_bound'`).
  * Finally choose M = `Nat.findGreatest (· ^ K ≤ N) N`.
* **The Selberg lemma.** f = α², κ = 1/4, with the inputs `mertens1_prime` and `mertens2_bound`.
  Deligne enters only through \|α(p^k)\| ≤ 1. The upper bound now has the clean shape
  (log N)^{1/4}, improving the earlier (log N + 1)^{1/4} in `sum_alpha_sq_div_le`.

### Route (b) is retracted, and the Q⁰ status

§6 proposed a Hall–Tenenbaum-type theorem: for real f with Σ_{p≤x} f(p)/p = κ log log x + O(1)
and κ < 0, Σ_{n≤x} f(n)/n ≪ (log x)^κ. **This should not be expected to follow from
Mertens-type hypotheses.**

* Take f = μ, so κ = −1. The statement would give Σ_{n≤x} μ(n)/n ≪ 1/log x. That is a
  prime-number-theorem-with-error statement, and the hypotheses are only Mertens-strength.
  * In Beurling generalized-integer systems, Chebyshev/Mertens-type bounds can hold while the PNT
    fails. I recall this but have not checked it in detail.
  * For natural means, the Hall–Tenenbaum constant K = 0.3286 < 1 shows that real signed f only
    gets a fraction of the full saving.
* What *is* proved is the sharp theorem for f ≥ 0 (both directions), plus the trivial signed
  bound (`logmean_upper_abs`), which gives no saving from cancellation.
* Consequence for (QF), the bound Q⁰ ≪ 1/log y: the needed (log y)^{−1/2} savings come from
  cancellation in the coefficients of R(1+s)^{−1/2} (branch point at s = 0). They require
  **route (a)**: a zero-free region for ζ·L(Sym²Δ) left of Re s = 1, then Selberg–Delange
  contour integration.
  * The repo has only edge non-vanishing.
  * The non-negative theorems proved here supply all the *size* inputs (Σα²/n ≍ (log)^{1/4},
    Mertens with rate). The cancellation input is the remaining gap.
* Rough cost of route (a), level 2 on `[DeligneBound]`:
  * a classical zero-free region for L(Sym²Δ) (de la Vallée Poussin type, using
    L(Sym²×Sym²)-positivity): about 2–4k lines;
  * Selberg–Delange with a Hankel contour: about 2–3k lines;
  * the mollifier bookkeeping: about 1–2k lines.
