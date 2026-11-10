# `HafnerBridge.QFHyp`: proof chain and Lean checkpoint (2026-11-06)

Lean: `RamanujanTau/QFProof/` (`JBound`, `Comb`, `Reduction`, `Local`, `Chol`, `LocalChol`, `Main`; ~950 lines). No sorry, no new axiom, no
native_decide; every headline prints `[propext, Classical.choice, Quot.sound]`.

    nice -n 10 lake build RamanujanTau.QFProof.Main      # exit 0

**Status.** `QFHyp` is reduced, in Lean, to seven named hypotheses: three exact identities, one
canonical factorization pair, and three non-negative Euler-product size bounds (`qfHyp_of`, level 2 on
them). The whole Selberg–Delange cancellation is discharged by one level-1 lemma (`J_bound`). The
identities are verified numerically (level 4); the size bounds are proved on paper (level 3, under
Deligne) and checked numerically for small `y`. **`QFHyp` itself is not yet proved.**

This also **removes two items of the plan in `SELBERG_DELANGE.md` §8**:

* *Uniformity of `logmean_LSD` in `d`* is **not needed**. All `d`-dependence is moved into
  absolutely convergent local factors, and the only Selberg–Delange input is for the single function
  `fR` (coefficients of `R^{−1/2}`), which is already proved.
* *Titchmarsh's smoothing combinatorics* reduce to one exact identity (`smooth_two`). No asymptotic
  main term, no constant `C₁`, no Taylor expansion and no `log log` bookkeeping is needed. Each `J`
  only has to be `≪ (log)^{1/2}`.

## 1. The kernel and its exact diagonalization

Write `X = 1/p` and `λ_j = λ(p^j)`, with `λ_{−1} = λ_{−2} = 0`. The Hecke relation is
`λ_{j+2} = λλ_{j+1} − λ_j`.

**(1a) Closed forms of the local factors** (level 4, checked against the `tsum` definitions of
`QF.lean` to `10^{−15}` for p = 2, 3, 5 and a = 1, 2, 3). **Lean, level 1:** `rhoP_one`, `rhoP_add_two`
(`QFProof/Local.lean`, from the `tsum` definitions and Hecke `uu_rec`). The `ρ'` formula is still TODO:

    ρ_p(a)  = (λ_a − X λ_{a−2}) / (1 + X)                       (a ≥ 1),   ρ_p(0) = 1,
    ρ'_p(a) = X log p · (λ_a + λ_{a−2}) / (1 + X)²             (a ≥ 1),   ρ'_p(0) = 0.

*Proof (paper).* Use `λ_{a+j} = λ_aλ_j − λ_{a−1}λ_{j−1}` (Hecke). Then
`N(a) = λ_a D − λ_{a−1} X N(1)`. Shifting the Hecke recursion inside `N(1)` gives
`N(1)(1+X) = λD`. So `N(a)/D = (λ_a(1+X) − Xλλ_{a−1})/(1+X) = (λ_a − Xλ_{a−2})/(1+X)`. The same
argument with `X = p^{−s}`, differentiated at `s = 1`, gives `ρ'`.

**(1b) Local kernel.** `K(h,k) := ρ(h₁)ρ(k₁)/[h,k] = Π_p K_p(a_p,b_p)`, where
`K_p(a,b) = X^{max(a,b)} ρ_p(|a−b|)`. The local kernel is a Gram matrix:
`K_p(a,b) D_p = Σ_{r ≥ max(a,b)} X^r λ_{r−a} λ_{r−b}`. (Re-index `r = max + j`.)

**(1c) Explicit LDLᵀ** (found symbolically). **Lean, level 1:** `chol_loc` (abstract Hecke sequences) and
`chol_rhoP` (the actual `rhoP`), in `QFProof/Chol.lean` and `LocalChol.lean`. For every prime p and every a, b ≥ 0:

    K_p(a,b) = Σ_{e ≤ min(a,b)} W_p(e) L_p(a,e) L_p(b,e),
    W_p(0) = 1,   W_p(1) = X((1+X)² − Xλ²)/(1+X)²,   W_p(e) = X^e (1−X)((1+X)² − Xλ²)/(1+X)   (e ≥ 2),
    L_p(a,0) = X^a ρ_p(a),   L_p(a,e) = X^{a−e} λ_{a−e}   (1 ≤ e ≤ a),   L_p(a,e) = 0 (a < e).

The columns e ≥ 1 are Toeplitz. The reason is that `v_a − λv_{a+1} + v_{a+2} = X^{a/2}e_a` for the
Gram vectors `v_a = (X^{r/2}λ_{r−a})_r`, so Gram–Schmidt becomes stationary after the first two
columns. Hence, globally (with `d | h`, `h = d m`, `m = m₁m₂`, where `m₁` is supported on the primes
of `d` and `(m₂,d) = 1`):

    K(h,k) = Σ_{d | (h,k)} W(d) U(h,d) U(k,d),   W(d) = Π_{p^e∥d} W_p(e),
    U(h,d) = 1_{d|h} · λ(m₁)/m₁ · ρ(m₂)/m₂.                                   (QDecomp)

Checked against the definition of `Q0` in `QF.lean`: `Q0` computed directly equals `Σ_d W(d)y_d²`
to `10^{−15}` for y = 6, 10, 16, 30, 60.

**(1d) The companion kernel is a derivative.** Put `K^{[s]}(h,k) = [h,k]^{−s}ρ(h₁,s)ρ(k₁,s)`; its
LDLᵀ is (1c) with `X → p^{−s}`. Since `[h,k]²/(h₁k₁) = hk`,

    K₁(h,k) = γ_R/r₀ · K + ∂_s|_{s=1} [ (hk)^{(s−1)/2} K^{[s]}(h,k) ].

The product rule gives

    K₁(h,k) = Σ_{d|(h,k)} [ W₁(d) U(h,d)U(k,d) + W(d)(V(h,d)U(k,d) + U(h,d)V(k,d)) ],     (QDecomp1)
    W₁ = γ_R/r₀ · W + ∂_s W^{[s]},
    V(h,d) = Σ_p (½ a_p log p · L_p − log p · X ∂_X L_p)(a_p,e_p) · Π_{q≠p} L_q(a_q,e_q).

Checked against the `ρ₁`-definition of `Q1` in `QF.lean` (level 4; agreement 10⁻¹¹ with finite
differences, for 8 random pairs h, k ≤ 800).

## 2. Diagonal form (Lean, level 1 given QDecomp)

`Q0_diag`, `Q1_diag`:

    Q⁰(y) = Σ_{d≤y²} W(d) y_d²,       Q¹(y) = Σ_{d≤y²} (W₁(d) y_d² + 2W(d) y_d z_d),
    y_d = Σ_{h≤y²} c(h)U(h,d),        z_d = Σ_{h≤y²} c(h)V(h,d).

## 3. Two-variable factorization through `fR` (QFactor)

Since `c = β∗β` and β is supported on [1, y],

    y_d = Σ_{n₁,n₂≤y} β(n₁)β(n₂) U(n₁n₂,d)                              (`yv_eq`, Lean).

`G_d(n₁,n₂) := α(n₁)α(n₂)U(n₁n₂,d)` is a multiplicative function of the pair. Let `F = fR/n`, with
Dirichlet inverse `F⁻¹ = fR⁻¹/n` (`fR⁻¹` = coefficients of `R^{1/2}` = `recF(+ΛR/2)`). Define
`Γ_d := G_d ⋆ (F⁻¹ ⊗ F⁻¹)`, a two-variable Dirichlet convolution. Then by construction

    α(n₁)α(n₂)U(n₁n₂,d) = Σ_{u₁|n₁,u₂|n₂} Γ_d(u₁,u₂) F(n₁/u₁) F(n₂/u₂).             (QFactor)

Do the same for `V` with `Γ'_d := (α⊗α·V) ⋆ (F⁻¹⊗F⁻¹)`. Because `F` does not depend on s,
`Γ'_d = ∂_s Γ_d^{[s]}`.

## 4. The smoothing identity and the only cancellation input (Lean, level 1)

`β(n) = α(n) log(y/n)/log y`. Substituting `n_i = u_i m_i` gives, exactly (`smooth_two`, `yv_smooth`):

    y_d = (log y)^{−2} Σ_{u₁,u₂≤y} Γ_d(u₁,u₂) J(y/u₁) J(y/u₂),   J(x) = Σ_{m≤x} (fR(m)/m) log(x/m).

`J_bound` (level 1, from `selberg_sum_fR`): `|J(x)| ≤ K(1 + log x)^{1/2}` for x ≥ 1. The trivial
bound is `(log x)^{3/2}`. Hence (`abs_yv_le`)

    |y_d| ≤ K²(1+log y)(log y)^{−2} · M_d(y),   M_d(y) = Σ_{u₁,u₂≤y} |Γ_d(u₁,u₂)|,

and likewise `|z_d| ≤ K²(1+log y)(log y)^{−2} M'_d(y)` with `Γ'`. **No main term and no constant are
used.** Every saving comes from `J ≪ (log)^{1/2}`.

## 5. Assembly (Lean, `Q0_bound_of`, `Q1_bound_of`, `qfHyp_of`)

Assume

    (QEuler₁)  Σ_{d≤y²} |W(d)|  M_d(y)²  ≪ log y,
    (QEuler₂)  Σ_{d≤y²} |W₁(d)| M_d(y)²  ≪ (log y)²,
    (QEuler₃)  Σ_{d≤y²} |W(d)|  M'_d(y)² ≪ (log y)³.

Then, writing `L = log y`:

* `|Q⁰| ≤ (2K²/L)² · AL = 4K⁴A/L`.
* `|Q¹| ≤ (2K²/L)²[A₁L² + Σ|W|(LM² + M'²/L)] ≤ 4K⁴(A₀+A₁+A₂)`. This uses `2MM' ≤ LM² + M'²/L`.

## 6. Proof of the Euler bounds (paper, level 3; Deligne enters only here)

Everything is multiplicative: `Γ_d(u₁,u₂) = Π_p Γ_{p,e_p}(v_p u₁, v_p u₂)`. The local
two-variable series is

    Γ_{p,e}(x₁,x₂) = [Σ_{i,j} α_iα_j L_p(i+j,e) x₁^i x₂^j] · D_p(Xx₁)^{1/2} D_p(Xx₂)^{1/2}.

Here `α_i = α(p^i)` and `D_p(t) = Σλ_j²t^j`, so `F_p = D_p^{−1/2}`. Write `m_{p,e} = Σ_{i,j}|Γ_{p,e}(i,j)|`.

The bounds used under `DeligneBound` are:

* `|λ_j| ≤ j+1`;
* `|α_i| ≤ 1`, with majorant coefficients `1, 1, O(k^{−3/2})`;
* `|ρ_p(a)| ≤ a+1`;
* `|[t^k]D_p^{1/2}| ≤ (k+1)²`, via `|fR⁻¹| ≤ recF(|ΛR|/2)` (`abs_recF_le`) and `|ΛR(p^k)| ≤ 6 log p`.

The local masses then satisfy:

* **p ∤ d (e = 0): `m_{p,0} = 1 + O(p^{−2})`.**
  * `Γ(0,0) = 1`.
  * The first-order term cancels exactly. Since `α(p) = −λ/2`, `ρ_p(1) = λ/(1+X)` and
    `fR⁻¹(p) = λ²/2`, we get `Γ(1,0) = α(p)Xρ_p(1) + Xλ²/2 = X²λ²/(2(1+X))`.
  * Every term with `i+j ≥ 2` is `O(poly(i+j) X^{i+j})`.
  * So `C₀ := Π_p m_{p,0} < ∞` and `m_{p,0} ≥ 1`.
  * *This is the only place where `fR` must match `α·ρ` to first order at primes.*
* **p ∥ d (e = 1): `m_{p,1} ≤ |λ(p)| + C/p`.**
  * `G(0,0) = 0`, and `Γ(1,0) = Γ(0,1) = α(p)L_p(1,1) = −λ/2`.
  * The remaining terms are `O(X)`.
* **e ≥ 2: `m_{p,e} ≤ C`, uniformly in e.** The leading part is `Σ_i|α_iα_{e−i}|`, which is bounded
  by the `k^{−3/2}` decay of the majorant.
* **Pivots.**
  * `0 < W_p(1) ≤ X`, because `(1+X)² − Xλ² ≥ (1−X)² > 0`.
  * `|W_p(e)| ≤ CX^e`.
  * `|∂_sW_p(e)| ≤ C(e+1) log p · X^e`.

**(QEuler₁).** `|W(d)|M_d(∞)² ≤ C₀² f(d)/d`, where f is multiplicative and non-negative with
`f(p) = p|W_p(1)|m_{p,1}² ≤ λ(p)² + C/p` and `f(p^e) ≤ B`. `mertens2_bound` gives
`Σ_{p≤M} f(p)/p ≤ log log M + C`. Then `logmean_upper` (SelbergCoeffs3, κ = 1) gives
`Σ_{d≤y²} f(d)/d ≪ log y`. The κ must be exactly 1, and it is, because `λ(p)²` has mean 1 (Rankin).

**(QEuler₂).** `|W₁(d)| ≤ (|γ_R/r₀| + C log d)·W̃(d)`, with `W̃_p(1) = X`. Since `log d ≤ 2 log y`,
this gives `≪ (log y)²`.

**(QEuler₃).** Use `Γ'_d = Σ_p ∂Γ_{p}·Π_{q≠p}Γ_q` (product rule).

* For **p ∤ d**, `∂Γ_{p,0}(0,0) = 0` and `|∂Γ_{p,0}(1,0)| ≤ (λ²/4 + CX)X log p`. The first-order
  term does **not** cancel after differentiation.
* Because `u ≤ y`, only primes `p ≤ y` contribute, so
  `M'_d(y) ≤ M̃_d·[Σ_{p≤y}(λ²/2 + C/p) log p/p + C log d] ≪ M̃_d·log y` by `mertens1_prime`.
* Here `M̃_d` is the majorant with `m̃_{p,1} = |λ| + C/p`; for p | d, `∂m_{p,e} ≤ C(e+1) log p · m̃_{p,e}`.
* Hence `Σ|W|M'² ≪ (log y)² · Σ|W|M̃² ≪ (log y)³`.

**Numerics (level 4), from exact τ.** Γ was computed by explicit two-variable convolution with
`fR⁻¹ = D_p^{1/2}`. The ratio `Σ_{d≤y²}|W|M_d(y)² / log y` was 1.276, 1.382, 1.338, 1.318, 1.330 for
y = 6, 9, 12, 20, 30, which is flat. The ratio `Σ|W₁|M²/(log y)²` was 0.25 → 0.36, slowly rising,
consistent with `L² + O(L)`. Separately, `Q⁰·log y` was 1.41, 1.61, 1.74, 1.87, 1.99 for
y = 6, 10, 16, 30, 60. That is bounded but not yet visibly constant; at these y it is
`c + O(1/log y)`-type behaviour.

## 7. What remains (to turn level 2 into level 2-on-Deligne only)

1. **Closed forms (1a)**: the `ρ` part is done (`rhoP_one`, `rhoP_add_two`). Still to do: the `ρ'`
   formula, which needs the j-weighted `tsum`s `Np'`, `Dp'` (same method). About 150 lines.
2. **`QDecomp`, `QDecomp1`.**
   * The local LDLᵀ is done (`chol_rhoP`).
   * Remaining: `Kq`, `Kq1` as products and derivations over `p | hk`; the `prod_sum` exchange over
     `d | (h,k)`; and the s-derivative of the local identity for `QDecomp1`.
   * About 400–600 lines, unconditional.
3. **`QFactor` pair.** About 250 lines.
   * The two-variable Dirichlet convolution with `F⁻¹`.
   * `recF(ΛR/2) ∗ recF(−ΛR/2) = δ`, since log is a derivation and recF is unique.
4. **Multiplicativity of `fR`, `fR⁻¹`** and their local factors `D_p^{∓1/2}`. Uniqueness of the
   log-derivative together with `ofLocal`. About 300–500 lines.
5. **`QEuler₁₋₃`.**
   * Local mass bounds as in §6.
   * The product over primes (absolute convergence).
   * `logmean_upper`, `mertens2_bound`, `mertens1_prime`.
   * About 600–900 lines, at level 2 on `[DeligneBound]`.

Total remaining: about 1.8–2.4k lines. The end product would be `QFHyp` at level 2 on `[DeligneBound]` only.
Without Deligne, §6 fails: the prime-power local masses are not bounded, as in
`SELBERG_COEFFS.md` §2. Items 1–4 are unconditional.

## Literature

Selberg (1942); Titchmarsh §§10.9–10.16 (the ζ-case; there U(h,d) = 1_{d|h}/h and W = φ);
Hafner, Math. Ann. 264 (1983); Granville–Koukoulopoulos, Ramanujan J. 49 (2019).

---

## 2026-11-06 (later): is `QFHyp` true? Numerics to y = 5000 and the local Euler factors

**Conclusion: yes. `QFHyp`'s normalization is right.** `Q⁰·log y` converges to a constant of about
2.4–2.5. It does not grow like `log log y` or `(log y)^ε`. `Q¹` is bounded, and the bound follows
from the rigorous chain of §§4–6. Only the size of its limit is uncertain from the numerics.

### Exact computation of `Q⁰` and `Q¹`

* **Method.** A C program uses τ(p) from PARI (`ramanujantau`, nbthreads 1) and the exact
  diagonalization `Q⁰ = Σ_d W(d)y_d²`. The `y_d` are accumulated over the divisors of every `h ≤ y²`.
* **Cross-check.** At y = 30 and y = 60 it reproduces the direct double sum to all printed digits.
* `Q¹' := Q¹ − (γ_R/r₀)Q⁰` is the part that does not involve the unknown constant `γ_R/r₀`. The
  remaining piece `(γ_R/r₀)Q⁰` is `O(1/log y)` once `Q⁰` is.

| y | log y | Q⁰ | Q⁰·log y | Q¹' |
|---|---|---|---|---|
| 30 | 3.40 | 0.55001 | 1.8707 | 0.3290 |
| 60 | 4.09 | 0.48536 | 1.9872 | 0.4086 |
| 100 | 4.61 | 0.44487 | 2.0487 | 0.4629 |
| 200 | 5.30 | 0.39841 | 2.1109 | 0.5297 |
| 400 | 5.99 | 0.36031 | 2.1588 | 0.5878 |
| 800 | 6.68 | 0.32814 | 2.1935 | 0.6394 |
| 1600 | 7.38 | 0.30083 | 2.2194 | 0.6849 |
| 3200 | 8.07 | 0.27751 | 2.2398 | 0.7249 |
| 5000 | 8.52 | 0.26425 | 2.2507 | 0.7481 |

### Least-squares fits over y = 30…5000 (max residual)

| quantity | model | fitted coefficients | max residual |
|---|---|---|---|
| `Q⁰ log y` | `a + b/L + c/L²` | a = 2.445 | 2.3e−3 |
| `Q⁰ log y` | `a + b/L + c·log L/L` | a = 2.376 | 1.7e−3 |
| `Q⁰ log y` | `a + b log log y` | — | 3.9e−2 |
| `Q⁰ log y` | `a + b/√L` | — | 2.3e−2 |
| `Q¹'` | `a + b/L + c·log L/L` | a ≈ 1.49 | 5.6e−4 |
| `Q¹'` | `a + b/L + c/L²` | a ≈ 1.25 | 1.8e−3 |
| `Q¹'` | `a + b log log y` | — | 3.4e−3 |

* For `Q⁰ log y`, the `log log y` model is worse by more than an order of magnitude.
* The increments of `log(Q⁰ log y)` per doubling of y fall off as `1/L²`, not `1/L`. That rules out
  `(log y)^ε`.
* For `Q¹'` the numerics alone do not exclude slow `log log` growth. The rigorous argument below
  does exclude it.

### Why the limit is finite: the local Euler factors (level 4 for every p < 20000)

The proof of `Q⁰ ≪ 1/log y` is `Q⁰ ≤ c(y)²·Σ_{d≤y²}|W(d)|M_d(y)²` with `c(y) = K²(1+L)/L²`. The first
factor is `J_bound` (Lean, level 1). So everything hinges on `Σ_{d≤y²} f(d)/d ≪ log y` with κ
**exactly 1**: any `κ > 1` would make `Q⁰ log y` grow like `(log y)^{κ−1}`.

The local claims of §6 were computed directly from the two-variable local series, with exact τ(p), for
all 2262 primes p < 20000:

| claim | observed range |
|---|---|
| `(m_{p,0} − 1)·p²` | between 0.04 and 7.8 (bounded) |
| `(f(p) − λ(p)²)·p`, where `f(p) = p W_p(1) m_{p,1}²` | between 0.04 and 7.4 (bounded) |
| `max_{2≤e≤4} m_{p,e}` | at most 1.44, and equal to 1.000 for p > 500 |

* So `f(p) = λ(p)² + O(1/p)`. Mertens for `λ²` (`mertens2_bound`) then gives κ = 1.
* With `f(p^e) ≤ B`, `logmean_upper` gives the bound.
* `Σ_{d≤y²}|W|M²/log y` is flat at 1.28–1.38 for y = 6…30 (§6).

**Q¹.** `|Q¹| ≤ c²[S₁ + L·S₀ + S₂/L]`, with:

* `S₁ ≪ L²`, because `|W₁(d)| ≪ log d · W̃(d)` and `d ≤ y²`;
* `S₂ ≪ L³`. Every local derivative term with `(i,j) ≠ (0,0)` is `O((i+j) log p · X^{i+j})`, so
  `Σ_{p≤y} ∂m_{p,0} ≪ Σ_{p≤y} log p/p ≪ L`. No cancellation is needed here.

Both bounds use only the same κ = 1 Euler product. Hence `Q¹ = O(1)`. The upward drift of `Q¹'` in
the table is the slowly converging `O(log L/L)` correction. The upper bound is unaffected.

**Predicted constant: not computed.** The limit of `Q⁰ log y` involves `C₁⁴` from `selberg_sum_fR`, and
`C₁` is not identified (`SELBERG_DELANGE.md` §8(c)). The proof does not need it. The fitted limit is
about 2.4–2.5.

**Verdict.** `QFHyp` is consistent with all data. Its proof (§§4–6) needs only κ = 1 Euler products,
which are verified prime by prime. Formalization continues in `RamanujanTau/QFProof2/`.

### `QFProof2/` checkpoint (same day)

Build: `nice -n 10 lake build RamanujanTau.QFProof2.Main` exits 0. All 4 headlines print
`[propext, Classical.choice, Quot.sound]`. There is no sorry, axiom or native_decide.

* **Gap 1 is done (level 1).**
  * `rhoP'_zero : rhoP' p 0 = 0`.
  * `rhoP'_succ : rhoP' p (a+1) = X·log p·λ(p)·λ(p^a)/(1+X)²`. By Hecke this equals
    `X log p (λ_{a+1}+λ_{a−1})/(1+X)²`, the §1(a) formula.
  * Supporting lemma `Np'_succ`.
* **Gap 2, exchange step done (level 1).** `sum_divisors_prod_local`:
  `Σ_{d|g} Π_{p|g} φ(p, v_p d) = Π_{p|g} Σ_{e ≤ v_p g} φ(p, e)`. The proof goes through
  `Nat.divisors_eq_map_attach_Iic_factorization_prod_pow` and `Finset.prod_sum`.
* **Remaining for `QDecomp`:**
  * write `Kq h k = Π_{p | hk} X^{max(a,b)} ρ_p(|a−b|)`, from the factorizations of gcd, div and lcm;
  * define `W` and `U` as local products, extended by the factors `= 1` at `e = 0`;
  * combine with `chol_rhoP` and `sum_divisors_prod_local`.
  * About 250–350 lines.
* **Remaining for `QDecomp1`:**
  * the product-rule (derivation) version of the same exchange;
  * the s-derivative of `chol_rhoP`, using `rhoP'_succ`.
  * About 300 lines.
* Gaps 3–5 are unchanged (§7).


Scripts for the numerics above are preserved in `scripts/qf_proof/` (`q.c`, `loc.py`).

---

## 2026-11-06 (later): `QFProof3/`. `QDecomp`, `QDecomp1` and `QFactor` are discharged; only the Euler bounds remain

Build: `nice -n 10 lake build RamanujanTau.QFProof3.Main` exits 0.

* 13 headlines, all `[propext, Classical.choice, Quot.sound]`.
* No sorry, axiom or native_decide.
* About 990 lines in 7 files: `Decomp`, `DChol`, `DLocal`, `Decomp1`, `Factor`, `Main`.
* Everything below is **level 1, unconditional**.

| statement | Lean name |
|---|---|
| `Σ_{d|g} Π_{p∈S} φ(p,v_p d) = Π_{p∈S} Σ_{e≤v_p g} φ(p,e)` for `S ⊇` primes of g | `sum_divisors_prod_local'` |
| `Kq h k = Π_{p|hk} X^{max(a,b)} ρ_p(|a−b|)` | `Kq_prod` |
| **`QDecomp Wd Ud`** (the explicit Cholesky data of §1(c)) | `qDecomp` |
| s-derivative of the local LDLᵀ (abstract Hecke sequences) | `dchol_loc` |
| the same for the actual `ρ_p`, `ρ'_p` | `dloc_sym` |
| `Kq1 = (γ_R/r₀)Kq + Σ_p κ'_p Π_{q≠p} κ_q` | `Kq1_prod` |
| **`QDecomp1 Wd W1d Ud Vd`** | `qDecomp1` |
| `recF g₁ ∗ recF g₂ = recF(g₁+g₂)` and `recF 0 = δ` | `recFA_mul`, `recFA_zero_fun` |
| `Fi ∗ (fR/n) = δ`, with `Fi = recF(ΛR/2)/n` | `Fi_mul_F` |
| **`QFactor U (Γc U)`** for every U, with `Γc` the two-variable convolution with `Fi⊗Fi` | `qFactor_canon` |
| **`QFHyp` ⇐ the three Euler bounds** | `qfHyp_of_euler` |

`qfHyp_of_euler` has the following type:

    theorem qfHyp_of_euler (hE : QEuler Wd (Γc Ud) 1) (hE1 : QEuler W1d (Γc Ud) 2)
        (hE2 : QEuler Wd (Γc Vd) 3) : QFHyp

**What remains: gaps 4 and 5, the three `QEuler` bounds (level 2 on `[DeligneBound]`).** About
1.2–1.8k lines.

1. **Multiplicativity.** Show that `fR` and `recF(ΛR/2)` are multiplicative, with local factors
   `D_p(t)^{∓1/2}`. Then show that `Γc Ud d` and `Γc Vd d` factor over primes in the pair (u₁, u₂),
   the latter as a derivation sum over p. Consequently
   `Σ_{u₁,u₂≤y}|Γc_d| ≤ Π_p m_{p,v_p d}` (respectively `M̃_d(Σ_{p≤y}∂m_p + …)`).
2. **Local mass bounds under Deligne** (§6):
   * `m_{p,0} ≤ 1 + C/p²`, using the exact first-order cancellation `Γ(p,1) = X²λ²/(2(1+X))`;
   * `p·W_p(1)·m_{p,1}² ≤ λ(p)² + C/p`;
   * `m_{p,e} ≤ C`;
   * `|wd| ≤ C(e+1)X^e`;
   * `∂m_{p,0} ≤ C log p/p`.
3. **Euler sums.** Apply `logmean_upper` (κ = 1) with `mertens2_bound` and `mertens1_prime`, using
   `d ≤ y² ⇒ log d ≤ 2 log y`.

Item 2 was checked numerically for all p < 20000 (previous section).

---

## 2026-11-06 (later): `QFProof4/`. Gap 4 (multiplicativity) is done; gap 5 (local masses and Euler sums) is mapped exactly

Build: `nice -n 10 lake build RamanujanTau.QFProof4.Main` exits 0.

* 10 headlines, all `[propext, Classical.choice, Quot.sound]`.
* No sorry, axiom or native_decide.
* About 650 lines in 6 files: `RecFMult`, `LocalFi`, `GammaMult`, `GammaMultV`, `Main`.

| statement | Lean name | level |
|---|---|---|
| `recF g n = Π_{p|n} recF g(p^{v_p n})` for g supported on prime powers | `recF_eq_prod` | 1 |
| `Fi n = Π_{p|n} Fi(p^{v_p n})`; `recF gRm p = λ(p)²/2` | `Fi_eq_prod`, `recF_gRm_prime` | 1 |
| `|gRm n| ≤ 3Λ(n)`, `|recF gRm (p^k)| ≤ (k+1)(k+2)/2` | `abs_gRm_le`, `abs_recF_gRm_ppow` | 2 (`[DeligneBound]`) |
| `Γc Ud d u₁ u₂ = Π_{p∈S} γ_p(v_p d; v_p u₁, v_p u₂)` | `Γc_eq_prod` | 1 |
| `Mass (Γc Ud) y d ≤ Π_{p ∈ primes(y!) ∪ primes(d)} T_p(v_p d)`, where `T_p = Σ_{i,j≤v_p(y!)} |γ_p|` | `Mass_le_prod` | 1 |
| `Vd = Σ_p L'_p Π_{q≠p} L_q` and `Mass (Γc Vd) y d ≤ Σ_p T'_p Π_{q≠p} T_q` | `Vd_eq_sum`, `MassV_le` | 1 |
| **(MV2) for Selberg's mollifier ⇐ the three `QEuler` bounds** | `mv2_of_euler` | 2 (on the bounds) |

The combined headline, through `HafnerBridge2.mv2_of_QF`:

```lean
theorem mv2_of_euler {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hE : QEuler Wd (Γc Ud) 1) (hE1 : QEuler W1d (Γc Ud) 2) (hE2 : QEuler Wd (Γc Vd) 3) :
    ∃ B T₀, ∀ T ≥ T₀, ∫_T^{3T} ‖tauL(6+iu) · Mc(bSel ⌊T^θ⌋₊)(6+iu)²‖² du ≤ B·T
```

**Remaining: gap 5, all at level 2 on `[DeligneBound]`.** About 0.8–1.2k lines. Throughout, X = 1/p,
`C₀` is an absolute constant, and every bound is uniform in the truncation N.

* **Basic inputs (Deligne):**
  * `|α(p^a)| ≤ 1` (`abs_alpha_le_one`);
  * `|Fi(p^k)| ≤ (k+1)(k+2)/2 · X^k` (done);
  * `|λ(p^j)| ≤ j+1`;
  * `0 ≤ q = (1+X)² − Xλ² ≤ (1+X)²`.
* **The common factorized estimate.** `|γ_p(e;i,j)| ≤ X^{i+j−e} P_i P_j`, where
  `P_i = Σ_{a≤i}(a+1)c_{i−a} ≤ (i+1)⁴` and `c_k = (k+1)(k+2)/2`.
* **L1:** `T_p(0) ≤ 1 + C₀X²`. Exact low-order terms: γ(0,0) = 1 and γ(1,0) = γ(0,1) = λ²X²/(2(1+X)).
  The rest, i+j ≥ 2, is at most `4X²(Σ_i P_i 2^{−i})²`.
* **L2:** `T_p(1) ≤ |λ| + C₀X`. Here γ(1,0) = γ(0,1) = α(p) = −λ/2.
* **L3:** `T_p(e) ≤ C₀(e+1)⁹`.
* **L4:** `T'_p(0) ≤ (λ²/4)X log p + C₀X`. The (0,0) term vanishes, and
  `γ'(0,1,0) = λ²X log p(1/(1+X) − 2X/(1+X)²)/4`.
* **L5:** `T'_p(1) ≤ log p · (|λ|/2 + C₀X)`.
* **L6:** `T'_p(e) ≤ C₀ (e+1)^{10} log p`.
* **Pivots.** `|Wc_p(e)| ≤ W̃_p(e)` and `|wd_p(e)| ≤ C₀(e+1)W̃_p(e)`, where `W̃_p(1) = X` and
  `W̃_p(e) = 3X^e` for e ≥ 2.
* **Euler assembly.**
  * Define `f = ofLocal(p,e ↦ p^e W̃_p(e) t_p(e)²)`, with `t_p(1) = |λ| + C₀X` and
    `t_p(e) = C₀(e+1)⁹`. Then `f(p) ≤ λ² + C/p` and `f(p^e) ≤ B(e+1)^{18}`.
  * `logmean_upper` must be reproved with polynomial growth `f(p^k) ≤ B(k+1)^m` in place of
    `f(p^k) ≤ B`; the local tail is `Σ_{k≥2}(k+1)^m p^{−k} ≪ p^{−2}`. Together with `mertens2_bound`
    this gives `Σ_{d≤y²} f(d)/d ≪ log y`, hence QEuler₁.
  * QEuler₂ adds `log d ≤ 2 log y`.
  * QEuler₃: `Mass' ≤ Π T̃ · [Σ_{p≤y} T'_p(0) + C Σ_{p|d}(e+1) log p]`. The first sum is
    `≤ (log y + E)/4 + C₀(1 + log y)`, by `mertens1_prime` and the harmonic sum, so `Mass' ≪ log y · Π T̃`.

---

## 2026-11-06 (later): `QFProof5/`. Gap 5 is closed: `QFHyp` and (MV2) hold under `[DeligneBound]` alone

Build: `nice -n 10 lake build RamanujanTau.QFProof5.Main` exits 0.

* 17 headlines, all `[propext, Classical.choice, Quot.sound]`.
* No sorry, axiom or native_decide.
* About 1.6k lines in 7 files: `Sums`, `Basic`, `Conv`, `Local`, `Euler`, `Assemble`, `Main`.
* Everything is **level 2 on `[DeligneBound]` only**: the repo class `τ(p)² ≤ 4p^{11}` at primes. The
  combinatorial lemmas `Sums` and `conv2_le` are level 1.

```lean
theorem qfHyp_deligne [DeligneBound] : RamanujanTau.HafnerBridge.QFHyp
theorem mv2_deligne [DeligneBound] {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T
```

Both are obtained from `qfHyp_of_euler` and `mv2_of_euler` applied to `qEuler1`, `qEuler2` and `qEuler3`.

### How the §6 plan was simplified

1. **One convolution inequality replaces the `P_i ≤ (i+1)⁴` bookkeeping.** Every local mass is
   bounded with a weight `w`:

       Σ_{i,j≤N} w^{i+j}|γ_K(e;i,j)| ≤ (Σ_{a,b≤N} w^{a+b}|K(a+b,e)|) · (Σ_k w^k|Fi(p^k)|)²   (`wmass_le`)

   This uses `|α| ≤ 1` and a two-variable Cauchy-product bound (`conv2_le`).
   * `|Fi(p^k)| ≤ C(k+2,2)X^k` and `wX ≤ 1/2` give `Σ_k w^k|Fi| ≤ 8`, by Mathlib's
     `hasSum_choose_mul_geometric_of_norm_lt_one`.
   * The kernels obey `|L(n,e)| ≤ (n+1)²X^{n−e}` and `|L'(n,e)| ≤ log p (n+1)²X^{n−e}`, which
     uses `|λ(p^j)| ≤ j+1` (`VoronoiPointwise.cheb_bound`), `|ρ_p(n)| ≤ n+1` and `|ρ'_p(n)| ≤ n log p`.
   * Then `(a+b+1)² ≤ (a+1)²(b+1)²` factorizes the kernel sum.
2. **Weight `w = p/2` for e = 0, 1; weight 1 for general e.**
   * With `w = p/2`, the terms with `i+j ≥ 2` cost `w^{−2} = 4X²` times a uniform constant.
   * `split_low` peels off the three terms (0,0), (1,0), (0,1), which are computed exactly:
     `γ(0;1,0) = λ²X²/(2(1+X))`, `γ(1;1,0) = α(p) = −λ/2`, `γ'(1;1,0) = −λ log p/4`, and
     `|γ'(0;1,0)| ≤ λ²X log p/4 + 2X`.
   * For e = 1, `X^{a+b−1} = p·X^aX^b` gives the extra X.
   * For general e, `X^{a+b−e} ≤ X^{a−e}X^{b−e}` (truncated subtraction) gives polynomial growth in e.
3. **The local masses, uniform in the truncation N** (X = 1/p, λ = λ(p)):

   | label | statement | Lean name |
   |---|---|---|
   | L1 | `T_p(0) ≤ 1 + 65540X²` | `Tl_zero_le` |
   | L2 | `T_p(1) ≤ |λ| + 65536X` | `Tl_one_le` |
   | L3 | `T_p(e) ≤ 16384(e+1)⁶` | `Tl_le` |
   | L4 | `T'_p(0) ≤ λ²X log p/2 + 65540X` | `TlV_zero_le` |
   | L5 | `T'_p(1) ≤ log p(|λ|/2 + 65536X)` | `TlV_one_le` |
   | L6 | `T'_p(e) ≤ 16384 log p (e+1)⁶` | `TlV_le` |

   The pivots satisfy `|W_p(e)| ≤ X^e` (`abs_Wc_le`) and `|wd_p(e)| ≤ 8(e+1)X^e` (`abs_wd_le`).
   Hence `|W(d)| ≤ 1/d` and `|W₁(d)| ≤ (|γ_R| + 16 log d)/d`.
4. **No polynomial `logmean_upper` is needed.**
   * `logmean_geo` takes the hypothesis `f(p^k) ≤ B(3/2)^k` for k ≥ 2. The local tail is then
     geometric with ratio `3/(2p) ≤ 3/4`, so it is at most `9B/p²`.
   * `(e+1)^{12} ≤ (100/3)^{12}(3/2)^e` follows from Bernoulli with `1.03^{12} ≤ 3/2`.
   * The majorant is `f = ofLocal(tt²)` with `tt(1) = |λ| + 65536X` and `tt(e) = 16384(e+1)⁶`.
     Then `f(p) ≤ λ² + K/p`, and `mertens2_bound` gives κ = 1 (`euler_fT`).
5. **Assembly.**
   * Primes `q ≤ y` with `q ∤ d` contribute at most `Π(1 + 65540/q²) ≤ e^{65540}` (`prod_Tl_le`).
   * QEuler₃ uses `MassV_le` and needs `Σ_{p≤y} V₀(p) ≪ log y`. This comes from `mertens1_prime`
     (the `λ² log p/p` part) together with `harmonic_le_one_add_log` (the `1/p` part).
   * The other contribution is `Σ_{p|d}(v_p d + 1) log p ≤ 2 log d ≤ 4 log y`.

**Evidence level.** `QFHyp`, and hence Hafner's (MV2) for Selberg's mollifier at `θ ≤ 1/81600`, are
now **level 2 on `[DeligneBound]` only**.

**Remaining gaps.**

* None on the QF route.
* The constants are huge (e^{65540}) but explicit, and immaterial.
* Without Deligne, L1–L6 fail, as noted in §6 and `SELBERG_COEFFS.md` §2.
