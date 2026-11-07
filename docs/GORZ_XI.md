# Griffin–Ono–Rolen–Zagier for the Riemann Ξ-function (and GORZ Theorems 3/6 for general sequences)

Reference: M. Griffin, K. Ono, L. Rolen, D. Zagier, *Jensen polynomials for the Riemann zeta function and other
sequences*, PNAS 116 (2019) 11103–11110 (arXiv:1902.07321). Equation numbers below follow the arXiv version.

## Normalizations

GORZ use these conventions, and the Lean code follows them exactly.

* `Λ(s) = π^{−s/2} Γ(s/2) ζ(s)`, which is Mathlib's `completedRiemannZeta`.
* The Taylor coefficients `γ(n)` are defined by eq. (1): **`(−1 + 4z²) Λ(1/2 + z) = Σ_{n≥0} γ(n) z^{2n}/n!`**.
  Note that the expansion is in **`z^{2n}/n!`**. In Lean, `gammaMathlib n = n!/(2n)! · Re[(d/dz)^{2n} xiFun](0)`,
  where `xiFun z = (−1 + 4z²) · completedRiemannZeta (1/2 + z)`.
* The Jensen polynomial is `J^{d,n}_α(X) = Σ_{j≤d} C(d,j) α(n+j) X^j` (eq. (2)), written `jensenSeq α d n` in Lean.
* The renormalized polynomial is `Ĵ^{d,n}(X) = δ(n)^{−d}/α(n) · J^{d,n}_α((δ(n)X − 1)/E(n))` (eq. (5), with
  `E = e^{A}`). In Lean this is `Jhat α E δ d n`.
* `H_d` is the Hermite polynomial with generating function `e^{−t² + Xt} = Σ H_d(X) t^d/d!` (eq. (3)). In
  physicists' normalization it equals `H_d^{phys}(X/2)`, and it is the existing `GORZ.H d`.
  For example, `H_6 = X⁶ − 30X⁴ + 180X² − 120`.
* Riemann's formula (GORZ (11)–(13)): let `θ₀(t) = Σ_{k≥1} e^{−πk²t} = (θ(t) − 1)/2`, with
  `θ = HurwitzZeta.evenKernel 0`. Define
  `F(m) = ∫_1^∞ (log t)^m t^{−3/4} θ₀(t) dt` and `B(n) = 32·C(2n,2)·F(2n−2) − F(2n)`. Then
  **`γ(n) = n!/(2n)! · 2^{1−2n} · B(n)`** for `n ≥ 1`. In Lean, `FXi`, `BXi` and `gammaXi = aXi · BXi` implement these.

## Evidence levels

The four levels are: (1) Lean, axiom-clean; (2) Lean, conditional on a named hypothesis; (3) paper only;
(4) numerical only.

| Milestone | Statement | Lean name | Level |
|---|---|---|---|
| M1 | **GORZ Theorem 6** (general `F`, `C_i(n) → c_i`): `Ĵ^{d,n} → H_{F,d}` coefficientwise and uniformly on compacts | `thm6_coeff`, `thm6_uniform` | **(1)** |
| M1 | **GORZ Theorem 3 + Corollary** in form (15): `log(α(n+j)/α(n)) = A j − δ²j² + Σ_{i=3}^d g_i j^i + o(δ^d)` with `g_i = o(δ^i)` ⇒ `Ĵ → H_d` (coefficientwise and uniformly on compacts) and `J^{d,n}_α` eventually hyperbolic | `gorz_thm3` | **(1)** |
| M1 | The arXiv form (4) (`g = 0`) | `gorz_thm3_arxiv` | **(1)** |
| M1 | Difference form: `Δ²[log α](n)/δ² → −2`, `Δ^k[log α](n)/δ^k → 0` (`3≤k≤d`) ⇒ same conclusions, with `E = α(n+1)/α(n)` | `gorz_thm3_diff` | **(1)** |
| M1 | Sanity check: the partition case re-derived as an instance of the abstract theorem | `partition_gorz` | **(1)** |
| M2 | Riemann's formula `Λ₀(s) = (M(s/2) + M((1−s)/2))/2`, `M(w) = ∫_1^∞ t^{w−1}(θ(t)−1)dt` | `completedRiemannZeta₀_eq` | **(1)** |
| M2 | **`γ(n)` (from Mathlib's `completedRiemannZeta`) `= n!/(2n)!·2^{1−2n}·B(n)`**, all `n ≥ 1` | `gammaMathlib_eq` | **(1)** |
| M3 | `XiKernelHyp`: `B(n) > 0` eventually and `n^{k/2}·Δ^k[log B](n) → 0` for every `k ≥ 2` | **`xiKernelHyp_holds`** (via `dlog_BXi_bound`) | **(1)** (2026-11-04; previously (4)) |
| M4 | **GORZ Theorem 1**: `∀ d, J^{d,n}_γ` is hyperbolic for all large `n`, and `Ĵ^{d,n}_γ → H_d` (with `δ(n) = (2n)^{−1/2}`, `E(n) = γ(n+1)/γ(n)`) | **`xi_gorz_unconditional`** (= `xi_gorz_mathlib xiKernelHyp_holds`); conditional forms `xi_gorz_mathlib`, `xi_gorz` | **(1)**, unconditional |

Running `#print axioms` on every name in the table (see `RamanujanTau/GORZXi/Main.lean` and
`RamanujanTau/GORZXi/MainUncond.lean`) gives `[propext, Classical.choice, Quot.sound]`. The files contain no
`sorry`, no `axiom` and no `native_decide`. `XiKernelHyp` is a `def … : Prop`; it is an explicit hypothesis of
`xi_gorz` and `xi_gorz_mathlib`, and it is **proved** by `xiKernelHyp_holds`.

## Headline statements

```lean
theorem GORZXi.gorz_thm3 (α A δ : ℕ → ℝ) (d : ℕ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hαpos : ∀ᶠ n in atTop, 0 < α n) (g : ℕ → ℕ → ℝ)
    (hg : ∀ i ∈ Icc 3 d, (fun n => g i n) =o[atTop] (fun n => δ n ^ i))
    (h : ∀ j ≤ d, (fun n => log (α (n + j) / α n) -
        (A n * j - δ n ^ 2 * j ^ 2 + ∑ i ∈ Icc 3 d, g i n * j ^ i)) =o[atTop] (fun n => δ n ^ d)) :
    (∀ i, Tendsto (fun n => (Jhat α (fun n => exp (A n)) δ d n).coeff i) atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K, IsCompact K → TendstoUniformlyOn (fun n x => (Jhat α (exp ∘ A) δ d n).eval x) (GORZ.H d).eval atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n))

theorem GORZXi.gammaMathlib_eq (n : ℕ) (hn : 1 ≤ n) : gammaMathlib n = gammaXi n

def GORZXi.XiKernelHyp : Prop :=
  (∀ᶠ n in atTop, 0 < BXi n) ∧
    ∀ k, 2 ≤ k → Tendsto (fun n : ℕ => Real.sqrt n ^ k * dlog BXi n k) atTop (𝓝 0)
-- dlog β n k = Σ_{j≤k} (−1)^{k−j} C(k,j) log β(n+j)

theorem GORZXi.xi_gorz_mathlib (hyp : XiKernelHyp) (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat gammaMathlib (fun n => gammaMathlib (n+1) / gammaMathlib n) δXi d n).coeff i)
      atTop (𝓝 ((GORZ.H d).coeff i))) ∧ (… uniformly on compacts …) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq gammaMathlib d n))

theorem GORZXi.xiKernelHyp_holds : XiKernelHyp

theorem GORZXi.xi_gorz_unconditional (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).coeff i)
      atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).eval x)
      (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq gammaMathlib d n))
```

## Proof structure

1. **Core (`Core.lean`).** The proof works for an arbitrary sequence `α` and scales `E`, `δ`. The Newton
   identity (`GORZ.newtonId`, all degrees) gives `Ĵ^{d,n}(x) = Σ_k C(d,k) γ_k(n) x^{d−k}(δx−1)^k`, where
   `γ_k = Δ^k w_n(0)/δ^k` and `w_n(j) = α(n+j)/α(n)·E^{−j}`. If `γ_k → ℓ_k`, the coefficients converge to
   those of `Σ C(d,k)(−1)^kℓ_kX^{d−k}`. Coefficient convergence then gives uniform convergence on compacts,
   because the degree is at most `d`. For `ℓ = c_k` (the derivatives of `e^{−y²}`), the alternation points of
   `GORZ.H_alternating`, together with `hyperbolic_of_alternating`, give eventual hyperbolicity.
2. **Theorem 6 (`Theorem6.lean`).** The difference `Δ^k[j^i](0)` is `0` for `i < k` and `k!` for `i = k`. This is
   GORZ's own proof, and it gives `γ_k → k!c_k`. The paper's `H_{F,d}` is identified with the limit (`Hgen_eq_HF`).
3. **Theorem 3 (`Theorem3.lean`, `exp_poly_expansion`).** Suppose `log(α(n+j)/α(n)) − Aj = Q_n(δj) + o(δ^d)`,
   where `Q_n(0) = 0` and the coefficients of `Q_n` converge. Then `w_n(j) = Σ_{i≤d} [y^i]P_n · δ^ij^i + o(δ^d)`,
   with `P_n = Σ_{m≤d} Q_n^m/m!`. The proof uses three bounds:
   * `|e^a − e^b| ≤ 2e|a−b|`;
   * `|e^x − Σ_{m≤d}x^m/m!| ≤ C|x|^{d+1}` (Mathlib's `Real.exp_bound`), with `x = O(δ)`;
   * the monomials of degree `> d` are `o(δ^d)`.

   Finally, `k!·[y^k]Σ_{m≤d}(−y²)^m/m! = c_k` (`factorial_mul_coeff_texp_negX2`).
4. **Difference form (`Diff.lean`).** Newton interpolation writes `log(α(n+j)/α(n)) − j·log(α(n+1)/α(n))`
   exactly as `Q_n(δj)`, with `Q_n(y) = Σ_{k≥2} Δ^k[log α](n)/k! · desc_k(y/δ)`. Its coefficients converge to
   those of `−y²`. `fd_chain_close` gives `|Δ^K f(0) − f^{(K)}(0)| ≤ 2^K K^{K+1} sup|f^{(K+1)}|`, by Taylor's
   theorem to order `K+1` (the repo's `taylor_bounds`).
5. **Ξ (`XiMain.lean`).** Write `γ = a·B` with `a(n) = n!/(2n)!·2^{1−2n}`. Then `Δ log a(m) = −log(8(2m+1))`,
   so `2n·Δ²log a(n) → −2` and `Δ^k log a(n) = O(n^{1−k})`. Both facts are unconditional and come from the
   derivative chain of `log(2x+1)`. With `δ(n) = (2n)^{−1/2}`, the hypothesis `XiKernelHyp` supplies exactly
   the remaining `B` contributions in `gorz_thm3_diff`.
6. **M2 (`XiMellin.lean`, `XiTaylor.lean`).**
   * Mathlib defines `Λ₀ = mellin f_modif`. Splitting `f_modif` at `t = 1` and applying `t ↦ 1/t`
     (`mellin_comp_inv`, `mellin_cpow_smul`) together with `θ(1/t) = t^{1/2}θ(t)` gives
     `Λ₀(s) = (M(s/2) + M((1−s)/2))/2`.
   * The derivative of `mellin(log^m·A)` is `mellin(log^{m+1}·A)`, by Mathlib's `mellin_hasDerivAt_of_isBigO_rpow`.
   * Near `z = 0`, `(−1+4z²)Λ(1/2+z) = 4 + (4z²−1)Λ₀(1/2+z)`. An explicit derivative chain `Gch` then yields
     every iterated derivative at `0`, and `mellin(log^m·A)(1/4) = 2F(m)` (`mellin_Am_quarter`).

## Proof of `XiKernelHyp` (M3, level 1)

The proof is elementary: no full asymptotic expansion of `F` (GORZ Theorem 7) and no log-concave measure
theory is needed. Write `u = log t`, `x = u − c`, and `M = 2n − 2` for the base index.

1. **Theta sandwich** (`XiStein.lean`). From Mathlib's `hasSum_int_evenKernel`,
   `θ₀(t) = Σ_{k≥1} e^{−πk²t}`, so `e^{−πt} ≤ θ₀(t) ≤ 2e^{−πt}` for `t ≥ 1` (`theta0_lower`, `theta0_upper`).
   All integrands are dominated by `K·t^N e^{−πt} ≤ K·N!·e^{−t}`, which gives integrability and decay.
2. **Stein identity** (`stein_identity`). Differentiating `Φ = u^{M} x^{2q+1} t^{1/4} e^{−πt}` and using
   `∫_1^∞ Φ' = 0` (Mathlib's `integral_Ioi_of_hasDerivAt_of_tendsto`; `Φ(1) = 0` because `log 1 = 0`) gives
   `∫ ((πt − ¼)u − M) u^{M−1} x^{2q+1} t^{−3/4}e^{−πt} = (2q+1) S_q`, where
   `S_q = ∫ u^M x^{2q} t^{−3/4}e^{−πt}`.
3. **Pointwise inequalities** (`XiMoments.lean`). Let `c` be the root of `(πe^c − ¼)c = M` (`cRoot`, obtained by
   the IVT on `[1, log(M+1)]`). Then `D·x = πu(e^u − e^c)x + (M/c)x²`, where `D = (πe^u − ¼)u − M`. Put
   `λ₁ = πe^{c−1}` and `λ₂ = M/c²`. Elementary estimates of `e^u` give `λ₂ux² ≤ Dx` (`ineqI`) and
   `λ₁ux² ≤ Dx + λ₁ux^{2R}` (`ineqII`). The second uses `|x| ≥ 1` in the far-left region `u < c − 1`, which
   is exactly where the curvature drops to `λ₂ ≪ λ₁`.
4. **Moment recursion** (`stein_ineqI`, `stein_ineqII`, `moment_rec`). Integrating these inequalities gives
   `λ₂S_{q+1} ≤ (2q+1)S_q` and `λ₁S_{q+1} ≤ (2q+1)S_q + λ₁S_{2q+2}`. Since `c ≤ log(M+1)` and
   `log(M+1)^4 ≤ (M+1)/4` eventually, we have `λ₁ ≤ λ₂²`, and then `S_q λ₁^q ≤ B_q S_0` with explicit
   constants `B_q`. Transferring back through the sandwich gives
   `|∫ u^M x^l t^{−3/4}θ₀| ≤ (1 + 2B_l) λ₁^{−l/2} F(M)` (`abs_rhoT_le`).
5. **Binomial expansion** (`XiKernel.lean`). `F(M+i) = F(M)c^i Σ_{l≤L} C(i,l) μ_l`, with normalized moments
   `μ_l` satisfying `|μ_l| ≤ (1+2B_l) ε^l`, where `ε = λ₁^{−1/2}/c` (`FXi_add`, `abs_muX_le`). The root
   equation gives `λ₁c² ≥ Mc/e`, so `nε² ≤ 3/c → 0` (`n_epsN_sq`). This is the `1/log n` to spare.
6. **Small-coefficient polynomials** (`XiPoly.lean`). Say `f(j) = Σ a_i j^{d_i}` on `j ≤ K` with `|a_i| ≤ Cη^{d_i}`
   (written `SP`). This class is closed under `+`, `×` and powers, and satisfies `|Δ^k f| ≤ N C 2^k (kη)^k`
   because `Δ^k j^d = 0` for `d < k`. Truncating the `log` series with Mathlib's
   `abs_log_sub_add_sum_range_le` then gives `|Δ^k log(1+q)| ≤ Λη^k` for `q` with degrees `≥ 1`
   (`abs_fd_log_SP`, `abs_dlog_of_SP`).
7. **Assembly** (`XiUncond.lean`, `dlog_BXi_bound`). For `j ≤ k`:
   `B(n+j) = 32C(2n,2)F(M)·c^{2j}·[A(j)E₀(j) − κE₂(j)]`, where
   * `A(j) = C(2n+2j,2)/C(2n,2) = 1 + O(j/n) + O(j²/n²)`,
   * `E_a(j) = Σ_{l≤2k+2} C(2j+a,l)μ_l`,
   * `κ = c²/(32C(2n,2)) ≤ 1/n`.

   Each piece is `SP` with `η = ε + 1/n`, and `W(0) ≥ 1/2`. Hence `B(n) > 0` and `|Δ^k log B(n)| ≤ Λ_k η^k`.
   Since `√n·η → 0` (`tendsto_sqrt_etaN`), `xiKernelHyp_holds` follows.

Numerical check (level 4, `scripts/gorzxi/xi7.py`, scipy): the inequalities (I), (II) and `λ₁ ≤ λ₂²` hold for
`M = 10 … 10⁵`. The normalized moments `λ₁^q S_q/S_0` stay bounded (≈ 0.33, 0.32, 0.53, 1.22 at `M = 10⁵`), the
θ-to-clean ratio is `1 + O(10⁻⁷)`, and `n ε²` decays (1.45, 0.74, 0.45, 0.32, 0.22, 0.16).

## The named hypothesis: numerical evidence (level 4, superseded by the proof above)


The values below were computed in mpmath (50–70 digits) from the integral formula for `F`. Scripts are in
`scripts/gorzxi/xi3.py`–`xi6.py`.

* The formula (13) agrees with the Cauchy-integral Taylor coefficients of `(−1+4z²)Λ(1/2+z)` for `n = 0..4`.
  At `n = 0` the value is `4 − 2F(0) = 3.97696622551`. The formula also reproduces GORZ's table:
  `γ(10) = 1.63233804903e−17` and `γ(100) = 6.57772637858e−205`.
* The table below gives `N^{k/2}·Δ^k log B(N)`.

| N | k=2 | k=3 | k=4 | k=5 | k=6 | k=7 |
|---|---|---|---|---|---|---|
| 25 | 0.583 | −0.126 | 0.0487 | −0.0265 | 0.0183 | −0.0152 |
| 100 | 0.477 | −0.0544 | 0.0115 | −0.0035 | 0.00139 | −0.00068 |
| 400 | 0.386 | −0.0221 | 0.00237 | −3.7e−4 | 7.6e−5 | −1.9e−5 |
| 1600 | 0.318 | −0.0090 | 4.8e−4 | −3.8e−5 | 3.9e−6 | −5.0e−7 |
| 10⁴ | 0.255 | −0.0028 | 6.0e−5 | | | |
| 10⁵ | 0.2025 | −7.0e−4 | 4.6e−6 | | | |

  For `k = 2` the decay is only logarithmic. The Laplace prediction is `N·Δ²log B(N) ≈ 2/(1+u₀(2N))`, where
  `s/u₀ + 1/4 = πe^{u₀}`, and it matches the computed values. For `k ≥ 3` the decay is like `N^{1−k/2}`, up
  to logarithmic factors. Since the `k = 2` limit is strictly `0` (and not merely bounded), the hypothesis is
  not vacuous. It is also sharp in the sense that `δ² = 1/(2n)` comes from the factorial part.
* The resulting GORZ quantities are consistent with the theorem:
  * `2N·δ_true(N)² = −N·Δ²log γ(N)` takes the values 0.38, 0.51, 0.61, 0.68, 0.74 and 0.80 at
    `N = 25, 100, 400, 1600, 10⁴, 10⁵`, tending slowly to 1;
  * `Δ^k log γ/δ_true^k → 0` for every `k`.

## What remains

Nothing remains for GORZ Theorem 1: `xi_gorz_unconditional` is level (1). Not attempted: effective thresholds
(the proof gives explicit but huge constants, and the threshold in `n` comes from `cRoot → ∞` and
`log(M+1)^4 ≤ (M+1)/4`), and GORZ Theorem 2 (`d ≤ 8` for all `n`). (Later: the `d = 2` case of Theorem 2, i.e. the
Turán inequalities for every `n`, is proved unconditionally in `GORZXiEff/` — `GORZXiEff.turan_gamma_unconditional`,
[GORZ_XI_EFFECTIVE](GORZ_XI_EFFECTIVE.md); `d = 3` is reduced to the higher-order Turán inequalities in `GORZXiD3/`,
[GORZ_XI_D3](GORZ_XI_D3.md), which is a restatement, not a proof.)

## Files (`RamanujanTau/GORZXi/`)

| File | Contents |
|---|---|
| `Core.lean` | `jensenSeq`, `Jhat`, `wr`, `gk`, `Gpoly`, `Hgen`, `Jhat_eq_Gpoly`, `tendsto_coeff_Jhat_of_gk`, `tendstoUniformlyOn_of_coeff`, `eventually_hyperbolic_of_gk` |
| `Theorem6.lean` | `apow`, `tendsto_gk_of_thm6`, `HF`, `Hgen_eq_HF`, **`thm6_coeff`**, **`thm6_uniform`** |
| `Theorem3.lean` | `CoeffTo` algebra, `texp`, **`exp_poly_expansion`**, `cH_even`, `tendsto_gk_of_poly`, `conclusions_of_gk`, **`gorz_thm3`**, **`gorz_thm3_arxiv`** |
| `Diff.lean` | `dlog`, `Qd`, **`gorz_thm3_diff`**, **`fd_chain_close`** |
| `Partition.lean` | `dlog_p_split`, `fd_phi_close`, `tendsto_fd_eps`, **`partition_gorz`** |
| `XiMain.lean` | `aXi`, the `log(2x+1)` chain `uch`, `fd_u_bound`, `theta0`, `FXi`, `BXi`, `gammaXi`, **`XiKernelHyp`**, `δXi`, **`xi_gorz`** |
| `XiMellin.lean` | `Aθ`, `Bθ`, `mellin_fmodif_split`, **`completedRiemannZeta₀_eq`**, `Am`, `hasDerivAt_mellin_Am` |
| `XiTaylor.lean` | `Lch`, `Gch`, `xiFun`, `gammaMathlib`, `mellin_Am_quarter`, **`gammaMathlib_eq`**, **`xi_gorz_mathlib`** |
| `Main.lean` | `#print axioms` for all headline theorems |
| `XiPoly.lean` | `SP` (small-coefficient polynomials in `j`), `abs_fd_SP`, `abs_SP_le`, **`abs_fd_log_SP`**, **`abs_dlog_of_SP`** |
| `XiStein.lean` | `theta0_lower/upper`, integrability bounds, `rho0`, `rhoT`, `steinI`, **`stein_identity`** |
| `XiMoments.lean` | `ineqI`, `ineqII`, `stein_ineqI/II`, `moment_rec`, `RootData`, **`abs_rhoT_le`** |
| `XiKernel.lean` | `cRoot` (IVT), `cRoot_tendsto`, `rootData_ev`, `FXi_pos`, `muX`, **`FXi_add`**, `abs_muX_le`, `SP_choose` |
| `XiUncond.lean` | `etaN`, `tendsto_sqrt_etaN`, `SP_E`, `SP_A`, `B_repr`, **`dlog_BXi_bound`**, **`xiKernelHyp_holds`**, **`xi_gorz_unconditional`** |
| `MainUncond.lean` | `#print axioms` for the unconditional track |

Imports: `RamanujanTau.GORZ.*` and `JensenThreshold.*`, unmodified, plus Mathlib. Nothing was added to the root
`RamanujanTau.lean` at the time; `GORZXi.Main` and `GORZXi.XiUncond` have since been added. Build with a single process (each module takes 13–20 s once the dependencies are built):

```
lake build RamanujanTau.GORZXi.Main
lake build RamanujanTau.GORZXi.MainUncond
```
