# GORZ Theorem 2 (all `n`) for the Riemann Ξ-function: the degree-2 case

Reference: M. Griffin, K. Ono, L. Rolen, D. Zagier, *Jensen polynomials for the Riemann zeta function and other
sequences*, PNAS 116 (2019), arXiv:1902.07321. Normalizations follow `docs/GORZ_XI.md`: `γ = gammaMathlib`, which
is defined from Mathlib's `completedRiemannZeta` by `(−1 + 4z²)Λ(1/2 + z) = Σ γ(n) z^{2n}/n!`, and
`J^{d,n}_γ = jensenSeq gammaMathlib d n`.

## What GORZ Theorem 2 says and how GORZ prove it

> **Theorem 2.** If `1 ≤ d ≤ 8`, then `J^{d,n}_γ(X)` is hyperbolic for every `n ≥ 0`.

GORZ write that hyperbolicity for all `n` was already known for `d ≤ 3`: `d = 2` is Csordas–Norfolk–Varga (1986)
and `d = 3` is Dimitrov–Lucas (2011). Their §5.2 contains only a *sketch* for `4 ≤ d ≤ 8`. The sketch has two
parts:

* **Numerical check.** Hermite's criterion confirms hyperbolicity for `n ≤ 10⁶`.
* **Effective bound.** An effective form of the asymptotic (16) gives `0 < C(n,j) < 14.25` for `n ≥ 7`.
  Explicit coefficient boxes around `H_d` then give hyperbolicity for `n ≥ M_{ε_d}`, where `M_{ε_d} < 10⁶`. For
  example, `M_{ε_4} = 10⁴`.

So the paper proof of the cases `d ≥ 4` depends on certified values of `γ(n)` up to `n ≈ 10⁶`.

## Result (this directory)

The degree-2 case of Theorem 2 is proved for **every `n ≥ 0`**, **unconditionally and axiom-clean**
(2026-11-04 update). The analytic input `CVHyp` (Csordas–Varga 1988) is now itself a Lean theorem,
`cvHyp_holds`, proved by an even Taylor model at `u = 0`, a kernel-checked interval cover of a compact
range, and an explicit estimate for large `u`; see "The proof of `CVHyp`" below. The finite computation is
confined to `CVHyp`: 129 interval cells, each closed by `decide +kernel`. There is no `native_decide`.

| Statement | Lean name | Level |
|---|---|---|
| `γ(n) = 32 · n!/(2n)! · ∫_0^∞ u^{2n} Φ(u) du` for **all** `n ≥ 0`, where `Φ` is Riemann's kernel (explicit series `PhiR`) | **`gamma_eq_mom`** | **(1)** |
| — the case `n ≥ 1`: substitution `t = e^{2u}` in `FXi`, plus two integrations by parts | `gammaMathlib_eq_mom` | (1) |
| — the case `n = 0`: boundary term `h'(0) = −1/4`, from the derivative at `t = 1` of `θ(t) = t^{−1/2}θ(1/t)` | `gammaMathlib_zero_eq_mom`, `Tth'_one` | (1) |
| `Φ > 0` on `[0,∞)`; `PhiD` is the derivative of `Φ` on `(0,∞)`; integrability of all `u^mΦ`, `u^mΦ'`; `∫u^{m+1}Φ' = −(m+1)∫u^mΦ` | `kernelMom_PhiR`, `hasDerivAt_PhiR` | (1) |
| **Chebyshev–Turán lemma** (any kernel): `R = −Φ'/(uΦ)` nondecreasing ⇒ `(2n+1)b_{2n}b_{2n+4} ≤ (2n+3)b_{2n+2}²` | **`turan_mom`** | **(1)** |
| Abstract transfer: `α(n) = C·n!/(2n)!·b_{2n}` ⇒ `α(n)α(n+2) ≤ α(n+1)²` and `J^{2,n}_α` hyperbolic | `turan_seq`, `jensen2_hyperbolic` | (1) |
| Turán inequalities, conditional form | `turan_gamma (hCV : CVHyp)` | (1) as an implication |
| GORZ Thm 2, `d = 2`, conditional form | `jensen2_gamma (hCV : CVHyp)` | (1) as an implication |
| **`CVHyp`: `u ↦ −Φ'(u)/(uΦ(u))` nondecreasing on `(0,∞)`** | **`CV.cvHyp_holds`** | **(1)** (also (3) Csordas–Varga 1988) |
| **Turán inequalities `γ(n)γ(n+2) ≤ γ(n+1)²` for all `n ≥ 0`** | **`turan_gamma_unconditional`** | **(1)** |
| **GORZ Thm 2, `d = 2`: `J^{2,n}_γ` hyperbolic for all `n ≥ 0`** | **`jensen2_gamma_unconditional`** | **(1)** |
| `J^{d,n}_γ` hyperbolic for `2 ≤ d ≤ 8`, `0 ≤ n ≤ 300` | — | (4) exact Sturm counts on 45-digit data |

Running `#print axioms` on every Lean name above gives `[propext, Classical.choice, Quot.sound]`. The files
contain no `sorry`, no `axiom` and no `native_decide`.

```lean
def GORZXiEff.CVHyp : Prop := MonotoneOn (ratioR PhiR PhiD) (Ioi 0)     -- ratioR Φ Φ' u = −Φ' u / (u * Φ u)
theorem GORZXiEff.gamma_eq_mom (n : ℕ) : gammaMathlib n = 32 * fq n * mom PhiR (2 * n)
    -- fq n = n!/(2n)!,  mom Φ m = ∫ u in Ioi 0, u ^ m * Φ u
theorem GORZXiEff.turan_gamma (hCV : CVHyp) (n : ℕ) :
    gammaMathlib n * gammaMathlib (n + 2) ≤ gammaMathlib (n + 1) ^ 2
theorem GORZXiEff.jensen2_gamma (hCV : CVHyp) (n : ℕ) : Hyperbolic (jensenSeq gammaMathlib 2 n)
theorem GORZXiEff.CV.cvHyp_holds : CVHyp
theorem GORZXiEff.turan_gamma_unconditional (n : ℕ) :
    gammaMathlib n * gammaMathlib (n + 2) ≤ gammaMathlib (n + 1) ^ 2
theorem GORZXiEff.jensen2_gamma_unconditional (n : ℕ) : Hyperbolic (jensenSeq gammaMathlib 2 n)
theorem GORZXiEff.turan_mom {Φ Φ'} (h : KernelMom Φ Φ') (hR : MonotoneOn (ratioR Φ Φ') (Ioi 0)) (n : ℕ) :
    (2 * n + 1 : ℝ) * mom Φ (2 * n) * mom Φ (2 * n + 4) ≤ (2 * n + 3 : ℝ) * mom Φ (2 * n + 2) ^ 2
```

Here `PhiR u = Σ_{k≥0} (2π²K²e^{9u/2} − 3πK e^{5u/2}) e^{−πK e^{2u}}` with `K = (k+1)²`, which is Riemann's
`Φ(u)`. `PhiD` is its termwise derivative, and `hasDerivAt_PhiR` proves that it is the derivative.

## The proof

1. **Kernel representation.** Write `h(u) = e^{u/2}θ₀(e^{2u}) = Σ_k h_k(u)`. Termwise, `8Φ = 4h'' − h`.
   * **`n ≥ 1`.** The substitution `t = e^{2u}` gives `F(m) = 2^{m+1}∫_0^∞ u^m h`. Two integrations by parts then
     turn `B(n) = 32C(2n,2)F(2n−2) − F(2n)` into `2^{2n+4}∫u^{2n}Φ`. With `gammaMathlib_eq` this gives
     `γ(n) = 32·n!/(2n)!·b_n`.
   * **`n = 0`.** The boundary term is `h'(0) = θ₀(1)/2 + 2θ₀'(1)`. Differentiating Mathlib's
     `evenKernel_functional_equation` at `t = 1` gives `θ₀'(1) = −(2θ₀(1)+1)/8`, so `h'(0) = −1/4`.
   * **Analytic bookkeeping.** On `u ≥ 0` every series is dominated by `L·K³e^{−π(K−1)}·e^{−u}` (`mono_le`).
     This single bound gives continuity, integrability, termwise integration
     (`integral_tsum_of_summable_integral_norm`), the per-term integrations by parts, and the derivative of the
     series.
2. **Turán from a monotone ratio** (`Chebyshev.lean`).
   * **Two moment identities.** Integration by parts gives `∫u^{2n+1}Φ'·… = −(2n+1)b_{2n}`. With the weight
     `w = u^{2n+2}Φ` this means `∫R·w = (2n+1)b_{2n}` and `∫u²R·w = (2n+3)b_{2n+2}`.
   * **One-point Chebyshev inequality.** Let `m̄ = ∫u²w/∫w` and `c = R(√m̄)`. The integrand
     `(u² − m̄)(R(u) − c)w(u)` is pointwise `≥ 0` because `R` is monotone. Integrating it gives
     `∫u²Rw·∫w ≥ ∫u²w·∫Rw`, which is exactly `(2n+3)b_{2n+2}² ≥ (2n+1)b_{2n}b_{2n+4}`.
   * **Connection to log-concavity.** In the variable `v = u²`, the hypothesis is the log-concavity of `Φ(√v)`.
     The inequality is the Turán inequality with the CNV factor `(2n−1)/(2n+1)`. After multiplying by
     `n!/(2n)!`, the factor is absorbed and the result is exactly `γ(n+1)² ≥ γ(n)γ(n+2)`.
3. **Degree 2 hyperbolicity.** `J^{2,n} = γ(n) + 2γ(n+1)X + γ(n+2)X²` has leading coefficient `γ(n+2) > 0` and
   discriminant `4(γ(n+1)² − γ(n)γ(n+2)) ≥ 0`. It factors over `ℝ`, so `card roots = 2`.

## The proof of `CVHyp` (files `CV*.lean`, 2026-11-04)

**Literature (level 3).** `CVHyp` says that `log Φ(√t)` is concave on `0 < t < ∞`, since
`d/dv[−log Φ(√v)] = R(√v)/2`. This is a theorem of Csordas–Varga, *Moment inequalities and the Riemann
hypothesis*, Constr. Approx. 4 (1988) 175–198, and the key property behind Csordas–Norfolk–Varga, Trans. AMS
296 (1986) 521–541. The Lean proof below does not follow their argument, which was not re-read.

**Reduction.** `R = −Φ'/(uΦ)` has `R' = G/(uΦ)²` with `G = Φ(Φ' − uΦ'') + uΦ'²` (`hasDerivAt_ratio`).
It suffices to show `G > 0` on `(0,∞)` (`Gfun_pos`), and then `monotoneOn_of_deriv_nonneg` applies.

**Derivative chain in polynomial form (`CVSeries`).** With `z_k = πK_k e^{2u}`, every derivative of
`φ_k` has the form `e^{u/2} p(z_k) e^{−z_k}`. Here `d/du` acts as `p ↦ (p + 4zp' − 4zp)/2` on integer
lists (`stepZ`). Put `Zs 0 = 2z² − 3z` and `Phi i = Σ_k e^{u/2} Zs_i(z_k) e^{−z_k} / 2^i`. Then
`hasDerivAt_Phi : HasDerivAt (Phi i) (Phi (i+1) u) u` holds on all of `ℝ`, with local domination of the
series by `K^n e^{−cK}`. We also have `PhiR_eq : PhiR = Phi 0` and `PhiD_eq : PhiD = Phi 1`.

**Evenness (`CVEven`).** `H(u) = e^{u/2}(2θ₀(e^{2u}) + 1)` is even by Mathlib's
`evenKernel_functional_equation`, and `Φ = H''/4 − H/16`. So `Phi 0` is even, the chain alternates
parity, and `Phi_odd_zero : Phi (2j+1) 0 = 0`. This is the cancellation that defeats every termwise
argument near `0`.

**Interval arithmetic (`CVExp`, `CVSigma`).** We reuse the fixed-point `Iv` (`2^{-192}`) of
`JensenThreshold/Tail` with outward rounding.
* `expPt` encloses `e^{a}`: 24 Taylor terms with the `Real.exp_bound'` remainder, after 12 halvings, then
  12 squarings.
* `expNeg` encloses `e^{−x}` on an interval and is always sound.
* `σ_l(x) = Σ_k l(K_k x)e^{−(K_k−1)x}` is enclosed by `k₁` exact terms plus a geometric tail
  `2A(1 + K_{k₁}x)^n e^{−(K_{k₁}−1)x}` (`tail_le`, with the ratio condition proved from `e^y ≥ 1+y`).
* Cells are `u ∈ [p/2^12, q/2^12]`. `x = πe^{2u}` is enclosed by monotonicity in `u`, with `π` taken from
  `pi_gt_d20` and `pi_lt_d20`.

**The three regions.** Let `x = πe^{2u}`, so that `G = e^u e^{−2x} QR/4` with
`QR = σ₀(2σ₁ − uσ₂) + uσ₁²`.
1. **`0 < u ≤ u₀ = 737/2^12 ≈ 0.18` (`CVRegionB`).**
   * Taylor's theorem (`Tail.taylor_bounds`) uses the vanishing odd `c_i` and the bound
     `|Φ^{(10)}| ≤ 8·10⁹` on `[0,u₀]` (`Phi10_bound`, a 67-cell cover, `CVDataM`).
   * It gives `G = u³(Ph·W + V²)`, where `Ph`, `W`, `V` are explicit even polynomials with remainders
     `θ_iu^j`, and `c_{2j} = Φ^{(2j)}(0)` is enclosed through `π`.
   * `Ph·W + V² > 0` is checked on 8 cells (`CVDataB`). The limit `G/u³ → 9.49` at `0` has a 13% margin.
2. **`u₀ ≤ u ≤ 12` (`CVRegionA`).**
   * Split `σ_i = Zs_i(x) + τ_i`. The `k = 1` part is exact:
     `Q0R = x²(32x³(2u−1) + 4x²(42−48u) + 240x(u−1) + 90)`.
   * The cross terms come from the enclosed tails `τ_i`: two exact terms plus the geometric tail from
     `K = 16`.
   * The check covers 52 adaptive cells (`CVDataA`).
3. **`u ≥ 12` (`QR_pos_large`).** The `k = 1` part satisfies `Q0R ≥ x⁵`. For the cross terms,
   `|cross| ≤ 9x·661(2x)⁵·1322(5x)⁵e^{−3x} ≤ 4.9·10¹² x³`, using `e^{3x} ≥ (3x)⁸/8!` and
   `x ≥ 3e^{24} > 8·10⁶`.

**Kernel cost.** `CVDataM` takes 89 s, `CVDataA` 38 s and `CVDataB` 27 s. Peak RSS is about 9 GB, of which
about 5.5 GB is the mmapped imports. Each cell is its own `decide +kernel` theorem. A single
`decide +kernel` over the whole list exhausts memory, and recomputing `stepZ` inside the kernel is
exponential. For that reason the `Zs i` used in region B are literals (`Zl`, `Zs_eq_Zl`).

**Numerics (level 4, earlier session).** `scripts/gorzxi_eff/cv_grid.py`: `dR/du > 0` on a 3000-point
grid, with `(dR/du)/u → 47.67` at `0`. The prototypes of this session are `cv_k1.py` (exact `k = 1`
polynomials), `cv_taylor.py` (Taylor-model feasibility) and `cv_proto.py` (an `mpmath.iv` mirror of the
checkers). The cells were found by `cv_subdiv.lean` (compiled `#eval` bisection), stored in `cv_cells.txt`,
and written out by `cv_gen_data.py`.

## Feasibility of the GORZ route for `d ≥ 3` (honest assessment)

* **The existing effective constants are hopeless for a kernel-checked finite range.**
  * The moment-recursion step of `GORZXi` needs `log(M+1)⁴ ≤ (M+1)/4`, which already forces `M ≳ 6·10⁴`.
  * The constants `B_q`, `Λ_k` grow rapidly with `k`, so the resulting `N₀(d)` is far beyond `10⁵` for `d ≥ 3`.
  * GORZ themselves needed certified data up to `n ≈ 10⁶`.
  * Every `γ(n)` is a theta integral. In the kernel, each one would need a certified quadrature, using interval
    arithmetic for `exp` and `log` on a moving peak at `u* ≈ ½log(n/(π u*))`, to relative precision of about
    `δ(n)^d`. At this scale that is infeasible.
* **Recommended route for `d = 3`.** Use the analogue of this note: a structural kernel property plus
  algebra, with no finite range. Dimitrov–Lucas (Proc. AMS 139 (2011) 1013–1022) prove the higher-order Turán
  inequalities `4(γ_n²−γ_{n−1}γ_{n+1})(γ_{n+1}²−γ_nγ_{n+2}) ≥ (γ_nγ_{n+1}−γ_{n−1}γ_{n+2})²` in CNV's
  normalization from properties of the kernel `Φ`.
  * They likely use the same `CVHyp`-type log-concavity together with a moment argument. This has not been checked.
  * A Lean version would reuse `gamma_eq_mom`, `kernelMom_PhiR` and the Chebyshev machinery.
* **For `4 ≤ d ≤ 8`.** No structural proof is known to me. GORZ's own proof is a sketch, with `n ≤ 10⁶` handled by
  floating-point Hermite matrices, so the cases `d ≥ 4` are level (3) at best in the literature. The level (4)
  check below agrees for `n ≤ 300`.

## Numerical check of `d ≤ 8`, small `n` (level 4)

The script is `scripts/gorzxi_eff/jensen_small_n.py 300`. It computes `γ(n) = 32·n!/(2n)!·∫u^{2n}Φ` by mpmath
quadrature at 50 digits. The values `γ(0) = 3.97696622551`, `γ(10) = 1.63233804903e−17` and
`γ(100) = 6.57772637858e−205` reproduce the values in GORZ_XI.md and GORZ. For `2 ≤ d ≤ 8` and `0 ≤ n ≤ 300` it
counts real roots exactly with a Sturm sequence on rationalized 45-digit coefficients. **All `7 × 301` polynomials are hyperbolic (0 failures).**

## Files

All files are new. Nothing in `GORZXi/`, `GORZ/` or `JensenThreshold/` was modified.

| File | Contents |
|---|---|
| `RamanujanTau/GORZXiEff/Chebyshev.lean` | `mom`, `KernelReg`, `KernelMom`, `ratioR`, `ibp_of`, `mom_pos`, **`turan_mom`** |
| `RamanujanTau/GORZXiEff/Turan2.lean` | `fq`, `fq_succ`, **`turan_seq`**, `hyperbolic_quadratic`, `jensenSeq_two`, **`jensen2_hyperbolic`** |
| `RamanujanTau/GORZXiEff/PhiKernel.lean` | `mono`, `mono_le`, `summable_cK`, the `Dom` toolkit, `phik`, `PhiR`, `PhiD`, `hk`, `PhiR_pos`, `ibp_PhiR`, **`kernelMom_PhiR`**, `FXi_eq_H` (`t = e^{2u}`), `mom_PhiR_succ`, **`gammaMathlib_eq_mom`** |
| `RamanujanTau/GORZXiEff/Gamma0.lean` | `Tth`, `hasDerivAt_Tth`, **`Tth'_one`** (θ₀'(1) from the functional equation), `hasSum_hk'_zero`, `gammaMathlib_zero`, **`gammaMathlib_zero_eq_mom`** |
| `RamanujanTau/GORZXiEff/Main.lean` | `hasDerivAt_PhiR`, **`CVHyp`**, **`gamma_eq_mom`**, **`turan_gamma`**, **`jensen2_gamma`**, `#print axioms` |
| `RamanujanTau/GORZXiEff/CVSeries.lean` | `pe`, `stepZ`, `Zs`, `tz`, `Ser`, **`hasDerivAt_Ser`**, `Phi`, **`hasDerivAt_Phi`**, **`PhiR_eq`**, **`PhiD_eq`** |
| `RamanujanTau/GORZXiEff/CVEven.lean` | `theta_fe`, `Hf_even`, `odd_of_even`, `even_of_odd`, `Phi0_eq` (`Φ = H''/4 − H/16`), **`Phi_odd_zero`** |
| `RamanujanTau/GORZXiEff/CVExp.lean` | `expSer`, `expPt`, **`mem_expPt`**, `expNeg`, **`mem_expNeg`** |
| `RamanujanTau/GORZXiEff/CVSigma.lean` | `sig`, `Ser_eq_sig`, `gT_ratio`, **`tail_le`**, `peIv`, `sigIv`, **`mem_sigIv`**, `tauIv`, **`mem_tauIv`**, `piIv`, `xCell`, `uCell` |
| `RamanujanTau/GORZXiEff/CVRegionA.lean` | `QR`, `Q0R`, `crossR`, `QR_split`, `QIvA`, `cellA`, **`cellA_sound`**, `allCells`, **`cover_sound`** |
| `RamanujanTau/GORZXiEff/CVRegionB.lean` | `Zl`, `Zs_eq_Zl`, `phiIvB`, `cB`, `cellM`, **`cellM_sound`**, `gBIv`, `gBR`, `Gfun`, **`G_eq_gBR`** (Taylor model), `cellB`, **`cellB_sound`** |
| `RamanujanTau/GORZXiEff/CVData{M,B,A}.lean` | per-cell `decide +kernel` certificates and `cover{M,B,A}_ok` (generated) |
| `RamanujanTau/GORZXiEff/CVMain.lean` | `Phi10_bound`, `Gfun_pos_small`, `QR_pos_mid`, **`QR_pos_large`**, **`Gfun_pos`**, **`hasDerivAt_ratio`**, **`cvHyp_holds`**, **`turan_gamma_unconditional`**, **`jensen2_gamma_unconditional`**, `#print axioms` |
| `scripts/gorzxi_eff/` | `phi_check.py` (normalization `γ = 32 n! b_n/(2n)!`), `cv_grid.py` (`CVHyp` numerics), `jensen_small_n.py` (`d ≤ 8`, `n ≤ 300`) |

To build, run one process: `lake build RamanujanTau.GORZXiEff.Main`. Each module takes about 15 s once
`GORZXi` is built. For the unconditional results, build `lake build RamanujanTau.GORZXiEff.CVMain` and then
the data modules one at a time (about 3 min in total). The root `RamanujanTau.lean` is not modified.

## What remains

1. ~~Discharge `CVHyp` in Lean.~~ **Done (2026-11-04):** `cvHyp_holds`, `turan_gamma_unconditional` and
   `jensen2_gamma_unconditional` are axiom-clean. The new code is about 1.3k lines plus generated data.
2. **`d = 3` for all `n`.** Formalize Dimitrov–Lucas's argument on top of `gamma_eq_mom`. Their method still has
   to be checked against the moment machinery.
3. **`4 ≤ d ≤ 8`.** No route with a feasible kernel cost is known. GORZ's sketch needs `γ(n)` certified up to
   `n ≈ 10⁶`.
