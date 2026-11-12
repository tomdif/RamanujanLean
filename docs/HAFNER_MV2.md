# Hafner's (MV2) from the twisted second moment (2026-11-06)

> **Current status (2026-11-12).** The chain now reaches `HafnerFinal.tauL_positive_proportion_deligne` under `[DeligneBound]` alone; see [HAFNER_PROPORTION](HAFNER_PROPORTION.md). `QFProof5.qfHyp_deligne` and `mv2_deligne` close the quadratic-form/MV2 inputs under that hypothesis, and `SvStripD.s4Bound_deligne` supplies the final strip bound. This does not prove Deligne or an unconditional positive-proportion theorem.
> The earlier checkpoints and gap lists below describe the development at that stage.

**Status.** The implication (MV2) ⇐ `DiagHyp` is proved in Lean: axiom-clean, unconditional apart
from the named hypothesis. The further step `DiagHyp` ⇐ `QFHyp`, i.e. the Laurent / leading-coefficient
evaluation of `MainTw`, is **not done**.

    nice -n 10 lake build RamanujanTau.HafnerMV2.Main      # exit 0

* Every `#print axioms` (5 names) gives `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom`.
* 4 new files, about 450 lines. No committed file was modified.

## Headline

```lean
theorem mv2_of_diag {θ : ℝ} (hθ0 : 0 < θ) (hθ : 136 * θ ≤ 1 / 600) (hD : DiagHyp θ) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T
```

The left side is exactly the (MV2) conjunct of `SelbergCoeffs.SelbergMollHyp` and
`HafnerProportion.SelbergHyp`. The mollifier is `bSel`, i.e. `b = α(1 − log n/log y)` with `y = ⌊T^θ⌋`.
The admissible range is `θ ≤ 1/81600`.

```lean
def DiagHyp (θ : ℝ) : Prop :=
  ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ X ∈ Icc (T / 2) (3 * T),
    ‖DiagSum (βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ X (X ^ (299 / 300 : ℝ))‖ ≤ B * T
```

* `DiagSum β y X H = Σ_{p,q∈[1,y]²} κ(p,q)·MainTw(h_p, h_q, X, H)`.
* `h_p = p₁p₂` and `κ = ½β(p₁)β(p₂)β(q₁)β(q₂)(h_p h_q)^{−1/2}`.
* `MainTw` is the smoothed diagonal of `TwistedMoment`, so `DiagSum` is the full diagonal (`kM = hN`)
  contribution to the mollified mean square up to height `X`.
* It mentions no `L`-values. It does contain the explicit smoothing integrals `P̃` of the fixed weight `V`.

## Method

1. **Expansion** (`Expand.normSq_Mc_sq`).
   * On the line, `M(6+iu)² = Σ_{p} β(p₁)β(p₂) h_p^{−1/2} h_p^{−iu}`. This uses `cpow_line`:
     `n^{11/2−(6+iu)} = n^{−1/2} e^{−iu log n}`.
   * Hence `|M²|² = Σ_{p,q} κ(p,q)((h_p/h_q)^{iu} + (h_q/h_p)^{iu})`, using real coefficients and
     symmetrising in `(p, q)`.
2. **Averaging** (`Av_LM2`). The `u`-average `Av` commutes with finite sums (`Av_sum`), so
   `Av(|LM²|²) = Σ κ·TwAv(h_p, h_q)`.
3. **Twisted moment** (`avg_err`).
   * Apply `TwistedMoment.twisted_moment` to each pair, using `|κ| ≤ ½` (from `|bSel(n)| ≤ √n`,
     unconditional) and `h_p h_q ≤ y⁴`.
   * Over the `y⁴` pairs this gives `‖Av − DiagSum‖ ≤ (C/2) y^{136} X^{599/600}`.
4. **Sharp cutoff** (`sharp_le`).
   * For `G ≥ 0`, `I(u) = ∫_{16}^u G` is monotone. So
     `∫_T^{3T} G ≤ Av_{[3T, 3T+H₃]} − Av_{[T/2, T/2+H₁]}`, with `H = X^{299/300}` and `T/2 + H₁ ≤ T`.
5. **Assembly** (`mv2_of_diag`).
   * `∫_T^{3T}|LM²|² ≤ ‖DiagSum(3T)‖ + ‖DiagSum(T/2)‖ + C y^{136}(3T)^{599/600} ≤ (2B + 3C) T`.
   * This uses `y^{136} ≤ T^{136θ}` and `136θ + 599/600 ≤ 1`.
   * It needs `T ≥ 2^{301}`, so that `T/2 ≥ 2^{300}`.

## Gaps

1. **`DiagHyp` ⇐ QF is not formalised.** This is the leading-coefficient evaluation the coordinator asked for.
   * For the pair `(h_p, h_q) = (h, k)`, `g = (h,k)`, `h₁ = h/g`, `k₁ = k/g`:
     `MainTw = (2/√(hk))·g·Σ_r λ(h₁r)λ(k₁r) r^{−1} P̃(log(h₁k₁r²), 0, X, H)`.
   * Evaluating it needs, uniformly in `h₁k₁ ≤ y⁴` with polynomial loss:
     * (a) `Σ_{r≤x} λ(h₁r)λ(k₁r) = r₀ ρ(h₁)ρ(k₁) x + O(x^{1−η}(h₁k₁)^A)`, via `D_{h,k}(s) = R(s)ρ(h₁)ρ(k₁)`.
       This is Hecke multiplicativity: factor `r = r₁r₂` with `r₁ | (h₁k₁)^∞` and `(r₂, h₁k₁) = 1`. It also
       needs the coprime-restricted Rankin asymptotic. Convergence of `ρ_p` without Deligne uses
       `|λ(p^j)| ≪ p^{11j/40}` (`TauPNTUncond.weil_uu`).
     * (b) the derivative `ρ'/ρ`, giving the `log` companions.
     * (c) the `V`-smoothing: Mellin transform of `V`, double pole at `w = 0`, giving
       `X(log X + const + ρ'/ρ terms)`.
   * Then `DiagSum(X) = 2r₀ ∫^X Q_t dt + O(X^{1−η'})`, with `Q_t` the form of `docs/SELBERG_COEFFS.md` §3:
     `Q_t = Σ_{h,k≤y²} c(h)c(k)/[h,k]·ρ(h₁)ρ(k₁)[log(t/2π) − ½log(h₁k₁) + γ_Δ + (ρ'/ρ)(h₁) + (ρ'/ρ)(k₁)]`,
     where `c = b ∗ b`.
   * Hence **`QFHyp`** — `Q⁰(c) = Σ c(h)c(k)ρ(h₁)ρ(k₁)/[h,k] ≪ 1/log y` plus the companion forms `≪ 1`
     (`SELBERG_COEFFS` §3, `SELBERG_DELANGE` §4) — implies `DiagHyp`.
   * `QFHyp` is **not stated in Lean** here. Stating it needs `ρ` and `ρ'` as definitions, and the
     bridge (a)–(c) is the missing piece, estimated at 1.5–3k lines.
   * The Selberg–Delange agent should target the §3 form. `DiagHyp` is the interface on this side.
2. The (SK) conjunct of `SelbergMollHyp` is untouched.
3. `θ ≤ 1/81600` is far from optimal. It is inherited from `(hk)^{33}` and `1/600`.

---

## 2026-11-06 (later): `HafnerBridge/` — `QFHyp` stated (checkpoint)

**Status.** `QFHyp` is defined in Lean and its local factors are shown to be well defined. The
bridge `DiagHyp θ ⇐ QFHyp` is **not yet proved**; this section is a clean checkpoint.

    nice -n 10 lake build RamanujanTau.HafnerBridge.Main      # exit 0

* All `#print axioms` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom`.
* 3 files: `QF.lean`, `Local.lean`, `Main.lean`.

### The statement (`RamanujanTau/HafnerBridge/QF.lean`; keep stable)

The objects, with `λ = SubconvexityCond.lam`:

* `D_p = Σ_j λ(p^j)² p^{−j}`.
* `N_p(a) = Σ_j λ(p^{j+a})λ(p^j) p^{−j}`.
* `D_p'`, `N_p'(a)`: the same series with an extra `−j log p`.
* `ρ_p(a) = N_p/D_p`.
* `ρ_p'(a) = (N_p' D_p − N_p D_p')/D_p²`.
* `ρ(m) = Π_{p^a∥m} ρ_p(a)` (`rho`).
* `ρ₁(m) = Σ_{p^a∥m} ρ_p'(a) Π_{q≠p} ρ_q` (`rho1`), i.e. `d/ds ρ(m,s)|_{s=1}`.
* `r₀ = c0` (`r0`), `γ_R/r₀ = gammaD/c0` (`gamR`).
* `c = b ∗ b` with `b = βSel y` (`cS`).
* `h₁ = h/(h,k)`, `k₁ = k/(h,k)`.

The forms:

    Q0 y = Σ_{h,k≤y²} c(h)c(k)/[h,k] · ρ(h₁)ρ(k₁)
    Q1 y = Σ_{h,k≤y²} c(h)c(k)/[h,k] · ( ρ(h₁)ρ(k₁)(γ_R/r₀ − ½log(h₁k₁)) + ρ₁(h₁)ρ(k₁) + ρ(h₁)ρ₁(k₁) )
    QFHyp :≡ ∃ B y₀, ∀ y ≥ y₀, |Q0 y| ≤ B / log y ∧ |Q1 y| ≤ B

**Normalisation (derived).**

* `DiagSum(X) = Σ_{h,k} c(h)c(k)/[h,k] Σ_r λ(h₁r)λ(k₁r) r^{−1} P̃(log(h₁k₁r²), 0, X, H)`, using
  `x = [h,k]r` in `MainTw`.
* For each `t`, `Σ_r λ(h₁r)λ(k₁r)/r · V(log(h₁k₁r²) − 2log(t/2π))` is a Mellin integral with kernel
  `e^{w²}(h₁k₁)^{−w}(t/2π)^{2w} D(1+2w) dw/w`.
* Its residue at `w = 0` is `r₀[ρρ(log(t/2π) − ½log h₁k₁) + ρ₁ρ + ρρ₁] + γ_R ρρ`. This uses
  `D(1+2w) = R(1+2w)ρ(h₁,1+2w)ρ(k₁,1+2w)` and `R(s) = r₀/(s−1) + γ_R + …`.
* Hence `DiagSum(X) ≈ r₀ ∫^X (Q0·log(t/2π) + Q1) dt` (`P̃`-weighted). Under `QFHyp` this is
  `≪ X(log X/log y + 1) ≪_θ X`, which is `DiagHyp`.

### Proved (`Local.lean`, unconditional)

* `lam_bound`: `|λ(n)| ≤ C n^{11/40}`, from `TauPNTUncond.tau_le_uniform`.
* `term_bound`, `summable_Np`, `summable_Np'`, `summable_Dp`, `summable_Dp'`: the local series converge
  with ratio `p^{−9/20}`.
* `one_le_Dp`: `D_p ≥ 1`. So `ρ`, `ρ₁` are genuine and not junk `tsum`s.

### Remaining for `DiagHyp θ ⇐ QFHyp`

All of the following must hold uniformly in `h₁k₁ ≤ y⁴`, with polynomial loss:

* **(a)** `Σ_{r≤x} λ(h₁r)λ(k₁r)/r = r₀ρ(h₁)ρ(k₁) log x + K₁(h₁,k₁) + O(x^{−η}(h₁k₁)^A)`, with
  `K₁ = r₀(ρ₁ρ + ρρ₁) + γ_R ρρ`. The **constant term** is required, not just the leading term: the
  companion `Q1` needs it exactly.
  * Route: write `r = s·m` with `s | (h₁k₁)^∞` and `(m, h₁k₁) = 1`, so
    `λ(h₁r)λ(k₁r) = λ(h₁s)λ(k₁s)λ(m)²`.
  * Then use `Σ_{m≤x,(m,q)=1} λ(m)²/m = r₀∏_{p|q}D_p^{−1} log x + γ_q + O(x^{−1/5}q^ε)`, coprime
    sieving of `AA_asymp`.
  * Sum over `s` using `term_bound` for convergence.
  * Identify the Euler products with `ρ`, `ρ₁`.
* **(b)** `ρ₁` arises as the `log s` moment of the `s`-sum. This needs the local identity
  `Σ_j (j log p)λ(p^{j+a})λ(p^j)p^{−j} = −N_p'(a)` (definitional) and the product rule over `p | h₁k₁`.
* **(c)** Partial summation of (a) against `V(2 log r + log h₁k₁ − L)`, then the `P̃` average.
  The symmetric `V` (`V(v) + V(−v) = 1`) makes the boundary constant vanish.
* Then sum over `h, k ≤ y²` with `|c| ≤ d(h)√h`. The errors are `≪ T^{1−η'} y^{A'}`, which is power-saving for small θ.

Estimate 1.5–2.5k lines.

---

## 2026-11-06 (later still): `HafnerBridge2/` — `DiagHyp θ ⇐ QFHyp` proved; (MV2) `⇐ QFHyp`

**Status.** The bridge is done. Items (a)–(c) are proved in Lean, axiom-clean, with no hypothesis
other than `QFHyp` itself.

    nice -n 10 lake build RamanujanTau.HafnerBridge2.Main      # exit 0

* Every `#print axioms` (12 names, `HafnerBridge2/Main.lean`) gives `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom`.
* 10 new files, about 2.5k lines. No committed file was modified. `HafnerBridge/QF.lean` (the `QFHyp`
  statement) is unchanged and used as is.

### Headlines (`RamanujanTau/HafnerBridge2/Assemble.lean`)

```lean
theorem diag_of_QF {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 260) (hQ : QFHyp) : DiagHyp θ

theorem mv2_of_QF {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600) (hQ : QFHyp) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T
```

`mv2_of_QF` is `HafnerMV2.mv2_of_diag ∘ diag_of_QF`. So the (MV2) conjunct of `SelbergMollHyp` is now
reduced to the purely arithmetic `QFHyp`: `Q⁰(y) ≪ 1/log y` and `Q¹(y) ≪ 1`.

### Method

**(a)+(b): the uniform twisted Rankin asymptotic.** This is `Twisted.twisted_asymp`. There is `Z` such that for all
coprime `h, k ≥ 1`:

    |Σ_{r≤N} λ(hr)λ(kr)/r − r₀ρ(h)ρ(k) log N − K₁(h,k)| ≤ E N^{−1/5},   E + |r₀ρρ| + |K₁| ≤ Z (hk)⁴,

where `K₁ = γ_Δ ρ(h)ρ(k) + r₀(ρ₁(h)ρ(k) + ρ(h)ρ₁(k))`.

* *Local algebra* (`Lam.lean`). We work in `ℝ⟦X⟧` with `D_p = Σ λ(p^j)² X^j` and
  `U_{p,a} = Σ λ(p^{j+a})λ(p^j) X^j`.
  * From the Hecke recursion, `D_p · (1 − bX + bX² − X³) = 1 + X`, where `b = λ_p² − 1` (`Dps_mul_P`).
    So `e_p = D_p⁻¹ = P/(1+X)` has `|coeff_j e_p| ≤ 4 + 2λ_p²` uniformly in `j`.
  * Set `g_{p,a} = U_{p,a} e_p`, so that `g·D = U`.
* *Peeling one prime* (`Twisted.T_peel`). Write `h = p^a h'` with `p ∤ h'k`. Then
  `λ(hr)λ(kr) = Σ_{p^j ∣ r} g_j λ(h'r/p^j)λ(kr/p^j)`. This uses Mordell multiplicativity and `g·D = U`.
* *Analytic step* (`Peel.peel_asymp`). If `A_F(N) = c log N + K + O(E N^{−1/5})`, then the convolution
  `f = g ⊛_p F` has `A_f(N) = cG log N + (KG − cG₁) + O((2E + 3|c| + |K|) S N^{−1/5})`, where
  `S = Σ (1 + j log p)|g_j| p^{−4j/5}`.
* *Evaluation* (`Eval.lean`). At `X = 1/p` we get `G = ρ_p(a)` and `G₁ = −ρ_p'(a)`. The second comes
  from `θ = X d/dX` with `θ(fg) = θf·g + f·θg` and `θ(e·D) = 0`. This is exactly the `ρ₁` of `QF.lean`;
  item (b) is therefore definitional.
* *Uniformity* (`Eval.Sg_le`, `Twisted.fiveS_le`).
  * `S ≤ 6C⁴W₀ p^{3a}`, using `|λ(n)| ≤ C n^{11/40}` (no Deligne).
  * Primes `p ≥ P₀ = ⌈30C⁴W₀⌉ + 1` cost `p^{4a}`. Primes below `P₀` cost an extra factor `P₀`.
  * Hence the constant is `Z₀ P₀^{P₀} (hk)⁴`.
* *Induction.* Strong induction on `hk`, peeling the least prime of `h`, or of `k` by symmetry. The
  base case is `GoodSecondTerm.AA_asymp`.

**(c): the `V`-smoothing and the `P̃` average.**

* *Smoothing* (`Smooth.abs_Dsum_sub_le`). Any sequence with `Σ_{m<k} f(m) = c log k + K + O(E k^{−1/5})`
  satisfies

      Σ f(m) V(2 log(m+1) − L) = cL + 2K + O((E + 2|c| + |K|)(1+|L|)e^{−L/10}).

  This is the `DiagD2` argument with nonnegativity removed. The boundary constant `2K` comes from
  `∫g = 2` and `∫u g = 0`, which is the symmetry `V(v) + V(−v) = 2`.
* *The `MainTw` sequence* (`Pair.logAsym_fseq`).
  * `f(m) = ι_k(m+1)ι_h(m+1)/(m+1)` has partial sums `[h,k]⁻¹ A_{h₁,k₁}(⌊N/[h,k]⌋)`.
  * Its constants are `c/ℓ` and `(K − c log ℓ)/ℓ`, with error `(2E + 2|c| + |K|)ℓ`.
* *The `P̃` average* (`Wint.lean`).
  * `Ptil(Λ, 0, X, H) = Wint X H (WV Λ)`.
  * The `m`-sum and the `t`-integrals are interchanged by dominated convergence (`hasSum_Wint`).
  * `Φ(t) = Σ_m f(m) V(…)` is continuous (Weierstrass).
* *One pair* (`PairBound.pair_eval`).
  * `MainTw(h,k) = 2√(hk) W(h,k)`, with
    `|W − (2r₀/[h,k])(q₀ I₁ + q₁ I₀)| ≤ Z (hk)⁵ (X+H)^{9/10}`.
  * Here `I₀ = Wint 1`, `I₁ = Wint log(t/2π)`, `q₀ = ρ(h₁)ρ(k₁)`, and `q₁` is the `Q¹` summand.
  * This uses `log(h₁k₁) = 2 log[h,k] − log hk` and `r₀ · gamR = γ_Δ` (from `r₀ > 0`, via
    `RankinError.petNormSq_pos`).
* *Assembly* (`Assemble.diag_decomp`).
  * `κ · 2√(h_p h_q) = cP(p) cP(q)`.
  * Regrouping `Σ_{p∈[1,y]²} β(p₁)β(p₂) F(p₁p₂) = Σ_{h≤y²} c(h) F(h)` gives
    `DiagSum = 2r₀(Q⁰(y) I₁ + Q¹(y) I₀) + R`, with `|R| ≤ Z y^{26}(X+H)^{9/10}`.
* *`diag_of_QF`.*
  * `I₀ ≤ X + H ≤ 6T` and `I₁ ≤ 6T log(6T)`.
  * `log y ≥ (θ/2) log T` once `T^θ ≥ 2(|y₀| + 4)`.
  * Hence `|DiagSum| ≤ (12 r₀ B (4/θ + 1) + 6Z) T`, using `26θ ≤ 1/10`.

### Numerical check

`scripts/hafner_bridge/twisted_rankin.gp` (PARI, `nbthreads = 1`, output in `twisted_rankin.out`)
tests (a) with `τ` up to `1.2·10⁶`. The tested pairs `(h₁,k₁)` are `(1,1)`, `(1,2)`, `(2,3)`, `(1,4)`,
`(3,4)`, `(1,6)` and `(5,1)`.

* `S(x) − r₀ρρ log x` agrees with the predicted `K₁ = r₀(ρ₁ρ + ρρ₁) + γ_Δρρ` to `10⁻⁶`–`10⁻⁴`, the
  size of the expected fluctuation.
* Example: for `(2,3)` the predicted `K₁` is `−0.15721693` and `S(2·10⁵) − r₀ρρ log x` is `−0.15721780`.
* It also confirms `λ(h₁r)λ(k₁r) = λ(h₁k₁r)λ(r)` for coprime `h₁, k₁`.

### Remaining

1. **`QFHyp` itself** is the only open input to (MV2). It is the Selberg–Delange target of
   `RamanujanTau/SelbergDelange3/`, the other agent's work.
2. The (SK) conjunct of `SelbergMollHyp` is untouched, as before.
3. The exponents are crude: `(hk)⁵` per pair, `y^{26}` in total, and `θ ≤ 1/260` for `DiagHyp`. The
   (MV2) range `θ ≤ 1/81600` is still set by `mv2_of_diag`.
