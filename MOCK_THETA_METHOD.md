# A machine-checked proof of the Mock Theta Conjectures

*RamanujanLean (Lean package `RamanujanTau`), `RamanujanTau/MTC/`. All results below are kernel-checked; `#print axioms`
gives only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.*

## Statements

With `Φ(q) = −1 + Σ_{n≥0} q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n)` and `Ψ(q) = −1 + Σ_{n≥0} q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n)`
(the rank-type functions of `RankSpec.lean`), as identities in `ℤ⟦q⟧`:

```
MTC.mock_theta_conjecture_f0 :  f₀(q) = (q⁵;q¹⁰)²_∞(q¹⁰;q¹⁰)_∞ / ((q;q⁵)_∞(q⁴;q⁵)_∞) − 2Φ(q²)
MTC.mock_theta_conjecture_f1 :  q f₁(q) = q (q⁵;q¹⁰)²_∞(q¹⁰;q¹⁰)_∞ / ((q²;q⁵)_∞(q³;q⁵)_∞) − 2Ψ(q²)
```

with `f₀ = Σ q^{n²}/(−q;q)_n`, `f₁ = Σ q^{n²+n}/(−q;q)_n`. These are Hickerson's theorems (Invent. Math. 1988); the
proof follows Hickerson–Mortenson, *Hecke-type double sums, Appell–Lerch sums, and mock theta functions I*
(Proc. LMS 2014, arXiv:1208.1421). The formalization needed three ingredients that are, as far as we know, new.

## 1. Hecke-type double sums by Bailey pairs with explicit certificates

Andrews' Hecke-type identities are obtained from Bailey pairs whose `α` contain a partial theta polynomial
`V_n = Σ_{|j|≤n} (−1)^j q^{n²−j²}`. Each pair relation is proved by **creative telescoping with the partial theta
polynomial treated as a symbol** obeying its own first-order recurrence; the certificates were found by a linear-algebra
ansatz in sympy (`scripts/mtc_gap/f0_pair_certificate.py`) and the Lean proofs are finite `ring` computations.

| function | pair (relative to) | `α_n` | certificate | file |
|---|---|---|---|---|
| `f₀` | `β_n = 1/(−q;q)_n`, `a = 1` | `q^{T(n)} V_n − q^{T(n)+n−1} V_{n−1}` | `G(n,s) = qⁿ((1−qⁿ)q^{T(s)+s}V_s + 2(−1)^s q^{T(s)}) / ((q)_{n−s−1}(q)_{n+s})` | `MockTheta5F0Pair` |
| `f₁` | `β_n = 1/(−q;q)_n`, `a = q` | `q^{(3n²+n)/2}(1−q^{2n+1})/(1−q) · Σ_{|j|≤n}(−1)^j q^{−j²}` | `G1term` (see file) | `MockTheta5F1Pair` |

Through the limiting Bailey lemma (`a = 1` and `a = q`) these give
`(q;q)_∞ f₀ = Σ_{n≥0} Σ_{|j|≤n} (−1)^j q^{n(5n+1)/2 − j²}(1 − q^{4n+2})` and
`(q;q)_∞ f₁ = Σ_{n≥0} Σ_{|j|≤n} (−1)^j q^{n(5n+3)/2 − j²}(1 − q^{2n+1})`.

A third pair, for `ψ₀` (`a = 1`): `β_n = [n ≥ 1]`, `α_n = −(1 − q^{2n}) q^{2n²−n} Σ_{j=−n}^{n−1} (−1)^j q^{−j(3j+1)/2}`.
It is checked symbolically for `n ≤ 7` but not yet proved in Lean. With the `ρ₁ = −1, ρ₂ → ∞` Bailey lemma it gives
Chen–Wang's form of `J_{1,2}ψ₀`.

## 2. HM Theorem 0.3 by theta spaces and a zero count over `ℂ((t))`

HM prove `f_{n,n+p,n}(x,y,q) = g_{n,n+p,n}(x,y,q,−1,−1) + θ_{n,p}(x,y,q)/J̄_{0,np(2n+p)}` analytically: the difference
times a theta product is a theta function of too high a degree with too many zeros. The formalization replaces
complex analysis by **formal Laurent series**.

* **Entire bilateral series** (`Ent.lean`, `Conv.lean`). A series in `x` with coefficients in `L = ℂ((t))` (Hahn series)
  is *entire* when `val(F_k)` grows faster than every linear function of `|k|`. Entire series can be evaluated at
  every monomial `x = c tᵉ`, and they are closed under products, shifts and twists. The identity principle says an
  entire series vanishing at `c tᵉ` for infinitely many `c` is `0`. With `q = t^{qe}` and `y = cy t^{ey}`, the double sum
  `f(x,y,q)`, the Appell–Lerch sums (as Lambert series `A(X,z)`, `Lambert.lean`) and all theta functions become entire
  series or quotients of them.
* **Theta spaces** (`ThSpace.lean`, `ThFactor.lean`). `Th(m, μ)` is the set of entire `F` with `F(Qx) = μ x^{−m} F(x)`.
  The factor theorem and `zero_count` say an element of `Th(m)` vanishing at `m + 1` points that are pairwise
  inequivalent under `x ↦ Qx` is zero.
* **The auxiliary function.** `D = J̄f − J̄g − κ θ` satisfies `D(Qx) = μ x^n D(x)` (HM Prop 5.5, Lemma 5.9: `fV_FE`,
  `gNum_FE`, `thV_FE`). Multiplying by the pole-clearing product `P(x) = Π j(A_r(x)) Π j(B_s(x))` gives an entire series
  `F = P·D ∈ Th(m)`. The series of `P·g` is assembled from the `Λ_ℓ`-series `j(u)/(1 − Q^ℓ/u)` (`LamX`, `UDecL`)
  with uniform decay estimates.
* **Residue identities.** At a zero of a factor `j(B_{s₀})` only one Lambert pole term of `P·g` survives (the pole map
  `k ↦ (s(k), ℓ(k))` is injective), together with one column of `P·θ`. The resulting bracket vanishes by an
  `m`-dissection of a theta function (HM (1.2f)), modulo one monomial identity per summand (`brB_zero`, `brA_zero`).
  At the specialization point every coefficient is a power of a fixed root of unity (`Z84 = e^{πi/42}`,
  `W16 = e^{πi/8}`), so each monomial identity is an exponent identity decided by `norm_num` plus a congruence decided by
  `omega`. This is the "symbolic check": dozens of residue identities, each a kernel computation, with no numerics.

| instance | specialization | space | zeros | files |
|---|---|---|---|---|
| `f_{3,7,3}` (MTC₀) | `q = t⁴², x = i t¹⁰⁵, y = −i t¹⁰⁵` | `Th(55)` | 49 + 7 | `F373 … Zeros373` |
| `f_{3,7,3}` (MTC₁) | `x = i t¹⁸⁹, y = −i t¹⁸⁹` | `Th(55)` | 49 + 7 | `Zeros1` (generated) |
| `f_{1,4,1}` (ψ₀ family) | `q = t⁸, y = i t¹²` | `Th(16)` | 16 + 1 | `F141 … Zeros141` |

For `f_{1,4,1}` the vanishing `F ≡ 0` holds as a series in `x`, so HM Theorem 0.3 holds at *every* good `x` once one
`y` is treated.

## 3. The endgame: Appell–Lerch calculus and theta identities by zero counts

* The `g`-side at the point is a few Appell–Lerch sums `A(Q^a)` in base `Q³⁰` (`GX373`, `GX1`). The rank side gives
  `(1+φ)(q⁵;q⁵)_∞` as three Appell–Lerch sums (`RankALm`, `L5`, `L5b`). HM (2.2a–c) and changes of `z`
  (`LamAb`, `LamInv`, `Endgame1`, `Endgame1b`) make the unknown Appell–Lerch values cancel exactly
  (`endgame_reduce`, `endgame_reduce₁`).
* What remains is a theta-function identity. Weierstrass three-term relations (`ALTheta.weierstrass`) and HM (1.4b)
  handle the easy ones. A product-identity engine (`ProdId`) rewrites every theta function into atoms `(q^r;q^M)_∞`
  and closes the identity with `field_simp`. The hard one, HM (8.17), is HM (1.9), proved by another zero count:
  `F19 ∈ Th(Q³⁰, 10)` vanishes at 11 points (`H19`, `H19b`, `F19_zero`). Specialized at `x = 1` it gives (8.17) for
  `f₀`, and at `x = Q⁶` it gives (8.17) for `f₁`.

## χ₀ and the combinatorial conjecture (done, 2026-10-26)

The Andrews–Garvan corollary `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀` is proved (`MTC.Chi0L.rank_chi0`).
So is the χ₀ identity `χ₀ − 2 = 3(Φ − 1) − J₅²J_{5,2}/J_{5,1}²` (`Watson.chi0_identity`), and the theta identity
`ThetaId` that the HM route for χ₀ had reduced to (`MTC.Chi0L.thetaId`). All of these are axiom-clean.

They are proved by Watson's elementary route (G. N. Watson, *The mock theta functions (2)*, Proc. LMS 1937),
not by HM for χ₀. The files are in `RamanujanTau/Watson/`, and `docs/watson1937_R1_proof.md` has the transcription.
1. **Toolkit.** Locally finite sums of power series (Fubini, reindexing, parity split) and q-Pochhammer products.
   Euler's two expansions are proved from their q-difference equations; with them come the finite q-binomial and
   the even part of Euler's expansion.
2. **Ramanujan's (B₀)** `χ₀ = 2F₀ − φ₀(−q)`, by Heine's method. Watson expands `2χ₀/(q)_∞` and splits by parity,
   and `χ₀ − 1` reappears through the second series form (A₀) of χ₀.
3. **Watson's (2₀), (3₀)** `f₀ ± ϑ₄(q)G(q)`, by the same method in bases `q²` and `q⁴`.
4. **The closing theta identity** `4qψ(q²)H(q⁴) + ϑ₄G − 3ϑ₄(q⁵)G + 2(q¹⁰;q¹⁰)²J_{10,4}/J_{10,2}² = 0`.
   Its certificate is five HM (1.4b) `θ_mul` instances, found numerically (`scripts/watson/`). Lean checks it
   over the atoms `(q^r;q^{80})_∞`.
5. **Assembly.** `2·R1(q²) + (2₀) + 2·(3₀) − 3·MTC₀ + (★)` is the χ₀ identity at `q²`. Cancelling the
   substitution `q ↦ q²` gives the identity itself.

## Reproducing

`lake build` (8710 jobs). Generators for the zero files and the certificate searches are in `scripts/mtc_gap/`;
the step-by-step map is `MTC_GAP_MAP.md`.
