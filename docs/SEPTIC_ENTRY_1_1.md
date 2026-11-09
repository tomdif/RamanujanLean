# Ramanujan's septic theta identity: Lost Notebook Entry 1.1(i)

**Status:** PROVED in Lean (q-series form, plus product forms). 0 `sorry`, no `native_decide`, no new axioms.
Audit: `scripts/audit/septic.lean` reports `[propext, Classical.choice, Quot.sound]` for every theorem.
The page-206 special value is stated as a named Prop and verified numerically. It is not proved.

## Statement

Lost Notebook p. 206; Son, Acta Arith. 98 (2001); Andrews–Berndt, *Lost Notebook* (septic chapter).
The definitions follow Rebák, Ramanujan J. 60 (2023), arXiv 2112.11884, eq. (11):

    φ(q^{1/7})/φ(q⁷) = 1 + u + v + w,
    u = 2q^{1/7} f(q⁵,q⁹)/φ(q⁷),  v = 2q^{4/7} f(q³,q¹¹)/φ(q⁷),  w = 2q^{9/7} f(q,q¹³)/φ(q⁷),

where `f(a,b) = Σ_{n∈ℤ} a^{n(n+1)/2} b^{n(n−1)/2}` and `φ(q) = f(q,q)`. Rebák notes that Entry 1.1(iv)
alone does not say which of the three terms is u, v or w; eq. (11) fixes that assignment. Son, Andrews–Berndt
and Rebák all give u, v, w as these f-quotients, not as products. Under `q ↦ q⁷` (equivalently, the series
variable is `q^{1/7}`):

    φ(q)/φ(q⁴⁹) = 1 + u + v + w,
    u = 2q f(q³⁵,q⁶³)/φ(q⁴⁹),  v = 2q⁴ f(q²¹,q⁷⁷)/φ(q⁴⁹),  w = 2q⁹ f(q⁷,q⁹¹)/φ(q⁴⁹).

### Lean headline (`RamanujanTau/Septic/Dissection.lean`)

```lean
theorem septic_entry_1_1_i : phi * Ring.inverse (ramF 49 49) = 1 + u + v + w
-- u := 2 * X * ramF 35 63 * Ring.inverse (ramF 49 49), and similarly v (X^4, ramF 21 77), w (X^9, ramF 7 91)
theorem phi_seven_dissection :
    phi = ramF 49 49 + 2 * X * ramF 35 63 + 2 * X ^ 4 * ramF 21 77 + 2 * X ^ 9 * ramF 7 91
```

Here `ramF α β : ℤ⟦X⟧` is `f(q^α, q^β)`, and `phi = ramF 1 1`. The definition counts the `n` in the
window `[-N, N]`. `coeff_ramF` shows that this equals `Nat.card {n : ℤ // α n(n+1) + β n(n−1) = 2N}`,
the untruncated bilateral sum, for α, β ≥ 1. `isUnit_phi49` shows that φ(q⁴⁹) has constant term 1, so the
quotient is a genuine power-series quotient.

### Proof

The exponents collapse to squares:

| term | exponent |
|---|---|
| q·f(q³⁵,q⁶³) | 1 + 35n(n+1)/2 + 63n(n−1)/2 = (7n−1)² |
| q⁴·f(q²¹,q⁷⁷) | (7n−2)² |
| q⁹·f(q⁷,q⁹¹) | (7n−3)² |
| φ(q⁴⁹) | (7n)² |

So Entry 1.1(i) is exactly the 7-dissection of `Σ_{k∈ℤ} q^{k²}` by `k mod 7`:

- `card_sq_seven`: `#{k : k² = N} = c₀ + 2c₋₁ + 2c₋₂ + 2c₋₃`, where `c_j = #{n : (7n+j)² = N}`.
- The proof uses the equivalence `splitSeven : {k // P k} ≃ Σ r : Fin 7, {n // P (7n + r)}`.
- Classes `r` and `7 − r` pair under `n ↦ −n` (`cls_neg`) and `n ↦ n+1` (`cls_shift`).

No Jacobi triple product is needed for (i) itself.

### Product forms (`RamanujanTau/Septic/ProductForm.lean`)

`ramF_product`: for odd α and β,

    f(q^α,q^β) = rescale(−1)[(q^α;q^{α+β})_∞ (q^β;q^{α+β})_∞ (q^{α+β};q^{α+β})_∞]
               = (−q^α;q^{α+β})_∞ (−q^β;q^{α+β})_∞ (q^{α+β};q^{α+β})_∞.

- It is derived from the repo's signed triple product `RankProof.jtp_ab` (RankTheta.lean) by `q ↦ −q`.
- The signs cancel because α and β are odd and α+β is even. `ramF_eq_rescale_thetaS` does this with an explicit
  bijection `m ≥ 0 ↔ d`, `m < 0 ↔ −(d+1)`.
- `rescale_Pfin` shows that `rescale(−1)` turns each factor `(1 − q^{b+ai})` into `(1 + q^{b+ai})` for odd b and even a.
- `septic_product_forms` instantiates this for all five thetas: φ(q), φ(q⁴⁹), f(q³⁵,q⁶³), f(q²¹,q⁷⁷), f(q⁷,q⁹¹).
  For example, `u = 2q (−q³⁵;q⁹⁸)(−q⁶³;q⁹⁸)(q⁹⁸;q⁹⁸)_∞ / [(−q⁴⁹;q⁹⁸)²(q⁹⁸;q⁹⁸)_∞]`.

## Numerics (`scripts/septic/`)

- `check_dissection.py` checks:
  - the integer identity to q⁴⁰⁰⁰;
  - the exponent identities;
  - the JTP product forms to q¹⁵⁰⁰;
  - the real-variable Entry 1.1(i) at q = 0.1, 0.5, 0.9 and e^{−π/√7}, with error ≤ 1e-39;
  - the ordering 2 > u > v > w > 0 (Rebák, Lemma 3.3).
- `check_page206.py` checks:
  - Theorem 4.1 to 60 digits;
  - that Ramanujan's printed `7^{+3/4}` fails, giving a ratio of 0.054;
  - that at q = e^{−π/√7}, u, v, w equal the three cosine terms **in the order (B, A, C)**: u matches the
    `cos(2π/7)/(2cos²(3π/7))` term. Theorem 4.1 lists the terms in a different order than u, v, w;
  - p = uvw = 1 and φ⁴(q)/φ⁴(q⁷) = 7 at that point;
  - Entry 1.1(ii) [p = 8q²(−q;q²)_∞/(−q⁷;q¹⁴)_∞⁷], (iii), and (iv)/(v), at generic q.

## Page 206 (Rebák Theorem 4.1): scoping

The statement is fixed in Lean as `RamanujanTau.Septic.Page206Evaluation : Prop` (`Septic/Page206.lean`,
real `phiR q = Σ' n:ℤ, q^{n²}`). It is unproved. Rebák's proof proceeds as follows:

1. **Lemma 2.1**, `φ(e^{−π/√n}) = n^{1/4} φ(e^{−π√n})`. **Cheap in Lean:** Mathlib's
   `jacobiTheta_S_smul` gives θ(−1/τ) = (−iτ)^{1/2} θ(τ), with `jacobiTheta τ = Σ exp(πi n² τ)`, at τ = i√n.
2. **Transfer of our ℤ⟦X⟧ identity to real q ∈ (0,1).** This is moderate: summability, plus splitting the ℤ-indexed tsum by
   residue mod 7. Together with step 1 at n = 343 (√343 = 7√7), it already gives
   `φ(e^{−7π√7}) = 7^{−3/4} φ(e^{−π√7})(1 + u + v + w)` with u, v, w as theta values at q = e^{−π/√7}.
3. **p = 1 at q = e^{−π/√7}.** This needs Entry 1.1(ii) (a theta-product identity proved by Son), Lemma 2.3
   `p = 2√2 G_n/G_{49n}⁷`, and the class invariant **G₇ = 2^{1/4}** with G_{1/7} = G₇.
   - G_{1/n} = G_n is a Dedekind-eta transformation; Mathlib has `DedekindEta.lean`, but the S-transformation needs checking.
   - G₇ = 2^{1/4} is Weber/Ramanujan's evaluation and needs a degree-7 modular equation. **Hard.**
4. **φ⁴(q)/φ⁴(q⁷) = 7.** This follows from step 1 alone (Rebák uses Lemma 3.5 together with Lemma 2.1). **Cheap.**
5. **Entry 1.1(iv)/(v), with p = 1 and φ⁴/φ⁴ = 7.** The cubic becomes r(ξ) = ξ³ − 6ξ² + 5ξ − 1, whose roots are
   1/(2cos(kπ/7))². Proving (iv)/(v) themselves is Son's main theorem (degree-7 modular equations). **Hard.**
   The root-ordering argument (Lemmas 3.2–3.8: monotonicity of u_k, discriminant, the trig identity in Lemma 3.8)
   is elementary real analysis and trigonometry. It is moderate.
6. Reading off u = (α²p/β)^{1/7} and the others is then algebra plus `Real.rpow`.

**Named gaps** (any proof of Page206Evaluation would need):

- **Entry 1.1(ii)–(v) (Son 2001)**: the modular-equation core.
- **G₇ = 2^{1/4}**: or an equivalent direct evaluation p(e^{−π/√7}) = 1.

**Mathematica:** Rebák's proof of Theorem 4.1 does not use Mathematica. He uses it only in Theorem 7.1 (the
φ(e^{−49π}) example), for polynomial factorization and numerical evaluation.

## Files

- `RamanujanTau/Septic/Dissection.lean` — definitions, the 7-dissection, headline `septic_entry_1_1_i`.
- `RamanujanTau/Septic/ProductForm.lean` — JTP product forms (imports `RamanujanTau.RankTheta`).
- `RamanujanTau/Septic/Page206.lean` — `Page206Evaluation : Prop` (statement only).
- `scripts/audit/septic.lean` — axiom audit.
- `scripts/septic/check_dissection.py`, `scripts/septic/check_page206.py` — numerics.

To compile the audit without `lake build`, the Septic oleans were produced with
`lake env lean FILE -o .lake/build/lib/lean/RamanujanTau/Septic/<F>.olean`. None of these files is imported by
`RamanujanTau.lean`.


**Update:** the page-206 evaluation is now proved (`page206_unconditional`); see docs/SEPTIC_PAGE206.md.


**Update:** `SepticSonCore` is now proved (`SonProof.septicSonCore`); see docs/SEPTIC_SON.md.
