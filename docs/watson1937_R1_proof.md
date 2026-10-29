# Watson (1937), proof of (B₀): χ₀(q) = 2F₀(q) − φ₀(−q)

The formal counterpart is `Watson.chi0_R1_watson` in
[Watson/R1.lean](../RamanujanTau/Watson/R1.lean). See the
[mock theta method](../MOCK_THETA_METHOD.md) for the complete proof architecture.

Source: G. N. Watson, "The mock theta functions (2)", Proc. London Math. Soc. (2) 42 (1937), 274–304,
§3, pp. 280–281. The steps below are transcribed and translated into modern notation; this is not a verbatim copy.

Watson's notation `Π_n(x, q) = ∏_{k<n} (1 + x q^k)` is translated throughout, so
`Π_n(−q, q) = (q;q)_n` and `Π_∞(q, q) = (−q;q)_∞`. The expansions used are:
- (E1) `(−x;q)_∞ = Σ q^{k(k−1)/2} x^k / (q)_k`;
- (E2) `1/(x;q)_∞ = Σ x^k / (q)_k`;
- (E4) `(−q;q)_∞ (q;q²)_∞ = 1`.

## Ingredients

- χ₀ has two series forms, (A₀):
  `χ₀ = Σ_n qⁿ (q)_n/(q)_{2n} = 1 + Σ_m q^{2m+1}/(q^{m+1};q)_{m+1}`.
  - Watson proves this by summing a double series two ways with (E3), the finite q-binomial
    `1/(x;q)_m = Σ_n xⁿ (q^m;q)_n/(q)_n`. The double series is
    `Σ_{n≥1} Σ_{m≥0} q^{mn+m+n} (q)_{m+n−1} / ((q)_{n−1} (q)_m)`.
  - Summing over m first gives `Σ_{n≥1} qⁿ/(q^{n+1};q)_n`.
  - Summing over n first gives `Σ_{m≥0} q^{2m+1}/(q^{m+1};q)_{m+1}`.

## Chain of equalities

1. Start from `2χ₀/(q)_∞ = 2 Σ_n qⁿ / ((q)_{2n} (q^{n+1};q)_∞)`.
2. By (E2), `1/(q^{n+1};q)_∞ = Σ_m q^{(n+1)m}/(q)_m`. Swap the sums; the factor 2 together with the
   n-sum is the even part of an Euler sum:
   `= Σ_m qᵐ/(q)_m · Σ_p [x^p + (−x)^p]/(q)_p` with `x² = q^{m+1}`.
   By (E2) again this is `Σ_m qᵐ/(q)_m · [1/(x;q)_∞ + 1/(−x;q)_∞]`.
3. Split by the parity of m.
   - For m = 2n: `x = q^{n+½}`, and `1/(x)_∞ + 1/(−x)_∞ = [(−x)_∞ + (x)_∞]/(q^{2n+1};q²)_∞`.
   - For m = 2n+1: `x = q^{n+1}`, `1/(q^{n+1})_∞ = (q)_n/(q)_∞` and `1/(−q^{n+1})_∞ = (−q)_n/(−q)_∞`.
4. By (E1), `(−x)_∞ + (x)_∞ = Σ_k (1+(−1)^k) q^{k(k−1)/2} x^k/(q)_k`. Keep k = 2p, where
   `q^{p(2p−1)} x^{2p} = q^{2p² + 2np}`. This gives three terms:
   - **T1** `= 2 Σ_{n,p} q^{2p²+2np+2n} / ((q)_{2n} (q^{2n+1};q²)_∞ (q)_{2p})`;
   - **T2** `= (1/(q)_∞) Σ_n q^{2n+1}(q)_n/(q)_{2n+1} = (χ₀ − 1)/(q)_∞`, using the second form in (A₀);
   - **T3** `= (1/(−q)_∞) Σ_n q^{2n+1}/((q;q²)_{n+1}(q)_n)`.
5. Evaluate T1 and T3.
   - **T1**: use `(q)_{2n}(q^{2n+1};q²)_∞ = (q;q²)_∞ (q²;q²)_n` and sum over n by (E2) in base q².
     This gives `T1 = (2/(q;q²)_∞) Σ_p q^{2p²}/((q)_{2p}(q^{2p+2};q²)_∞)`.
     Since `(q)_{2p}(q^{2p+2};q²)_∞ = (q;q²)_p (q²;q²)_∞`, we get **T1 = 2F₀/(q)_∞**.
   - **T3**: write `1/(q;q²)_{n+1} = (q^{2n+3};q²)_∞/(q;q²)_∞`; by (E4) the prefactor becomes 1.
     Expand `(q^{2n+3};q²)_∞` by (E1) in base q² and sum over n by (E2).
     This gives `T3 = Σ_m (−1)^m q^{(m+1)²} / ((q²;q²)_m (q^{2m+2};q)_∞)`
     `= (1/(q)_∞) Σ_m (−1)^m q^{(m+1)²} (q;q²)_{m+1}`, so **T3 = (1 − φ₀(−q))/(q)_∞**.
6. Hence `2χ₀ = 2F₀ + (χ₀ − 1) + (1 − φ₀(−q))`, i.e. **χ₀ = 2F₀ − φ₀(−q)**.

## Notes for formalization

- Every step uses only (E1), (E2), (E4), (E3) for (A₀), parity splitting and Fubini for absolutely
  convergent series. In formal power series, Fubini is just a rearrangement of coefficient-finite sums.
- The half-integer powers `q^{n+½}` can be avoided. Only even powers of x survive, so step 2 can be
  stated as the lemma `(y;q²)_∞ Σ_n yⁿ/(q)_{2n} = Σ_p q^{p(2p−1)} y^p/(q)_{2p}`, the even part of Euler,
  with `y = q^{m+1}` an integer power. Alternatively, work in `t` with `q = t²`.
- χ₁ (B₁) is proved the same way, with odd parts in place of even parts (pp. 281–282).

# The companion formulae (2₀), (3₀), (1₀) (Watson 1937, §3, pp. 283–287)

Notation: `ϑ₄(q) = (q;q)_∞/(−q;q)_∞` (J1), `ψ(q²) = (q⁴;q⁴)_∞/(q²;q⁴)_∞` (J2),
`G(q) = Σ q^{n²}/(q)_n`, `H(q) = Σ q^{n²+n}/(q)_n`, `f₀(q) = Σ q^{n²}/(−q;q)_n`.

## (2₀) and (3₀): `f₀(q) ± ϑ₄(q) G(q)`

1. Since `(q)_n(−q)_n = (q²;q²)_n`, we have
   `f₀ ± ϑ₄G = (q)_∞ Σ_n q^{n²}/(q²;q²)_n · [1/(q^{n+1};q)_∞ ± 1/(−q^{n+1};q)_∞]`.
   By (E2) this is `(q)_∞ Σ_{n,p} (1 ± (−1)^p) q^{n² + p(n+1)}/((q²;q²)_n (q)_p)`.
2. **Upper sign** (p = 2m), proving (2₀):
   - By (E1) in base q², `Σ_n q^{n²+2mn}/(q²;q²)_n = (−q^{2m+1};q²)_∞`.
     This gives `f₀ + ϑ₄G = 2(q)_∞ Σ_m q^{2m}(−q^{2m+1};q²)_∞/(q)_{2m}`.
   - Rearranging products, this is `2(q²;q²)_∞ Σ_m q^{2m}(q^{4m+2};q⁴)_∞/(q²;q²)_m`.
   - Apply (E1) in base q⁴ to `(q^{4m+2};q⁴)_∞`, then sum over m with (E2) in base q².
     The result is `2(q²;q²)_∞ Σ_n (−1)ⁿ q^{2n²}/((q⁴;q⁴)_n (q^{4n+2};q²)_∞)`.
   - Since `(q²;q²)_∞/(q^{4n+2};q²)_∞ = (q²;q²)_{2n}`, this equals
     `2 Σ (−1)ⁿ q^{2n²} (q²;q⁴)_n = 2φ₀(−q²)`. ∎ (2₀)
3. **Lower sign** (p = 2m+1), proving (3₀):
   - By (E1) in base q², `Σ_n q^{n²+(2m+1)n}/(q²;q²)_n = (−q^{2m+2};q²)_∞`.
     This gives `f₀ − ϑ₄G = 2(q)_∞ Σ_m q^{2m+1}(−q^{2m+2};q²)_∞/(q)_{2m+1}`.
   - Rearranging products, this is `2(q⁴;q⁴)_∞ Σ_m q^{2m+1}(q^{2m+3};q²)_∞/(q⁴;q⁴)_m`.
   - Apply (E1) in base q², then sum over m with (E2) in base q⁴. The result is
     `K₋ := 2(q⁴;q⁴)_∞ Σ_n (−1)ⁿ q^{(n+1)²}/((q²;q²)_n (q^{2n+2};q⁴)_∞)`.
   - Split by the parity of n.
     - n = 2m gives `2ψ(q²) Σ q^{(2m+1)²}/(q⁴;q⁴)_m = 2qψ(q²)H(q⁴)`, using `(q²;q²)_{2m} = (q²;q⁴)_m (q⁴;q⁴)_m`.
     - n = 2m+1 gives `−2 Σ q^{(2m+2)²}/(q²;q⁴)_{m+1} = −2(F₀(q²) − 1)`.
   - So **f₀ − ϑ₄G = 2qψ(q²)H(q⁴) − 2(F₀(q²) − 1)**. ∎ (3₀)

## (1₀): `ψ₀(q) = qψ(q²)H(q⁴) + F₀(q²) − 1`, where `ψ₀ = Σ q^{(n+1)(n+2)/2}(−q;q)_n`

1. Write `(−q)_n = (q²;q²)_n/(q)_n`. Then (E2) in base q², followed by (E1) for the n-sum, gives
   `ψ₀ = (q²;q²)_∞ Σ_m q^{2m+1}(−q^{2m+2};q)_∞/(q²;q²)_m`.
2. Rearranging products, this is `(q⁴;q⁴)_∞ Σ_m q^{2m+1}(−q^{2m+3};q²)_∞/(q⁴;q⁴)_m`.
3. (E1) followed by (E2) gives `(q⁴;q⁴)_∞ Σ_n q^{(n+1)²}/((q²;q²)_n (q^{2n+2};q⁴)_∞)`.
   This is the same kernel as K₋ above, without the sign and the factor 2.
4. The same parity split gives **ψ₀ = qψ(q²)H(q⁴) + F₀(q²) − 1**. ∎ (1₀)

## How this closes χ₀ in RamanujanLean

Put (B₀) at q² together with (2₀) and (3₀):
`χ₀(q²) = 2F₀(q²) − φ₀(−q²) = 2 + 2qψ(q²)H(q⁴) − (3/2) f₀(q) + (1/2) ϑ₄(q)G(q)`.

MTC₀ (already proved) gives `f₀ = ϑ₄(q⁵)G(q) − 2(Φ(q²) − 1)`. Substituting, the χ₀ target
`χ₀ − 2 = 3(Φ − 1) − P` (evaluated at q²) becomes the single theta identity

  `4qψ(q²)H(q⁴) + ϑ₄(q)G(q) − 3ϑ₄(q⁵)G(q) + 2P(q²) = 0`.

This is the 4-term identity `2∏₂₀ − 3TG − ∏₁₀ + 2P(q²) = 0` from MTC_GAP_MAP §8, with
`∏₂₀ = ϑ₄G + 2qψ(q²)H(q⁴)` and `∏₁₀ = ϑ₄G`. Its theta side is already certified (T1–T3 certificates).
