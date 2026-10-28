# Atkin–O'Brien-type congruences for ℓ ∈ {13, 17, 19, 23}: proof via overconvergence

**Theorem.** Let `ℓ ∈ {13, 17, 19, 23}` (the primes `≥ 13` with `dim S_{ℓ−1}(SL₂ℤ) = 1`). There is
`κ_ℓ ∈ ℤ_ℓ^×` such that for all `m ≥ 1` and all `n`:

  `p((ℓ^{m+2}n + 1)/24) ≡ κ_ℓ · p((ℓ^m n + 1)/24)   (mod ℓ^m)`.

Equivalently, `b_ℓ(m) = m` in Boylan–Webb's notation. For ℓ = 13 this is Atkin–O'Brien (1967). For ℓ = 17, 19, 23
it improves Boylan–Webb's `b_ℓ(m) ≤ 2m − 1`. The proof below is complete **modulo the standard
overconvergence inputs (I2) and (I3)**, which are stated precisely and checked numerically, but for which I
have not located exact references. Status: needs expert verification of (I2) and (I3).

## Setup
* `p := ℓ`, `E := E_{p−1}`. Let `B_i ⊂ M_{i(p−1)}(ℤ_p)` be complements of `E·M_{(i−1)(p−1)}`; Miller top
  pieces work, and `B_1 = S_{p−1}`.
* Katz expansion of a weight-0 overconvergent `f`: `f = Σ_i a_i/E^i` with `a_i ∈ B_i ⊗ ℚ_p`. Write `v_i(f)`
  for the valuation of `a_i` in the coordinates of a fixed basis of `B_i`.
* For `0 < v(r) < 1/(p+1)`, `B_E(r) = {f : r^{−i}a_i` integral `}` is a ring.

## External inputs
* **(I1)** [Vonk, LMS J. Comput. Math. 2015, Thm B; Katz 1973; Wan 1998, p ≥ 5]
  `p·U(B_E(r)) ⊆ B_E(r^p)` and `G := E/V(E) ∈ 1 + 𝔪B_E(r)`.
  Consequence **(UB)**: `v_i(U(b/E^j)) ≥ ⌈(pi − j)/(p+1)⌉ − 1` for `b ∈ B_j`. This matches the numerics exactly
  for `i, j ≤ 14` at `p = 17` (`katz.py`).
* **(I2)** `Q := E·η(pz)²/η(z)^{2p} ∈ 1 + 𝔪B_E(r^p)`. `Q` is the ratio of two lifts of the Hasse invariant;
  it is a Γ₀(p)-function, which overconverges to radius `p/(p+1)`. Numerically,
  `v_i(Q) ≥ ⌈pi/(p+1)⌉` (`fq.py`).
* **(I3)** `V` maps `B_E(r^p)` into `B_E(r)` (Frobenius pullback through the canonical subgroup).
* **(I4)** [Boylan–Webb 2013] `b_ℓ(1) = 1`. The stable modules have rank 1, with an `X`-eigenvalue
  `κ ∈ ℤ_ℓ^×` common to both parities. The `L(b)` are cuspidal (`L(b) ∈ qℤ[[q]]`).

## Step 1: the D-bound
* With `s = (p+1)/2`, `δ = (p²−1)/24`, `W = η(p²z)/η(z)^{p²}`, we have `Φ = Δ^δ W`.
* Exact identity (checked): `(E^s W)² = Q^p · V(Q) · G`.
* By (I1)–(I3), `Q^p V(Q) G ∈ 1 + 𝔪B_E(r)`. The binomial coefficients `C(1/2, n)` are p-integral, so
  `E^s W ∈ B_E(r)`. Numerically, `v_i(E^s W) ≥ ⌈i/(p+1)⌉` for `i ≤ 64` (`fw.py`).
* Then `Φ·b/E^j = (Δ^δ/E^s)(E^sW)(b/E^j) ∈ r^{−(j+s)}B_E(r)`, and (I1) gives
  **(DB)** `v_i(D(b/E^j)) ≥ ⌈(pi − j − s)/(p+1)⌉ − 1`. This matches the numerics for `i, j ≤ 12` (`katz.py`).

## Step 2: envelopes
* Define `α(i) = ⌈(pi − 2)/(p+1)⌉` and `β(i) = ⌈(pi − 2 − s)/(p+1)⌉`.
* Define `A_c(γ) = {f cuspidal : v_i(f) ≥ max(0, γ(i) − c) ∀i}`.
* From (UB) and (DB), for `p > 11`:
  1. `U(A_c(β)) ⊆ A_{c−1}(α)` and `D(A_c(α)) ⊆ A_{c−1}(β)` for `c = 2`.
  2. `U(A_1(β)) ⊆ A_1(α)` and `D(A_1(α)) ⊆ A_1(β)`.
  3. `α(i), β(i) ≥ 2` for `i ≥ 2`.
* Proof of (1) and (2): split the minimum over `j` into `j ≤ 2`, where the shift is exact, and `j ≥ 3`, where
  the slack `(p−1)j/(p+1) − c` exceeds the loss. For example, the `U`-step needs
  `(3(p−1) − (p+1)/2)/(p+1) > 2`, i.e. `p > 11`.

## Step 3: induction
1. `L(0) = 1`. By Step 2, `L(b) ∈ A_1(β)` for odd `b` (after `D`) and `L(b) ∈ A_1(α)` for even `b`.
2. Let `e_b = L(b+2) − κL(b)`, so `e_{b+1} = e_b|T_b`. By (I4), `e₁ ≡ 0 (mod p)`. Katz-expansion uniqueness
   mod `p` then gives `e₁/p ∈ A_2`.
3. **Inductively**, `g_b = e_b/p^b ∈ A_2`.
4. By Step 2(1), `g_b|T ∈ A_1`, so mod `p` it reduces to its `B_1 = S_{p−1}` component.
5. **Here `dim S_{p−1} = 1` enters**: that component is `c·\bar L(b+1)`.
6. Hence `L(β+2) ≡ (κ + p^b c) L(β) (mod p^{b+1})` for all `β ≥ b+1`. Comparing with (I4) for large `β`
   gives `c = 0`.
7. So `g_b|T ≡ 0 (mod p)`, and by uniqueness `g_{b+1} = (g_b|T)/p ∈ A_2`.
8. Thus `v(e_b) ≥ b` for all `b`, which is the Theorem. ∎

For ℓ = 29 and 31 everything holds except step 5 (`dim S_{ℓ−1} = 2`), matching Boylan–Webb's sharp `2m − 1`.

## Numerical corroboration (scripts in `scripts/frontier/`)
* `b_ℓ(m) = m`, exact exponent, for:
  * ℓ = 17: m ≤ 4;
  * ℓ = 19, 23: m ≤ 3;
  * ℓ = 13: m ≤ 3, reproducing A–O's `K₂ = 45`.
* (UB) and (DB) match exactly. (W) holds for `i ≤ 64`; (I2) holds within precision.
* The digit pattern `(i+1)(ℓ−1)` of `L(b)` (a corollary of Step 3.1) is observed for ℓ = 17–31.

## Lean status (`RamanujanTau/AtkinOBrien/`, axiom-clean: propext/choice/Quot.sound only)
* `Envelope.lean`. Step 2 for every prime `p ≥ 13` and all Katz indices `i, j`:
  * `U_step`: `α(i) − 1 ≤ max(0, β(j) − c) + u(i,j)` for `c ≤ 2`;
  * `D_step`: the same inequality for `D`;
  * `envelopes_ge_two`.
* `Induction.lean`.
  * `induction`: Step 3 as an abstract theorem over any ring where every element is a unit or a multiple of
    `ϖ`, and any `ϖ`-torsion-free module. Its hypotheses are exactly Steps 2(1)/2(2), the
    `dim S_{ℓ−1} = 1` leading-digit statement, Katz uniqueness, and Boylan–Webb `b(1) = 1` plus stability at
    *some* level. Conclusion: `L(b+2) ≡ κ L(b) (mod ϖ^b)` for all `b ≥ 1`.
  * `eta_identity`: `(E^s W)² = Q^p V(Q) G` in any commutative group with an endomorphism `V`.
* **Not formalized:** (I1)–(I3). These need overconvergent forms, Katz expansions and the canonical
  subgroup, none of which exist in Mathlib. They enter only through the hypotheses of `induction`.
* `Bridge.lean`. `bridge`, `U_maps`, `D_maps`: the coordinate-level form of `hT`.
  * Model: Katz coordinates are `f : ℕ → M` and operator blocks are `T i j`.
  * If (UB) holds, i.e. `T i j` raises ϖ-divisibility by `u(i,j)`, which may be negative, then
    `Σ_j U i j (f j)` lies in the α-envelope whenever `f` lies in the β-envelope.
  * The same holds for D with (DB).
  * This uses only `U_step` and `D_step` together with the ultrametric inequality.

## Assessment of the I2/I3 citation proposal (2026-10-27)
An outside proposal tried to supply I2 and I3 from Katz 1973, Newman 1959 and Ramsey's appendix to
Folsom–Kent–Ono. I checked it against the definitions used here.
* **I3 (V: B_E(r^p) → B_E(r)) is standard.** It is Katz's Frobenius on overconvergent forms (LNM 350,
  §3.10–3.11; the canonical-subgroup theorem gives `v(E_{p−1}(E/C)) = p·v(E_{p−1}(E))` for `v < 1/(p+1)`).
  It is the same input Vonk uses for Theorem B. Downgrade I3 from "open" to "cited". The exact numbering in
  Katz still needs checking against the text.
* **Newman's criterion holds for our actual W.** `W = η(p²z)/η(z)^{p²}` satisfies Σδr_δ = 0,
  Σ(p²/δ)r_δ = 1 − p⁴ ≡ 0 (mod 24), and Πδ^{r_δ} = p². So W is a level-p² form of weight −(p²−1)/2, and
  `E^s W` is a genuine weight-0 function on X₀(p²). The proposal conflated W with Φ = η(p²z)/η(z) = Δ^δ W.
  The conclusion survives.
* **Root extraction.** The binomial series `(1+x)^{1/2}` (or `^{1/12}`, since p ∤ 12) together with
  q-expansion uniqueness already does this. Spectral-norm multiplicativity is not needed.
* **Error in the proposal.** Its Ĝ carries a spurious Δ^{p²−1}. The correct 12th-power form is
  `(E^sW)^{24} = Q̂^p V(Q̂) (E/V E)^{12}` with `Q̂ = Q^{12} = E^{12} V(Δ)/Δ^p`, where all q-powers cancel.
* **I2 is still not supplied.**
  * Katz's integral model is `R[Y]/(E·Y − r^p)`. Its reduction has an ordinary component, where Q ≡ 1 by
    the q-expansion principle, and supersingular components, where Q mod 𝔪 sees `a_i r^{−pi}`.
  * So I2 is *equivalent* to: `Q = E_{p−1}/A_p`, where `A_p = η^{2p}/η(pz)²` is the Γ₀(p)-lift of Hasse,
    has Katz coefficients `v(a_i) > p·i·v(r)`, i.e. Q overconverges integrally to radius `p/(p+1)`.
  * This is a sharp-radius statement. None of the cited results states it. Ramsey's FKO appendix is
    qualitative (half-integral weight, ordinary projector) and gives no radius.
  * Numerically `v_i(Q) ≥ ⌈pi/(p+1)⌉` (`fq.py`), which is consistent.
  * Plausible route: compare `A_p(x)` with the derivative of the dual of the canonical isogeny (Katz 3.10.7).
