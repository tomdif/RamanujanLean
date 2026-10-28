# Atkin–O'Brien-type congruences for ℓ ∈ {13, 17, 19, 23}: proof via overconvergence

**Theorem.** Let `ℓ ∈ {13, 17, 19, 23}` (the primes `≥ 13` with `dim S_{ℓ−1}(SL₂ℤ) = 1`). There is
`κ_ℓ ∈ ℤ_ℓ^×` such that for all `m ≥ 1` and all `n`:

  `p((ℓ^{m+2}n + 1)/24) ≡ κ_ℓ · p((ℓ^m n + 1)/24)   (mod ℓ^m)`.

Equivalently, `b_ℓ(m) = m` in Boylan–Webb's notation. For ℓ = 13 this is Atkin–O'Brien (1967). For ℓ = 17, 19, 23
it improves Boylan–Webb's `b_ℓ(m) ≤ 2m − 1`. **Status (2026-10-27):** (I2) and (I3) are now proved from standard published results: Katz's canonical-subgroup
theorem, Lubin's quotient, Katz expansions, Vonk Thm B, and Boylan–Webb. See "Proof of I2 and I3" below. The
whole argument still needs a check by a p-adic modular-forms expert before any claim is made.

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

## Proof of I2 and I3 (2026-10-27)
Notation: x = (E, ω) is a point of X(1)[ρ] = {v(E_{p−1}(x)) ≤ ρ}, ω is a Néron generator, and v := v(E_{p−1}(x)).
H is the canonical subgroup, π: E → E' = E/H, π̌ its dual, and V f(E, ω) = f(E', π̌^*ω). On the Tate curve
π̌ is étale with π̌^*ω_can = ω_can(q^p), so this V is q ↦ q^p.

**(K) Katz expansions = sup norm.** Katz's integral model of X(1)[ρ] is A[Y]/(E·Y − r). Its special fibre
`Ē·Y = 0` is reduced, because the Hasse invariant has simple zeros. So f is integral on the model iff
|f(x)| ≤ 1 at every point, and f = Σ a_i/E^i is integral iff v(a_i) ≥ i·v(r) (Katz LNM 350, §2.6–2.8).

**I3.** If v(r) < 1/(p+1) and v(E) ≤ v(r), then v(E') = p·v(E) ≤ v(r^p) (Buzzard JAMS 16, Thm 3.3(ii) =
Katz 3.10.7). So |V f(x)| = |f(E', π̌^*ω)| ≤ 1 whenever f ∈ B_E(r^p). By (K), V f ∈ B_E(r). This uses that
f has weight 0, so the choice of differential does not matter.

**I2.**
1. *Newton polygon (proof of Katz 3.10.7).* [p](T) = pT + … + aT^p + … + uT^{p²}, with v(a) = v and
   v(u) = 0. For v < p/(p+1) the p−1 nonzero points of H have valuation (1−v)/(p−1), and the other p²−p
   nonzero points have valuation v/(p²−p).
2. *Derivatives.* Lubin's parameter Y = ∏_{P∈H} T(X ⊕ P) gives a Néron generator ω'_0 on E' with
   π^*ω'_0 = μ·ω and v(μ) = Σ_{P≠0} v(T(P)) = 1 − v. Since π^*π̌^* = p, we get π̌^*ω = λ·ω'_0 with
   **v(λ) = v**.
   *Cross-check.* ker π̌ = E[p]/H. For v < 1/(p+1) it is a *non*-canonical subgroup of E' (v(E') = pv), so
   v(λ) = (p−1)·pv/(p²−p) = v. For v ∈ (1/(p+1), p/(p+1)) it is canonical (v(E') = 1−v), so
   v(λ) = 1 − (1−v) = v. The two regimes agree.
3. *Value of VΔ/Δ^p.* VΔ/Δ^p(x) = Δ(E', λω'_0)/Δ(E, ω)^p = λ^{−12} Δ(E', ω'_0)/Δ(E, ω)^p. Both Δ values are
   units, so v(VΔ/Δ^p (x)) = **−12v**.
4. *Conclusion.* Q^{12} = E^{12}·VΔ/Δ^p, an exact q-series identity. So |Q(x)|^{12} = |p|^{12v − 12v} = 1 on
   all of X(1)[ρ] for every ρ < p/(p+1). A_p is analytic and nonvanishing there via the canonical section, so
   Q = E/A_p is analytic. By (K), v(a_i(Q)) ≥ i·ρ for all ρ < p/(p+1), i.e. v(a_i) ≥ ⌈pi/(p+1)⌉. This matches
   `fq.py` exactly.
5. *Congruence.* Q ≡ 1 (mod p) as a q-series, and mod-p q-expansions are injective on ⊕B̄_i. So a_0 ≡ 1 and
   v(a_i) ≥ 1, and Q ∈ 1 + 𝔪B_E(r^p) for v(r) < 1/(p+1). ∎

Provenance and corrections. The argument is from an outside proposal, which I corrected in three places:
* it had the sign of Step 3 as +12v (from ω' = λ^{−1}ω'_0);
* it wrote Q^{12} = Q̂^{−1};
* it had a spurious Δ^{p²−1} in Ĝ.

Citation status:
* Katz 3.10.7 and Buzzard Thm 3.3 are checked against Buzzard's text.
* Buzzard's 3.3 does not itself state the torsion valuations; those come from the proof of Katz 3.10.7.
* Katz 2.6.2, 3.11.2 and 3.11.3, Katz Appendix 2, and Coleman's 1996 p. 221 are **unchecked**.

## Lean, round 2 (2026-10-27): I2/I3 layers
* `AtkinOBrien/I2.lean`:
  * `Q12_identity`: Q^{12}·Δ^p = E^{12}·VΔ in ℤ⟦q⟧, cleared of denominators.
  * `Ap_cong` / `Q_cong`: A_p ≡ 1 (mod p) by Frobenius, so Q ≡ 1 whenever E ≡ 1.
  * `newton_break`: the slopes separate ⇔ v < p/(p+1).
  * `lie_dual_noncanonical` / `lie_dual_canonical` / `lie_sum`: the cross-check v(Lie π̌) = v in both regimes.
  * `Q_val`: the pointwise cancellation.
  * `sharp_of_all_radii`: an integer n with i·ρ ≤ n for all ρ < p/(p+1) satisfies n ≥ ⌈pi/(p+1)⌉.
  * `I3_radius`: the radius arithmetic behind I3.
* `AtkinOBrien/Newton.lean`: **Newton-polygon theory over any ultrametric normed field**, built from scratch
  because Mathlib has none.
  * `dominant`: if ‖c_m‖ρ^m strictly dominates every other term, then exactly m roots of ∏(X − rᵢ) have
    norm < ρ, none has norm ρ, and ‖c₀‖ = ‖c_m‖·∏_{small}‖rᵢ‖.
  * `two_segment`: Katz's two-slope shape with the break condition ε^{N−m} < α^N. For [p](T)/T it yields
    the p−1 canonical points with product norm |p|^{1−v}.

### Remaining layers for a fully formal I2/I3 (not built; each is a large project)
1. The formal group law of a Weierstrass curve over a ring, its [p]-series, and [p](T) ≡ V(T^p) (mod p) with
   linear coefficient the Hasse invariant. Mathlib has `FormalGroup` but no elliptic one.
2. Hasse invariant ≡ E_{p−1} (mod p) (Deligne/Serre, via the Tate curve and the q-expansion principle).
3. The Lubin quotient formal group by a finite subgroup, with its Néron differential (Step 2 of I2).
4. Katz modular forms as functions of (E, ω) over O_{ℂ_p}: the Tate curve, q-expansions, and V defined via π̌.
5. Katz expansions and the reducedness of the integral model A[Y]/(EY − r) (simple zeros of Hasse/Igusa).
Weierstrass preparation, needed to pass from the [p]-series to a polynomial, is already in Mathlib.

## Lean, round 3 (2026-10-28): formal-group layer (`RamanujanTau/FormalGroupLayer/`)
Built on Mathlib's bare `FormalGroup` structure. Everything is axiom-clean.
* `PDeriv.lean`: partial derivatives `pd` of `MvPowerSeries`, the Leibniz rule (via truncation), `pdDer`
  as a derivation, and `pd_coe` (compatibility with `MvPolynomial.pderiv`).
* `Chain.lean`: **the multivariable chain rule** `pd_subst`:
  ∂ⱼ f(a) = Σₛ (∂ₛf)(a)·∂ⱼaₛ, for substitutions with zero constant terms. It is not in Mathlib.
* `Basic.lean`:
  * `assoc_ev`: associativity along any substitution.
  * `subst_zeros`.
  * **`ev_T_zero`: F(X,0) = X**. f = F(X,0) is idempotent, and Mathlib's compositional inverse then
    forces f = X.
* `Invariant.lean`:
  * `ev_zero_right`.
  * **`invariance`**: Ψ(F(a,b)) = (∂₂F)(a,b)·Ψ(b), with Ψ(u) = (∂₂F)(u,0).
  * The [n]-series `nmul`.
  * **`nmul_invariant`: Ψ(T)·[n]′(T) = n·Ψ([n]T)**, i.e. [n]^*ω = nω, for commutative F.
* `CharP.lean`:
  * `pd_nmul_eq_zero`: [p]′ = 0 in characteristic p.
  * `coeff_nmul_eq_zero`: [p] has only T^{pk} terms there.
  * `nmul_map`.
  * **`p_dvd_coeff_nmul`**: over *any* commutative ring, p divides the coefficient of T^k in [p](T)
    whenever p ∤ k.
  This is the shape [p](T) = pT + ⋯ + aT^p + ⋯ that Katz's Newton-polygon argument (`Newton.two_segment`)
  consumes.

Still open for I2:
* the height-2 refinement: mod (p, a), [p] is a series in T^{p²} with unit leading term;
* the elliptic formal group itself, with Hasse = E_{p−1} mod p;
* Lubin's quotient;
* Katz forms and his integral model.
* `Endo.lean`:
  * `nm_ev`: [n] is an endomorphism.
  * **`hom_invariant`**: for a homomorphism f: G₁ → G₂, f′(T)·Ψ_{G₁}(T) = Ψ_{G₂}(f(T))·f′(0).
* `HeightTwo.lean`:
  * In characteristic p, `nmul_eq_expand` gives [p] = g(T^p).
  * **`gV_hom`**: g is a homomorphism F^{(p)} → F, via F(X,Y)^p = F^{(p)}(X^p,Y^p) and injectivity of
    `expand`.
  * **`coeff_nmul_eq_zero_of_aH`**: if a = 0 then [p] ∈ R⟦T^{p²}⟧.
  * **`mem_ideal_coeff_nmul`** (mixed characteristic): over any commutative ring, the coefficient of T^m in
    [p](T) lies in the ideal (p, a) whenever p² ∤ m.
  Together with `p_dvd_coeff_nmul`, these are exactly the coefficient bounds that `Newton.two_segment`
  needs below the T^{p²} term.
* `AtkinOBrien/Canonical.lean`:
  * **`dominance_transfer`**: a strictly dominant term passes from h = P·U to P when U is a Gauss-norm-1
    unit. This replaces Gauss-norm multiplicativity.
  * `FGL.coeff_one_nmul`: [n] = nT + O(T²).
  * `exists_rho`.
  * **`canonical_subgroup`**: the Newton half of Katz 3.10.7 / Lubin, for *any* commutative formal group F
    over R → K, where K is an ultrametric normed field and the coefficients have norm ≤ 1. Assume:
    * height ≤ 2, i.e. ‖coeff_{p²}[p]‖ = 1;
    * the break ‖p‖^p < ‖a‖^{p+1}, i.e. v(a) < p/(p+1);
    * the Weierstrass factorization [p](T)/T = ∏(X − rᵢ)·U.

    Then exactly p−1 roots are small, and ‖a‖·∏_{small}‖rᵢ‖ = ‖p‖, i.e. the total valuation of the
    nonzero canonical points is 1 − v.

    Every input about [p] is proved here (`p_dvd_coeff_nmul`, `mem_ideal_coeff_nmul`, `coeff_one_nmul`).
    The only hypothesis is the Weierstrass factorization with splitting. Mathlib has the factorization over
    complete local rings; splitting holds over a finite extension.

Remaining for a fully formal I2:
1. Lubin's quotient formal group G = F/H, with π(X) = ∏_{h∈H} F(X,h), and its dual π̌.
   * Given these, π′(0) = ∏_{h≠0} h (immediate), and `hom_invariant` gives π^*ω_G = π′(0)·ω_F.
   * π̌∘π = [p] then gives v(Lie π̌) = v.
   * The existence of G and π̌ (Lubin 1967) is the substantial part.
2. The elliptic formal group, and Hasse ≡ E_{p−1} (mod p).
3. Katz forms (E, ω): V via π̌, the Tate curve q-expansion, and Katz's integral model.

## Lean, round 4 (2026-10-28): Tate curve (`RamanujanTau/TateCurve/`, axiom-clean)
* **`Δ_Tate`: Δ(Tate) = q∏(1−qⁿ)²⁴**.
* c₄ = E₄ and c₆ = −E₆.
* The division of a₆ by 12 is integral.
* **von Staudt–Clausen at p** (`VonStaudt.lean`, not in Mathlib): p·B_{p−1} ≡ −1 (mod p).
* **E_{p−1} ≡ 1 (mod p)**: `map_toZMod_EhasseZp`, with E_{p−1} lifted to ℤ_p⟦q⟧.
* Tate(q) ↦ Tate(q^p) under `expand`, with Δ compatible.
* Frobenius on 𝔽_p⟦q⟧.
* Tate over ℤ((q)) is elliptic.

## Lean, round 5 (2026-10-28): modular forms mod p (`RamanujanTau/ModP/`, axiom-clean)
* `Formal.lean`:
  * the single-weight q-expansion principle for polynomials in E₄, E₆ (given that 1728 is a unit);
  * `descend`.
* `Structure.lean`:
  * every level-1 form is an isobaric polynomial in E₄, E₆, in q-expansion form (via Mathlib's
    `discriminantEquiv`);
  * qExpansion(E_k) = Eis k.
* `SwinnertonDyer.lean` (p ≥ 5):
  * the Hasse polynomial A with A(E₄,E₆) = E_{p−1} over ℤ_p;
  * Ā(Ē₄,Ē₆) = 1, and Ā is unique;
  * injectivity mod p in a single weight;
  * filtration: P′ = Ā^m P;
  * Swinnerton-Dyer's kernel theorem within one weight class;
  * **`katz_independent`**: mod-p independence of the Katz pieces, which is the input `hdiv`/`hlead` need.

Not done:
* separation across different weight classes, which needs θ and Ramanujan's identities;
  the downstream proof only uses weights i(p−1), so this is not needed;
* the bridge from actual ℤ_p-forms to polynomials.

## Lean, round 6 (2026-10-28): Lubin's quotient (`RamanujanTau/LubinQuotient/`, axiom-clean, ~1600 lines)
Setting: O is a complete, Hausdorff, linearly topologized domain; F is a commutative formal group over O;
H ⊂ O is a finite subgroup of topologically nilpotent points.
* π(X) = ∏_{h∈H} F(X,h) has a Weierstrass factorization `pis_factor`.
* Lubin's invariance lemma: `descent`, `inj`. A translation-invariant series is a series in π.
* **The quotient formal group** `quot S` (commutative): π is a homomorphism (`pis_hom`), and it is
  unique (`quot_unique`).
* **The dual** `exists_dual`: if H ⊂ F[p], there is a unique π̌ with π̌∘π = [p], and π̌ is a homomorphism
  (`dual_hom`).
* `LieBridge.lie_dual_lubin`: feeds `Lie.lie_dual` directly. Given the canonical-subgroup norm relation,
  ‖Lie π̌‖ = ‖a‖.

Remaining links for I2 Step 2:
* identify H with the small roots of `Canonical.canonical_subgroup`, i.e. show the small roots form a
  subgroup lying in O;
* install the topology instances for a complete DVR.

## Lean, round 7 (2026-10-28): the formal group of a Weierstrass curve (`RamanujanTau/EllipticFormal/`, axiom-clean, ~1540 lines)
* w(z): fixed point, uniqueness, and the coefficients z³ + a₁z⁴ + (a₁²+a₂)z⁵ + ⋯, all over any commutative ring.
* The chord law F_W. Associativity and commutativity come from Mathlib's group law on W(Frac R⟦σ⟧),
  first over the universal curve over ℤ[A₁,…,A₆], then specialized.
  * **`formalGroup W : FormalGroup R`** for every commutative ring R.
  * It is commutative, and compatible with base change (`formalGroup_map`).
* **The invariant differential** `Ψ_formalGroup`: ω = dz/(1 − a₁z − a₂z² − 2a₃w − 2a₄zw − 3a₆w²),
  equivalently Silverman's dx/(2y + a₁x + a₃).
* Scaling: F_{u•W}(uz₁, uz₂) = u·F_W(z₁, z₂). Δ scales by u⁻¹² (Mathlib).

## Lean, round 8 (2026-10-28): Step 2 of I2 end to end (`RamanujanTau/CanonicalIsogeny/`, axiom-clean)
* **`exists_dual_isogeny_lie_integers`**. Setting: F is a commutative formal group over the integer ring of
  a complete ultrametric field K. Assume:
  * height ≤ 2;
  * the break condition v(a) < p/(p+1);
  * a Weierstrass factorization of [p](T)/T, with roots in the integer ring.

  Conclusion: there are a formal group G and homomorphisms π: F → G, π̌: G → F with π̌∘π = [p] and
  ‖Lie π̌‖ = ‖a‖.
* H is built from the small roots (`root_iff`, `injOn_roots`). Simplicity of the roots is *proved*: a double
  root would make [p]′ vanish there, contradicting `nmul_invariant`.
* Inverses come from [p−1].
* The topology instances on the integer ring are supplied.

## Lean, round 9 (2026-10-28): Vélu's formulas (`RamanujanTau/Velu/`, axiom-clean, ~1350 lines)
Setting: the short form y² = x³ + Ax + B over a field with 2 ≠ 0, and a finite subgroup G of odd order.
* `exists_kernel`: Vélu's data exist for every such subgroup.
* E′: y² = x³ + (A−5t)x + (B−7w).
* **`velu_equation_point`**: P ∉ G maps onto E′. The proof is purely algebraic: no poles at kernel points
  via Taylor jets, plus valuation at infinity.
* **`invariant_differential`**: dX/(2Y) = dx/(2y).
* `curve_Δ`.
* G-invariance, and X(P) = Σ_{V∈G} x(P+V) − Σ x(V).

Not done:
* the homomorphism E → E′ with kernel G;
* Δ′ ≠ 0;
* the general a₁…a₆ form.

## Lean, round 10 (2026-10-28): Weierstrass supply (`RamanujanTau/WeierstrassSupply/`, axiom-clean)
* The integer ring of a complete ultrametric field is (π)-adically complete for any 0 < ‖π‖ < 1. This
  includes ℂ_p.
* `exists_prep`: Weierstrass preparation over that integer ring.
* `exists_split`: over an algebraically closed field, the Weierstrass polynomial splits with integral roots.
* **`exists_dual_isogeny_lie_integers_algClosed`**. Setting: K complete and algebraically closed; F a
  commutative formal group over its integer ring. The hypotheses are only:
  * height 2 (‖coeff_{p²}[p]‖ = 1 and ‖a‖ < 1);
  * the break condition.

  Conclusion: π, π̌ with π̌∘π = [p] and ‖Lie π̌‖ = ‖a‖. **Step 2 of I2 is formal with no structural
  hypotheses.** The ordinary case ‖a‖ = 1 is separate and trivial.

## Lean, round 11 (2026-10-28): step (K), Katz series vs. sup norm (`RamanujanTau/KatzForms/`, axiom-clean)
* **`katz_iff`** (abstract) and **`katz_iff_weierstrass`** (concrete: test objects are good-reduction
  Weierstrass curves over an algebraically closed complete K). Statement: gnorm(bᵢ) ≤ ‖r‖^i for all i
  ⟺ ‖f(W)‖ ≤ 1 on {‖E(W)‖ ≥ ‖r‖}, for 0 < ‖r‖ < 1.
  * ⇒ is unconditional.
  * ⇐ uses a dominance argument at ‖E‖ slightly above ‖r‖, plus a lifting lemma (`exists_lift`: Hensel
    via `Newton.dominant`).
  * Remaining hypothesis `SSDetect`: every element of B_i ⊗ K attains its Gauss norm at a supersingular
    good-reduction point. Discharging it needs three things:
    * existence of supersingular points;
    * Igusa's theorem that Ā has simple zeros;
    * a saturated basis of the pieces B_i.

## Lean, round 12 (2026-10-28): Hasse invariant (`RamanujanTau/HasseInv/`, axiom-clean)
* `coeff_nmul_sub_omega_mem_W`: for every Weierstrass curve over every ring, a ≡ coeff_{p−1} ω (mod p).
  The proof goes through [p]^*ω = pω and the universal ring.
* **`aH_formalGroup_eq_hasseH`**: in characteristic p, a equals the classical Hasse invariant, i.e. the
  coefficient of x^{p−1} in f(x)^{(p−1)/2}. The proof is a coefficientwise Cartier argument.
* `hassePoly`: an explicit isobaric weight-(p−1) polynomial with aH(formalGroup W) = hassePoly(c₄, −c₆).
* `hassePoly_eq_hasseBar_iff`: it equals Swinnerton-Dyer's Ā iff hasseH(Tate mod p) = 1.
* `coeff_nmul_sub_hasseA_mem`: **a ≡ E_{p−1}(E, ω) (mod p)**, *conditional on* hT : hasseH(Tate mod p) = 1.
  This is Deligne's congruence.
  * hT is still open; it is the only `sorry`, kept in an untracked WIP file.
  * Route: Tate's uniformization gives 𝔾̂ₘ ≅ formal group of Tate, and aH(𝔾̂ₘ) = 1.

## Lean, round 13 (2026-10-29): Buzzard 3.3 for formal groups (`RamanujanTau/QuotientHasse/`, axiom-clean)
Setting: F is a commutative formal group over the integers of an algebraically closed complete K, of
height 2 and satisfying the break condition. C ranges over order-p subgroups.
* **`hasse_quot_noncanonical`** (v): if C ≠ H, then F/C has height 2, ‖a_{F/C}‖^p = ‖a_F‖ (v/p), it
  satisfies the break condition, and π(F[p]) lies in {0} ∪ Can(F/C).
* **`hasse_quot_canonical`** (ii)/(iv): if C = H, then:
  * v < 1/(p+1) ⇒ ‖a_{F/H}‖ = ‖a‖^p (p·v); **this is the formal-group content of I3**;
  * 1/(p+1) < v ⇒ ‖a_{F/H}‖·‖a‖ = ‖p‖ (1 − v).
* `quot_height`: F/C has height 2. The proof compares Weierstrass degrees.
* `torsion_classify`: root norms of [p], via the converse of Newton.
* `norm_pt_pis`.

Hypotheses as stated:
* C ≠ H appears as "C has no nonzero canonical point".
* The canonical subgroup of the quotient is proved only as an inclusion.

## Lean, round 14 (2026-10-29): Igusa and `SSDetect` (`RamanujanTau/Igusa/`, axiom-clean)
* Route: the Serre derivation (Swinnerton-Dyer). It gives ∂Ā = B̄ and ∂B̄ = −X₀Ā, and these force simple roots.
* `roots_nodup` / `igusa_chartT` / `igusa_chartS`: **Ā has simple zeros (Igusa)**, and Ā does not vanish at
  the cusp.
* `exists_ss`: supersingular points exist.
* `exists_ss_nonvanishing`.
* An explicit monomial complement Bz, with `katz_independent_S`.
* **`katz_iff_hasse`**: step (K) with SSDetect discharged.
* All of this is conditional on `RamanujanODE`, Ramanujan's three q-series ODEs over ℤ. RamanujanODE is a
  true classical theorem, stated as an explicit Prop hypothesis. It is the remaining input.

## Lean, round 15 (2026-10-29): Ramanujan's ODEs (`RamanujanTau/RamanujanODE/`, axiom-clean)
* **`RamanujanODEProof.ramanujanODE`** proves all three, over ℤ⟦q⟧:
  * 3θE₄ = E₂E₄ − E₆;
  * 2θE₆ = E₂E₆ − E₄²;
  * 12θE₂ = E₂² − E₄.
* The route:
  * the Serre derivative is slash-equivariant, and ∂₁E₂ has weight 4. This part is adapted from
    Sphere-Packing-Lean, Apache 2.0, with attribution in the file;
  * q-series term-by-term differentiation (`QSeries.lean`, new);
  * the dimension-1 argument below weight 12, via `CuspForm.rank_eq_zero_of_weight_lt_twelve`;
  * descent from ℂ to ℤ.
* This fills Mathlib's TODO in `ModularForms/Derivative.lean`.
* `Igusa/Unconditional.lean`: Igusa's theorem, supersingular points, and **step (K)** (`katz_iff_hasse'`)
  now hold **without any extra hypothesis**.

## Lean, round 16 (2026-10-29): height 2 for elliptic curves (`RamanujanTau/HeightEll/`, axiom-clean)
* **`topc_norm_eq_one`**: let W be a good-reduction curve over the integers of an ultrametric field, with
  residue characteristic p ≥ 5 and ‖a‖ < 1. Then the T^{p²} coefficient of [p] is a unit, i.e. the formal
  group has height exactly 2.
* `coeff_p2_ne_zero_field`: the characteristic-p statement over any field.
* Route: degree bounds via Kummer-line recursions for x(n•P), with ht Xₙ ≤ n² (Gauss lemma). The formal
  group connects through `nsmul_P`: n•P(T) = P([n]T). Then:
  * `[p] ≠ 0` uses a 2-torsion point;
  * if a = b = 0, then [p] ∈ k⟦T^{p³}⟧, which contradicts p³ ≤ 2(p+1)² + 6.
* No division polynomials were needed.

## Lean, round 17 (2026-10-29): Deligne's congruence (`RamanujanTau/TateFormal/`, axiom-clean, ~1470 lines)
* **`TateFormal.hasseH_TateBar`**: the Tate curve over 𝔽_p⟦q⟧ has Hasse invariant 1, for p ≥ 5.
* The route:
  * Tate's uniformization as a formal identity over ℤ[u,u⁻¹]⟦q⟧ (`EA_eq_zero`). It is obtained from
    Mathlib's ℘′² = 4℘³ − g₂℘ − g₃ via q-expansions and two identity principles;
  * substitute u = 1+T, which gives (1+T)dx/dT = 2y + x;
  * then ω = dT/(1+T), and a Cartier lemma gives H = 1.
* `HasseInv/Unconditional.lean`: **a ≡ E_{p−1}(E, ω) (mod p) unconditionally** (`coeff_nmul_sub_hasseA_mem'`).
  It also gives hassePoly = Ā (Deligne).
* The WIP file with the last sorry is deleted.

## Lean, round 18 (2026-10-29): Boylan–Webb inputs (`RamanujanTau/BoylanWebb/`, axiom-clean, ~2.2k lines)
* L_ℓ(b) are defined exactly as in Boylan–Webb. `L_eq_partition` links them to p(n), and `L_cuspidal` gives
  cuspidality.
* **`two_step_mod_ell`**: L(b+2) ≡ κ L(b) (mod ℓ) for **all** b ≥ 1. The constants are κ = 6, 6, 10, 5 for
  ℓ = 13, 17, 19, 23. `partition_count_ℓ` gives the corresponding congruence for partition numbers.
* `hnz_ℓ`: L(b) ≢ 0 (mod ℓ). `CertX.rank_one`: L(b) mod ℓ lies on the line spanned by the weight-(ℓ−1) cusp
  form. Both are proved by kernel certificates (`decide +kernel`) plus the Sturm bound (`sturm`, new).
* **`induction_seq` / `induction_padic`**: a variant of Step 3 that **no longer needs Boylan–Webb stability
  (hstab) or hnz**. The leading-digit correction is absorbed into the constant, K_{j+1} = K_j + ϖ^{j+1}d. The
  same correction works for all β ≥ j+1, because L(β+1) = T L(β) propagates it. The ℓ-adic limit κ_lim then
  works at every level.
* Remaining inputs to `induction_padic`:
  * hT, hdiv, hL: Steps 1–2 plus Katz uniqueness, on an actual module M of overconvergent forms;
  * hlead: the S_{ℓ−1}-leading digit.

## Lean, round 19 (2026-10-29): I2 for elliptic curves (`RamanujanTau/EllipticI2/`, axiom-clean)
* **`elliptic_step2` / `elliptic_step2_E`**: for a good-reduction W over the integers of an algebraically
  closed complete K with ‖p‖ > 0 and 0 < v(E_{p−1}(W)) < p/(p+1), there are π, π̌ with π̌∘π = [p] and
  ‖Lie π̌‖ = ‖E_{p−1}(W)‖. **This is Step 2 of I2 for curves, unconditional.**
  * Supporting lemma: `norm_hasse_eq_norm_Ep_of_break`.
* **`step3_of_link`**: given a `VeluLubinLink`, the pointwise statement v(Q(x)) = 0 follows, i.e.
  ‖E‖¹²·‖Δ(E′, π̌^*ω)‖/‖Δ‖^p = 1. A `VeluLubinLink` consists of:
  * a good-reduction curve W′;
  * an isomorphism-like hom formalGroup(W′) → G with unit Lie derivative.
* `Log.hom_of_invariant`: in characteristic 0, matching invariant differentials force a homomorphism. This
  is the converse of `hom_invariant`, built via the formal logarithm.
* Remaining (untracked WIP): construct the link.
  * Formal Vélu series and the chain rule.
  * Points of H in E(K).
  * Translation invariance, then `Lubin.quot_unique`.
  * Integrality and good reduction of E/H.

## Lean, round 20 (2026-10-29): I1, the U_p contraction (`RamanujanTau/UpContraction/`, axiom-clean)
* **`thmB`** (Vonk Thm B) and **`UB`**: the coefficient bound v(a_{ij}) ≥ ⌈(pi−j)/(p+1)⌉−1, via step (K). The
  hypotheses are:
  * `QuotHyp`: Buzzard 3.3(v) on curves;
  * `hU`: p·Uf(W) = Σ_{C≠H} f(W/C) on the break region. This is the q-expansion principle for U_p, and it
    is **the main remaining gap**;
  * existence and decay of U f's Katz expansion.
* `hasse_transport`: for a hom f with u = f′(0), u·a_F − u^p·a_G ∈ (p).
* `quot_E_pow`: ‖E(W′)‖^p = ‖E(W)‖ for non-canonical quotient curves, given a quotient model.
* `quotHyp_of_models`: `QuotHyp` reduces to the existence of quotient models (`SSData`, `hord`).
* `TateU.sum_rescale_Up`: the Tate-curve root-of-unity identity Σ_k F(ζ^k t) ↔ p·U_p F.

Remaining for I1:
* `hU`, the q-expansion principle for U_p on all test curves. This needs Katz moduli or rigid input.
* `SSData`, which needs the following:
  * F[p] ≅ (ℤ/p)²;
  * the count of p+1 subgroups;
  * Vélu–Lubin quotient models for non-canonical C (same link as I2).
* `hord`: étale quotients of an ordinary curve are ordinary.

## Lean, round 21 (2026-10-29): THE FINAL THEOREM, modulo (UB) and (DB) (`RamanujanTau/AtkinOBrienFinal/`, axiom-clean)
* **`atkin_obrien_13/17/19/23 (hUB : UB ℓ) (hDB : DB ℓ)`**: there is κ ∈ ℤ_ℓ, with κ ≡ 6, 6, 10, 5 (mod ℓ),
  such that for all m ≥ 1 and n with 24 ∣ ℓ^m n + 1,
  ℓ^m ∣ #Partitions((ℓ^{m+2}n+1)/24) − κ·#Partitions((ℓ^m n+1)/24).
* The hypotheses are exactly the column matrix bounds:
  * UB: for b ∈ B_j, U(b/E^j) has an integral Katz expansion with v_i ≥ u(i,j);
  * DB: the same for U(Φ·b/E^j), with v_i ≥ d(i,j).

  Here E = E_{ℓ−1} (`EhasseZp`), and the B_i are the monomial complement `Igusa.S`. This is a genuine
  complement, because A has a unit leading monomial. The bounds do not depend on the choice of complement.
* Assembly:
  * `Katz.lean`: Katz series in ℤ_ℓ⟦q⟧, envelopes, and Katz uniqueness mod ℓ.
  * `Transfer.lean`: hT from UB/DB plus `U_step`/`D_step`.
  * `Lead.lean`: hlead via Sturm.
  * `Main.lean`: `BoylanWebb.induction_padic`, then translation to partition numbers.

Remaining to make it unconditional:
* UB: `UpContraction.thmB`/`UB_of_models`, conditional on:
  * hU, the q-expansion principle for U_p;
  * quotient models for non-canonical C;
  * matching UpContraction's formulation to `AtkinOBrienFinal.UB`.
* DB: Step 1 (E^sW ∈ B_E(r) from I2 + I3) plus UB. This still needs I2's Vélu–Lubin link and a Lean derivation
  of DB from UB.

## Lean, round 22 (2026-10-29): Hecke operators on q-expansions (`RamanujanTau/HeckeQExp/`, axiom-clean)
* `Tq`, `sigma_hecke`, `Tq_Eis`; `tate_geom_sum` gives the Tate-curve sum over all p+1 subgroups.
* **`heckePoly`**: T_p on isobaric polynomials (classical level-1 forms), with `ev_heckePoly` and
  `heckePoly_unique`.
* `classical_hU` / `hU_classical`: Σ_{C≠H} P(W/C) = p·(T_pP)(W) − P(W/H) on all test curves, for classical P.
  It assumes two hypotheses:
  * **hAlg**: algebraicity of the subgroup sum;
  * **hT**: the Vélu quotients of Tate(q) are the explicit Tate(q^p) and Tate(ζ^j t).

Remaining for hU:
* hAlg, via symmetric functions of the kernel polynomials;
* hT, via the Tate parametrisation of quotients;
* the overconvergent limit, Σ_{C≠H} for Katz series.

## Lean, round 23 (2026-10-29): DB from UB (`RamanujanTau/DBound/`, axiom-clean)
* **`DB_of_UB (hUB) (hW)`**, where HW is the statement E^sW ∈ B_E(r) (v_i ≥ ⌈i/(ℓ+1)⌉).
* **`HW_of (hQ) (hV) (hG)`**: proved through the η-identity in ℤ_ℓ⟦q⟧, a Hensel square root (`sqrt_Ap`),
  and the ring structure of B_E(r) (`Ap_mul`).
* Supporting: `decompN` (Katz decomposition mod ℓ^N), `isKatz_of_Ap` and `katz_unique_N`.
* **`atkin_obrien_13'/17'/19'/23' (hUB) (hQ) (hV) (hG)`**: the final theorem, now hypothesised on four
  explicit Props.
  * UB: the U column bounds (I1-U).
  * HQ: v_i(Q) ≥ ⌈ℓi/(ℓ+1)⌉ (I2).
  * HV: V maps B_E(r^ℓ) into B_E(r) (I3).
  * HG: E/V(E) ∈ B_E(r) (I1-G).
* All four are geometric, i.e. pointwise on test curves combined with step (K).

## Lean, round 24 (2026-10-29): Vélu–Lubin link (`RamanujanTau/VeluLubin/`, axiom-clean, ~2000 lines)
* Formal Vélu series φ = −X/Y, with **φ^*ω′ = ω** (`phi_invariant`) and `velu_formal_hom`:
  φ is a formal-group homomorphism.
* `Pt_hom`: formal points map into E(K) homomorphically. `exists_kernel_of_finSub` gives the canonical
  subgroup as a Vélu kernel.
* Good reduction from the formal group (`norm_Δ_eq_one_of_iso`): a unit-Lie homomorphism from a height-2
  formal group forces ‖Δ‖ = 1. The proof uses Hasse invariants of the cusp/node.
* **`link_of_descent`**, and **`exists_step2_with_velu`** for short curves.
* The only remaining hypothesis is **integral descent (I1)**: ∃ θ ∈ 𝒪⟦T⟧ with θ∘π = μ·φ_κ.
  * Route: translation invariance of φ under H via Vélu `X_add_mem` over Frac K⟦z⟧, then `Lubin.descent`.
* Also remaining: reduction from a general Weierstrass W to short form.

## Lean, round 25 (2026-10-29): subgroup-sum algebraicity (`RamanujanTau/SubgroupSum/`, axiom-clean)
* The intrinsic Vélu coefficients depend only on G (`Kernel.curve_eq_veluC`).
* `subSum`: a sum over the order-n subgroups.
* Galois descent (`subSum_mem_range`, including for the algebraic closure) gives rationality.
* `universal_subSum_mem`: the universal sum lies in ℚ[A,B], given integrality of torsion x-coordinates.
* `subSum_ptR_scale` gives scaling; `exists_iso_of_poly` gives isobaricity.
* `sum_kernels_eq_subSum` is the hAlg shape.
* Remaining (untracked WIP):
  * R1: x-coordinates of torsion points are integral, via the division-polynomial link nP = 0 ⟹ ψ_n(x) = 0.
  * R2: specialization from the universal curve to every nonsingular curve. This needs the generic E[p] to
    have p² points, plus a ring map from the integral closure.

## Lean, round 26 (2026-10-29): Vélu quotients of the Tate curve (`RamanujanTau/TateQuot/`, axiom-clean, ~2300 lines)
* **`ptR_veluQuot`**: for every one of the p+1 kernels, Vélu's formulas applied to the explicit Tate kernel
  points give the ptR (c₄, −c₆) of `tateQuot`: Tate(q^p) scaled by 1/p, and Tate(ζ^j t).
* μ_p (`velu_mu_A`/`B`): Vélu's A′, B′ give p⁴E₄(q^p) and p⁶E₆(q^p). The root-of-unity constants are
  −(p²−1)/12 etc.
* The ⟨s⟩ kernels (`velu_sub_A`/`B`) give E₄, E₆, via Eulerian-polynomial and divisor-counting identities.
* `zB2_eq`, `zB4_eq`: θ-derivative identities for Tate's x(u).
* `hT_iff_velu`: hT ⟺ the hAlg identity over K⟦t⟧ at the short Tate model.

Remaining:
* the kernel points form subgroups under the group law (Tate addition theorem);
* hAlg over the ring K⟦t⟧, which is the specialization R2 from the universal curve.

## Lean, round 27 (2026-10-29): V-layer via modular equations (`RamanujanTau/VLayer/`, axiom-clean)
* `modular_equation_E` / `modular_equation`: the level-ℓ modular equation of E (or of any isobaric P) has
  classical coefficients over ℤ_ℓ. The proof:
  * the conjugates live in `PadicAlgCl ℓ⟦t⟧`;
  * their power sums are ℓ·T_ℓ;
  * Newton's identities;
  * norms in PadicAlgCl, then `descend`.
* **`HG_holds`**: E/V(E) ∈ B_E(r) unconditionally, for all ℓ ≥ 5. The proof applies an ℓ-adic Hensel
  contraction in Katz coordinates (`hensel_fix`) to the modular equation.
* **`Q_InB1`** (ℓ ≥ 11): Q ∈ B_E(r), via the modular equation of Δ, Q¹² = E¹²VΔ/Δ^ℓ, and a Hensel 12th root.
* **`atkin_obrien_13''/17''/19''/23'' (hUB) (hVQ)`**: the final theorem now rests on two hypotheses:
  * UB, the U-column bounds;
  * HVQ: V(Q) ∈ B_E(r).

  HVQ is the one genuinely level-ℓ² statement left.

## Lean, round 28 (2026-10-29): torsion integrality and specialization (`RamanujanTau/TorsionSpec/`, axiom-clean, ~2100 lines)
* **`R1`**: x-coordinates of torsion points are integral. The proof is by valuations plus a Kummer recursion
  in residue characteristic 0; no division polynomials.
* **`fullTorsion`**: E[n] has exactly n² points over an algebraically closed field of characteristic 0.
  This uses the HeightEll degree recursion and a Wronskian separability argument.
* **`R2'`**: the universal subgroup sum specializes to every nonsingular curve. It uses lying-over,
  `IsAlgClosed.lift`, and injective, additive specialization of torsion.
* **`R2_field` / `exists_poly_field`**: the same over any characteristic-0 field via F̄, including
  K((t)) and FractionRing K⟦t⟧.
* So **hAlg holds** (for short curves). The bridge to `TateQuot.hT_iff_velu` / `HeckeQExp.classical_hU` is
  still to be written.
