# Ramanujan's forty identities for the Rogers–Ramanujan functions

Source of the statements: B. C. Berndt, G. Choi, Y.-S. Choi, H. Hahn, B. P. Yeap, A. J. Yee, H. Yesilyurt, J. Yi,
*Ramanujan's forty identities for the Rogers–Ramanujan functions*, Mem. AMS 188 (2007), no. 880, §3 (35 entries,
40 identities). The main proof method used here is from Z. Cao, *Quadratic forms, exact covering systems, and product
identities for theta functions*, arXiv:2503.11445 (Types I/II).

Lean: `RamanujanTau/Forty/`. Audit: `scripts/audit/forty2.lean` (all proved entries; `forty.lean` is the round-1 audit). Numerics: `scripts/forty/verify_forty.py` checks all 40
identities to order 200, with G and H computed from their **sum** sides. Generators: `scripts/forty/ecs.py` searches
for exact covers; `scripts/forty/gen.py` emits the ECS definitions and the theta and product theorems.

## Conventions in Lean

* `G = Σ q^{n²}/(q;q)_n`, `H = Σ q^{n²+n}/(q;q)_n` (`Forty.G`, `Forty.H`; sum sides, in `ℤ⟦q⟧`). The product forms
  `G_eq`, `H_eq` are the repo's Rogers–Ramanujan identities.
* `S a f = f(q^a)`; `Ng f = f(−q)`; `fm a = f(−q^a) = (q^a;q^a)_∞`; `chim a = χ(−q^a) = (q^a;q^{2a})_∞`;
  `chip a = χ(q^a) = (−q^a;q^{2a})_∞`, defined as `S a (Ng (q;q²)_∞)`.
* `φ` is `RamanujanTau.Septic.phi = Σ_{n∈ℤ} q^{n²}` (sum definition).
* Division `a/b` is written `a * Ring.inverse b`; every denominator is a unit with constant term 1.

## The method

1. **Engine** (`Lattice.lean`). `ECS` is an integer matrix `B` with `det B ≠ 0` and shift set `I`, such that
   `ℤ² = ⨆_{i∈I} (Bℤ² + i r)` is an exact cover. Cover and uniqueness are proved by `omega` from explicit coset
   formulas.
   * `hs_split` / `split_two`: summing a family over `ℤ²` coset by coset.
   * `θθ_lattice` (Cao Thm 3.1): `θ_{N₁}(e₁,w₁) θ_{N₂}(e₂,w₂) = Σ_{i∈I} t^{…} θ_{M₁}(…) θ_{M₂}(…)` whenever `B` is orthogonal
     for `diag(N₁,N₂)`. This covers Type I.
   * `qf_two`: two exact covers of one binary quadratic form `Σ_{x∈ℤ²} (−1)^{δ·x} t^{Ax²+2Bxy+Cy²+dx+ey}` give two theta
     expansions of the same sum. This covers Type II.

   All of this lives in `L = ℂ((t))` (HahnSeries summable families). Thetas are `ALz.θ`.
2. **Normal forms** (`Tools.lean`). These are quasi-periodicity (`θ_sh`), reflection (`θ_nfr1`, `θ_nfrm`) and zeros
   (`θz'`). A simp set merges monomials.
3. **Bridge to products** (`Bridge.lean`). It uses the injective `ι : ℤ⟦q⟧ → ℂ((t))` with `q ↦ t`, and the Jacobi
   triple product `θ_N(e,1) = ι(J_{e,N})` (`θ_unb`). Barred thetas use `θ_bar` and `θ_bar0` (`f(1,q)=2ψ(q)`). Every
   Type II identity lives at `t = q^{1/2}` and is pulled back by `S_inj 2`.
4. **Entry** (`E*.lean`). The lemmas `SG_E : G(q^a) f(−q^a) = f(−q^{2a},−q^{3a})` and
   `SH_E : H(q^a) f(−q^a) = f(−q^a,−q^{4a})` reduce each entry to its product identity `P3_k`. The remaining factors
   are split to a common modulus (`atom`), and `linear_combination` closes the goal.

The generic engine is proved once. Each entry adds one or two `ECS` instances (cover and uniqueness by `omega`), a
generated normal-form proof, and a short final step.

## Status of all 40

✅ means proved, with axioms `[propext, Classical.choice, Quot.sound]` only. ⬜ means not proved.

| # | Identity | Status / Lean name | Route |
|---|----------|--------------------|-------|
| 1 | 3.1  `G¹¹H − q²GH¹¹ = 1 + 11qG⁶H⁶` | ✅ `entry_3_1` (Defs) | repo's `ramanujan_R5` (`1/R⁵ − 11 − R⁵`) |
| 2 | 3.2  `G(q)G(q⁴) + qH(q)H(q⁴) = χ²(q)` | ✅ `entry_3_2` (E02) | Type I, `B=(1 4;−1 1)` on `f(1,q)f(−q²,−q²)` |
| 3 | 3.3  `G(q)G(q⁴) − qH(q)H(q⁴) = φ(q⁵)/f(−q²)` | ✅ `entry_3_3` (E03) | Watson: 3.2 + Lemma 7.1 (`φ²−φ(q⁵)²`, Type I `B=(1 2;−2 1)`) + square root fixed by constant term |
| 4 | 3.4  `G(q¹¹)H(q) − q²G(q)H(q¹¹) = 1` | ✅ `entry_3_4` (E04) | Type II, form `3x²+2xy+4y²+x+4y`, covers det 3 and 5 |
| 5 | 3.5  `G(q¹⁶)H(q) − q³G(q)H(q¹⁶) = χ(q²)` | ✅ `entry_3_5` (E05) | Type II, form `4x²+4xy+5y²+2x−3y`, sign `(−1)^{x+y}` |
| 6 | 3.6  `G(q)G(q⁹) + q²H(q)H(q⁹) = f²(−q³)/(f(−q)f(−q⁹))` | ✅ `entry_3_6` (E06) | Type II, form `2x²+2xy+5y²−2x−y`, sign `(−1)^y` |
| 7 | 3.7  `G(q²)G(q³) + qH(q²)H(q³) = χ(−q³)/χ(−q)` | ✅ `entry_3_7` (E07) | Type I, `B=(2 3;−1 1)` |
| 8 | 3.8  `G(q⁶)H(q) − qG(q)H(q⁶) = χ(−q)/χ(−q³)` | ✅ `entry_3_8` (E08) | Type I on `f(−q,−q)f(1,q³)`, `B=(1 3;−1 2)` |
| 9 | 3.9  `G(q⁷)H(q²) − qG(q²)H(q⁷) = χ(−q)/χ(−q⁷)` | ✅ `entry_3_9` (E09) | Type II, `3x²+2xy+5y²−x−5y` |
| 10 | 3.10 `G(q)G(q¹⁴) + q³H(q)H(q¹⁴) = χ(−q⁷)/χ(−q)` | ✅ `entry_3_10` (E10) | Type II, `3x²+2xy+5y²+3x+y` |
| 11 | 3.11 `G(q⁸)H(q³) − qG(q³)H(q⁸) = χ(−q)χ(−q⁴)/(χ(−q³)χ(−q¹²))` | ✅ `entry_3_11` (E11) | Type II, `4x²+4xy+7y²+2x+7y` |
| 12 | 3.12 `G(q)G(q²⁴) + q⁵H(q)H(q²⁴) = χ(−q³)χ(−q¹²)/(χ(−q)χ(−q⁴))` | ✅ `entry_3_12` (E12) | Type II, `5x²+2xy+5y²+x+5y` |
| 13 | 3.13 `G(q⁹)H(q⁴) − qG(q⁴)H(q⁹) = χ(−q)χ(−q⁶)/(χ(−q³)χ(−q¹⁸))` | ⬜ | Cao Type III (combined ECS / quintuple product) |
| 14 | 3.14 `G(q³⁶)H(q) − q⁷G(q)H(q³⁶) = χ(−q⁶)χ(−q⁹)/(χ(−q²)χ(−q³))` | ⬜ | Type III |
| 15 | 3.15(i) `G(q³)G(q⁷)+q²H(q³)H(q⁷) = G(q²¹)H(q) − q⁴G(q)H(q²¹)` | ⬜ | only known proof uses modular forms (Biagioli) |
| 16 | 3.15(ii) the same equals `(1/2√q)[χ(q^{1/2})χ(−q^{3/2})χ(q^{7/2})χ(−q^{21/2}) − …]` | ⬜ | modular forms |
| 17 | 3.16(i) `G(q²)G(q¹³)+q³H(q²)H(q¹³) = G(q²⁶)H(q) − q⁵G(q)H(q²⁶)` | ⬜ | Cao Type III, worked out in §3.4 |
| 18 | 3.16(ii) the same equals `√(χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³))` | ⬜ | Berndt et al. §19 (square-root argument as in 3.3) |
| 19 | 3.17 `G(q)G(q¹⁹)+q⁴H(q)H(q¹⁹) = …` (three χ terms) | ⬜ | Type III |
| 20 | 3.18 `G(q³¹)H(q) − q⁶G(q)H(q³¹) = …` | ⬜ | Type III (Bressoud) |
| 21 | 3.19(i) `{G(q)G(q³⁹)+q⁸H(q)H(q³⁹)}f(−q)f(−q³⁹) = {G(q¹³)H(q³)−q²G(q³)H(q¹³)}f(−q³)f(−q¹³)` | ✅ `entry_3_19_i` (E19) | Type II, `5x²+2xy+8y²+x+8y` |
| 22 | 3.19(ii) the same `= (1/2q)(φ(−q³)φ(−q¹³) − φ(−q)φ(−q³⁹))` | ⬜ | Type III |
| 23 | 3.20 `G(q)H(−q) + G(−q)H(q) = 2/χ²(−q²)` | ✅ `entry_3_20` (E20) | Watson: 3.21, `GH = f(−q⁵)/f(−q)` at `±q`, Lemma 23.1 `ψ²−qψ(q⁵)² = f(q,q⁴)f(q²,q³)` (Type I, `B=(1 2;−2 1)` on `f(1,q)²`, `P23_1`), square root fixed by the constant term |
| 24 | 3.21 `G(q)H(−q) − G(−q)H(q) = 2qψ(q¹⁰)/f(−q²)` | ✅ `entry_3_21` (E21) | Watson: 3.2 and 3.3 at `±q` (`q ↦ −q` bookkeeping in `NgTools`), Lemma 7.1 at `q ↦ −q²` (`lemma71_neg`) |
| 25 | 3.22 `G(−q)G(−q⁴) + qH(−q)H(−q⁴) = χ(q²)` | ⬜ | Type III |
| 26 | 3.23 `G(−q²)G(−q³) + qH(−q²)H(−q³) = χ(q)χ(q⁶)/(χ(q²)χ(q³))` | ⬜ | Type III |
| 27 | 3.24 `G(−q⁶)H(−q) − qH(−q⁶)G(−q) = χ(q²)χ(q³)/(χ(q)χ(q⁶))` | ⬜ | Type III |
| 28 | 3.25 `G(−q)G(q⁹) − q²H(−q)H(q⁹) = χ(−q)χ(q⁹)/χ(−q⁶)` | ⬜ | Bressoud |
| 29 | 3.26 `G(q¹¹)H(−q) + q²G(−q)H(q¹¹) = …` | ⬜ | Watson |
| 30 | 3.27(i) `U² + qV² = χ³(q)χ³(q¹¹)` (U, V with 44 and 4·11) | ⬜ | Watson |
| 31 | 3.27(ii) `UV + q = χ²(q)χ²(q¹¹)` | ⬜ | Watson |
| 32 | 3.28(i) `U/V = χ(−q)/χ(−q¹⁷)` (U = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷), V = G(q)G(q³⁴)+q⁷H(q)H(q³⁴)) | ✅ `entry_3_28_i` (E28) | Type II, `5x²+2xy+7y²+x+7y` |
| 33 | 3.28(ii) `U⁴V⁴ − qU²V² = …` | ⬜ | modular forms (claimed, never written; Berndt et al.) |
| 34 | 3.29 (23, 46) | ⬜ | modular forms only (Biagioli) |
| 35 | 3.30 (19, 76, with `−q`) | ⬜ | Type III / modular forms |
| 36 | 3.31 (33, 66) | ⬜ | modular forms only |
| 37 | 3.32 (22, 11·6) | ⬜ | modular forms only |
| 38 | 3.33 (54, 27) | ⬜ | Bressoud |
| 39 | 3.34 (19, 38, with `−q`) | ⬜ | Bressoud |
| 40 | 3.35 (94, 47, with a square root) | ⬜ | modular forms only |

**Proved: 16 of 40** (3.1–3.12, 3.19(i), 3.20, 3.21, 3.28(i)).

In the Lean statements `G(−q)` is `Ng G` and `ψ(q) = f(q,q³) = Σ_{n≥0} q^{n(n+1)/2}` is `RamanujanTau.Septic.ramF 1 3`, a sum definition whose product form `psi_chip` comes from the repo's `ramF_product`.

All 40 hold numerically to `q²⁰⁰` (`verify_forty.py`). Two of the memoir's typeset forms needed care. 3.16(ii) is a
single square root over the difference. 3.22 has `G(−q⁴)`, not `G(q⁴)`.

## Obstacles and estimates for the rest (after round 2)

* **3.20 and 3.21 are done.** The `q ↦ −q` toolkit is in `NgTools.lean`: `Ng ∘ S_{2k} = S_{2k}`, `Ng ∘ S₅ = S₅ ∘ Ng`,
  `(−q;−q)_∞ = f(−q²)χ(q)`, `φ(−q)` and `ψ`.
* **3.34** reduces, via 3.20 + 3.21 and `G(q)G(−q) = f(q⁴,q⁶)/f(−q²)`, to the four-product theta identity (33.6) of
  Berndt et al. That identity mixes moduli `(10,190)`, `(8,152)`, `(40,760)` (and `(2,38)` in the memoir's proof).
  `scripts/forty/combo.py` searched for (33.6) as a ℚ-linear combination of ECS relations. The search covered every
  determinant-19 and 76 form tried, all sign characters, linear terms in `[−3,3]`, and covers with entries up to 10.
  It found none. The memoir's proof also needs one-variable 2-dissections (33.10) and the identities (20.3), (20.5) and
  (20.6). So the engine needs a 1D-dissection relation added to the search basis. Estimate: about half a day.
* **3.13, 3.14, 3.16(i), 3.30** (Cao's Type III, "zoom out / zoom in"). Each needs specialised quintuple products
  `f(−x²,−λx)f(−λx³)/f(−x,−λx²) = f(−λ²x³,−λx⁶) + x f(−λ,−λ²x⁹)` in theta form. The repo's quintuple product
  (`MockTheta5.JTP.formal_quintuple_product_identity`, `thetaA*thetaB = qfac2InfL*quintTheta`) lives in
  `ℤ[z^{±1}]⟦q⟧`. Using it needs an evaluation map `z ↦ c tᵉ` into `ℂ((t))` with a summability proof.
  - A specialised quintuple product is not a single two-form ECS relation: the determinants `M₁M₂` of its two sides
    differ by a non-square. This was confirmed by a search on `2x²+2xy+2y²`.
  - Estimate: one to two days for the bridge, then about an hour per entry.
* **3.17, 3.18, 3.19(ii)**. 3.19(ii) mixes the inequivalent forms `x²+39y²` and `3x²+13y²` with `5x²+2xy+8y²`. No
  single form represents all the needed values (checked), so it needs a multi-form combination. 3.17 and 3.18
  (Bressoud) are similar.
* **G(−q) entries 3.22–3.26, 3.30**. `G(−q) = f(−q¹⁰)²/(f(q,q⁹)f(−q⁴,−q⁶))` is a quotient of two thetas, so these
  are four-theta identities. The memoir derives 3.22 and 3.25 from 3.5 and 3.14 using Watson's 2-dissection
  `G(q)f(−q²) = f(−q⁸)(G(q¹⁶) + qH(−q⁴))` (Lemma 4.1). That lemma itself rests on quintuple-product instances (4.26) and
  (4.27). Same bridge as above.
* **3.27, 3.33**: these use 3.4, 3.6–3.8 and modular-equation manipulations (memoir §§31–32). Not attempted.
* **Modular-only entries (3.15(i,ii), 3.16(ii), 3.28(ii), 3.29, 3.31, 3.32, 3.35): scoped only.**
  - `MTC/ThFactor.zero_count` (`Th(m)`) bounds zeros of theta functions in the elliptic variable `x` at fixed nome. It
    does not certify identities in `q`.
  - The only Sturm-type results are `TheoremA/LevelSixModularSturm.lean` (for genuine Mathlib `ModularForm`s on
    `Γ₀(6)`) and `BoylanWebb/Forms.lean` (Sturm mod ℓ, level 1).
  - Certifying these entries would need the eta quotients of levels 46–94 as `ModularForm` objects on `Γ₀(N)`: eta
    transformation laws, behaviour at all cusps, and a level-`N` Sturm bound. None of this exists, so no entry was
    attempted. A finite coefficient check is not a proof.
