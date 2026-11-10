# Ramanujan's forty identities for the Rogers–Ramanujan functions

Source of the statements: B. C. Berndt, G. Choi, Y.-S. Choi, H. Hahn, B. P. Yeap, A. J. Yee, H. Yesilyurt, J. Yi,
*Ramanujan's forty identities for the Rogers–Ramanujan functions*, Mem. AMS 188 (2007), no. 880, §3 (35 entries,
40 identities). The main proof method used here is from Z. Cao, *Quadratic forms, exact covering systems, and product
identities for theta functions*, arXiv:2503.11445 (Types I/II).

Lean: `RamanujanTau/Forty/`. Audit: `scripts/audit/forty9.lean` (all proved entries and the lemmas of rounds 1–9, 272 declarations, all `[propext, Classical.choice, Quot.sound]` or a subset; `forty.lean`–`forty8.lean` are the earlier rounds). Numerics: `scripts/forty/verify_forty.py` checks all 40
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
| 13 | 3.13 `G(q⁹)H(q⁴) − qG(q⁴)H(q⁹) = χ(−q)χ(−q⁶)/(χ(−q³)χ(−q¹⁸))` | ✅ `entry_3_13` (E13) | Cao Type III: form `7x²+6xy+9y²+6x`, covers `(1 3;−1 2)`, `(0 −3;1 1)`, quintuple product at `c=±1` (`ALz.quint_theta`), Cao (59) at `q⁹` |
| 14 | 3.14 `G(q³⁶)H(q) − q⁷G(q)H(q³⁶) = χ(−q⁶)χ(−q⁹)/(χ(−q²)χ(−q³))` | ✅ `entry_3_14` (E14) | Cao (64): Type II on `5x²+4xy+8y²+3x−6y` gives the numerator of 3.13; then 3.13 |
| 15 | 3.15(i) `G(q³)G(q⁷)+q²H(q³)H(q⁷) = G(q²¹)H(q) − q⁴G(q)H(q²¹)` | ✅ `entry_3_15_i` (E15) | new elementary proof: two Cramer eliminations with Entries 3.7–3.10 give `L₂(q)L₁(q²) = L₁(q)L₂(q²)` (`prod15a`, `prod15b`), then `D(q)L₂(q²) = L₂(q)D(q²)`, `D(0)=0` forces `D = 0` (`eq_zero_of_S2`) |
| 16 | 3.15(ii) the same equals `(1/2√q)[χ(q^{1/2})χ(−q^{3/2})χ(q^{7/2})χ(−q^{21/2}) − …]` | ⬜ | modular forms; see round-7 notes |
| 17 | 3.16(i) `G(q²)G(q¹³)+q³H(q²)H(q¹³) = G(q²⁶)H(q) − q⁵G(q)H(q²⁶)` | ✅ `entry_3_16_i` (E16) | Cao §3.4: form `5x²+2xy+8y²+x−5y`, four quintuple collapses, Cao (59) at `q` and `q¹³` |
| 18 | 3.16(ii) the same equals `√(χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³))` | ✅ `entry_3_16_ii` (E16ii; squared form), `entry_3_16_ii'` (other side), `entry_3_16_ii_unique` (the branch: unique square root with constant term 1) | Berndt et al. §19 without the operator `L`: Lemma 5.1 used through its quintuple-product components (`Q16`), Type I `(2 −13; 1 1)` on `f(1,q)φ(−q¹³)` (`P16_1`), Type II on `3x²+10xy+17y²−x+7y` (`P16_2`) |
| 19 | 3.17 `G(q)G(q¹⁹)+q⁴H(q)H(q¹⁹) = …` (three χ terms) | ✅ `entry_3_17` (E17), stated with `q ↦ q²` to clear `q^{1/2}` | Cao: form `4x²+2xy+5y²+4x+y` (det-5 and det-4 covers, Cao (80)/(81)) + 2-dissection of `φ` (`MTC.dissect2`) |
| 20 | 3.18 `G(q³¹)H(q) − q⁶G(q)H(q³¹) = …` | ✅ `entry_3_18` (E18), stated times `2q` | Cao (Identity 18): forms `(4,1,8)`, `(2,1,16)`, `(5,2,7)` of det 31 glued through `QS` (parity splits, swap, index-2 cover) |
| 21 | 3.19(i) `{G(q)G(q³⁹)+q⁸H(q)H(q³⁹)}f(−q)f(−q³⁹) = {G(q¹³)H(q³)−q²G(q³)H(q¹³)}f(−q³)f(−q¹³)` | ✅ `entry_3_19_i` (E19) | Type II, `5x²+2xy+8y²+x+8y` |
| 22 | 3.19(ii) the same `= (1/2q)(φ(−q³)φ(−q¹³) − φ(−q)φ(−q³⁹))` | ✅ `entry_3_19_ii` (E19ii), stated times `2q` | Cao (Identity 19-2): forms `(6,3,8)`, `(2,1,20)`, `(5,1,8)` of det 39 glued through `QS` |
| 23 | 3.20 `G(q)H(−q) + G(−q)H(q) = 2/χ²(−q²)` | ✅ `entry_3_20` (E20) | Watson: 3.21, `GH = f(−q⁵)/f(−q)` at `±q`, Lemma 23.1 `ψ²−qψ(q⁵)² = f(q,q⁴)f(q²,q³)` (Type I, `B=(1 2;−2 1)` on `f(1,q)²`, `P23_1`), square root fixed by the constant term |
| 24 | 3.21 `G(q)H(−q) − G(−q)H(q) = 2qψ(q¹⁰)/f(−q²)` | ✅ `entry_3_21` (E21) | Watson: 3.2 and 3.3 at `±q` (`q ↦ −q` bookkeeping in `NgTools`), Lemma 7.1 at `q ↦ −q²` (`lemma71_neg`) |
| 25 | 3.22 `G(−q)G(−q⁴) + qH(−q)H(−q⁴) = χ(q²)` | ✅ `entry_3_22` (E22) | Watson's Lemma 4.1 (`lemma41a`, `lemma41b`) substituted in 3.5, then `q ↦ −q` (Berndt et al. §25) |
| 26 | 3.23 `G(−q²)G(−q³) + qH(−q²)H(−q³) = χ(q)χ(q⁶)/(χ(q²)χ(q³))` | ✅ `entry_3_23` (E23) | Lemma 4.1 in 3.8 (Berndt et al. (15.4)); odd part = 3.11 at `q²`; even part via (11.10) at `−q` (`star1110_neg`), `S_inj`, `q ↦ −q` |
| 27 | 3.24 `G(−q⁶)H(−q) − qH(−q⁶)G(−q) = χ(q²)χ(q³)/(χ(q)χ(q⁶))` | ✅ `entry_3_24` (E24) | Lemma 4.1 at `q³` in 3.7 (Berndt et al. (16.5)); even part = 3.12 at `q²`; odd part via (11.10) (`P11`, 2-dissection of `f(q,q⁵)`) |
| 28 | 3.25 `G(−q)G(q⁹) − q²H(−q)H(q⁹) = χ(−q)χ(q⁹)/χ(−q⁶)` | ✅ `entry_3_25` (E25) | Berndt et al. §28 second proof: Type I cover `(1 1;−2 3)` of `f(q⁶,q¹²)f(−q)`, quintuple at `c=−1`, product forms of `G(−q)`, `H(−q)` (`NgOdd`) |
| 29 | 3.26 `G(q¹¹)H(−q) + q²G(−q)H(q¹¹) = …` | ✅ `entry_3_26` (E26), `entry_3_26'` (cleared) | Watson §29 with Schröter's degree-11 equation replaced by `M26chi` (E26a: Type II on the form of 3.4, covers det 3 and 4, + `dis2`); (29.7)–(29.9) from Lemma 4.1, 3.4, 3.20; sign by constant term |
| 30 | 3.27(i) `U² + qV² = χ³(q)χ³(q¹¹)` (U, V with 44 and 4·11) | ✅ `entry_3_27_i` (E26) | Watson: (29.14) (`entry_29_14`) from 3.26 and (29.7); pulled back by `q ↦ q²`, times its `q ↦ −q` image |
| 31 | 3.27(ii) `UV + q = χ²(q)χ²(q¹¹)` | ✅ `entry_3_27_ii` (E27) | Watson (29.17): `3 × 3` elimination with Entry 3.4 at `q⁴` and Entry 3.2 at `q¹¹` |
| 32 | 3.28(i) `U/V = χ(−q)/χ(−q¹⁷)` (U = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷), V = G(q)G(q³⁴)+q⁷H(q)H(q³⁴)) | ✅ `entry_3_28_i` (E28) | Type II, `5x²+2xy+7y²+x+7y` |
| 33 | 3.28(ii) `U⁴V⁴ − qU²V² = (χ³(−q¹⁷)/χ³(−q))(1 + q²χ³(−q)/χ³(−q¹⁷))²` | ✅ `entry_3_28_ii` (E28ii), `entry_3_28_ii'` (cleared) | Yesilyurt JMAA 2012 §3: lattice identities `E28p`, `E28m` (E28b/c); his (3.1)–(3.6) as series identities (E28e/E28g); the algebra (3.29)–(3.44) in the fraction field (`alg28`, E28d); the root at (3.40) chosen mod `q³` (`hbr28`); see round-9 notes |
| 34 | 3.29 `{G(q²)G(q²³)+q⁵H(q²)H(q²³)}{G(q⁴⁶)H(q)−q⁹G(q)H(q⁴⁶)} = χ(−q)χ(−q²³) + q + 2q²/(χ(−q)χ(−q²³))` | ✅ `entry_3_29` (E29) | Yesilyurt JMAA 2012 §4 in Cao's language: one form `7x²+12xy+15y²+5x+y`, covers det 5 and 10, signs `(−1)^x`, `(−1)^y` (E29b–E29d); degree-23 equation `M23` by a det-23 QS gluing (E29a) |
| 35 | 3.30 `{G(q¹⁹)H(q⁴)−q³G(q⁴)H(q¹⁹)}/{G(q⁷⁶)H(−q)+q¹⁵G(−q)H(q⁷⁶)} = χ(−q²)/χ(−q³⁸)` | ✅ `entry_3_30` (E30) | Yesilyurt/Cao: form `10x²+8xy+13y²+6x+10y`, four quintuple collapses (`c=±1`), Cao (59) at `q¹⁹`, `NgOdd` |
| 36 | 3.31 (33, 66) | ✅ `entry_3_31` (E31) | Berndt et al. §31: two `3 × 3` eliminations (`NU31`, `MT31`; Entries 3.4, 3.7, 3.8) + Entry 3.32 |
| 37 | 3.32 (22, 11·6) | ✅ `entry_3_32` (E32, E32a) | after Yesilyurt (JNT 2009) but without his 3-dissection: two Type II identities of determinant 396 (`L32T`: `8x²−4xy+50y²+2x+16y`; `L32U`: `18x²−12xy+24y²+16x+2y`), each collapsed by `quint1`/`quintm` to the same `Φ = f(q³,q⁵)f(q⁹⁹,q¹⁶⁵) − q¹⁷f(q,q⁷)f(q³³,q²³¹)` |
| 38 | 3.33 (54, 27) | ✅ `entry_3_33` (E33), denominators cleared; `entry_3_33'` quotient form | Berndt et al. §32 second proof: Entries 3.6–3.8 at `q, q², q³, q⁶, q⁹`, two `3 × 3` eliminations, 3-dissections of `φ(−q)` and `ψ(q)` (`dis3` from `θ_dissect`) |
| 39 | 3.34 (19, 38, with `−q`) | ✅ `entry_3_34` (E34) | Berndt et al. §33: 3.20 + 3.21, `G(q)G(−q)f(−q²) = f(q⁴,q⁶)`; (33.6) from `M3_17`, the 20-coset cover `(1 −19; 1 1)` of `φ(±q)φ(±q¹⁹)`, a new Type II for `ψ(q²)ψ(q³⁸)` (form `4x²+4xy+20y²+2x−18y`, covers det 2 and 10), `dis2` |
| 40 | 3.35 (94, 47, with a square root) | ⬜ | Yesilyurt's product formula `entry_3_35_AB` is proved (E35b–E35); the level-47 eta–theta identity `L47` is proved (E35d); open: two even-part identities and the assembly of (5.18), see round-9 notes |

**Proved: 38 of 40** (3.1–3.14, 3.15(i), 3.16(i,ii), 3.17, 3.18, 3.19(i,ii), 3.20–3.27, 3.28(i,ii), 3.29, 3.30–3.34).
Open: 3.15(ii), 3.35.

In the Lean statements `G(−q)` is `Ng G` and `ψ(q) = f(q,q³) = Σ_{n≥0} q^{n(n+1)/2}` is `RamanujanTau.Septic.ramF 1 3`, a sum definition whose product form `psi_chip` comes from the repo's `ramF_product`.

All 40 hold numerically to `q²⁰⁰` (`verify_forty.py`). Two of the memoir's typeset forms needed care. 3.16(ii) is a
single square root over the difference. 3.22 has `G(−q⁴)`, not `G(q⁴)`.

## Round 3 notes

* **No new quintuple-product bridge was needed.** The repo already has the theta-form quintuple product
  `ALz.quint_theta` (`RamanujanTau/ALQuint.lean`):
  `(θ_{3N}(N+3e,c³) + c tᵉ θ_{3N}(2N+3e,c³)) θ_N(e,c) = θ_{3N}(N,1) θ_N(2e,c²)`.
  It is proved directly in `ℂ((t))` by a parity split of `ℤ²`, so it is directly compatible with `θθ_lattice`. The
  wrappers `quint1` (`c=1`, E16) and `quintm` (`c=−1`, E13) normalise numerals. The `ℤ[z^{±1}]⟦q⟧` form
  `formal_quintuple_product_identity` was not needed.
* `MTC.dissect2` supplies the 2-dissections (`dis2`, E17).
* `NgOdd.lean` gives `G(−q)` and `H(−q)` as product quotients (`NgG_prod`, `NgH_prod`) via
  `(−q^c;q^M)(q^c;q^M) = (q^{2c};q^{2M})`.
* Cao (59) appears as `R59a` and `R59b`, proved by splitting to a common modulus.

## Round 4 notes

* **Watson's Lemma 4.1** (Berndt et al. (4.23)/(4.24)) is in `W41.lean` and `W41b.lean`:
  - `lemma41a : G·f(−q²) = f(−q⁸)(G(q¹⁶) + qH(−q⁴))`.
  - `lemma41b : H·f(−q²) = f(−q⁸)(q³H(q¹⁶) + G(−q⁴))`.

  Each is proved by a quintuple collapse at nome `q¹⁰`, two `dis2` dissections and two quintuple collapses at
  `c = −1`, nome `q⁴⁰`, followed by `NgOdd` product forms.
* (11.7)/(11.10) are in `R11.lean`: the 2-dissection of `f(q,q⁵)` (`L11`, `P11`). They are used as `star1110` (E24)
  and, after `q ↦ −q`, as `star1110_neg` (E23).
* The parity arguments ("equate the odd parts") are done without a parity operator. The known part (Entries 3.11 and
  3.12 at `q²`) is subtracted, the remainder is matched with a product identity, and `S_inj 2` then undoes `q ↦ q²`.

## Round 5 notes

* **`QS` engine** (`QS.lean`). `QS F` is the sum over `ℤ²` of a summable function. `QS_cover` glues along any exact
  cover (not only orthogonal ones), `qmono_cmap` gives the transformed form on each coset, `qmono_summ` shows every
  positive definite form is summable (generic orthogonal cover `(1 −Bq; 0 A)`), and `QS_orth` gives the theta-product
  expansion. Cao's Type III proofs (3.18, 3.19(ii)) are chains of `QS_sub` steps. The script
  `scripts/forty/gen3.py` emits them (`gen_sub` for a change of variables or parity split, `gen_orth` for a product
  expansion).
* **3.34**. The memoir's (20.6) uses its Theorem 4.14. Here `ψ(q²)ψ(q³⁸)` is a Type II identity: the form
  `4x²+4xy+20y²+2x−18y` has covers `(1 1; 0 −2)` (det 2, both cosets give `ψ(q²)ψ(q³⁸)`) and `(0 10; 1 −1)` (det 10).
  A 20-coset cover of `θ₂(0,−1)θ₃₈(0,−1)` alone does not work: its even cosets give atoms that only cancel through a
  further identity.
* **3.33** uses the memoir's second proof. Both determinant eliminations are explicit `linear_combination`s (`hN33`,
  `hM33`). `dis3` is the 3-dissection from `ALz.θ_dissect`.
* **3.27(ii)** is pure algebra from Entries 3.2 and 3.4 (Watson's determinant (29.17); the memoir misprints its middle
  row).

## Round 6 notes

* **3.16(ii)** (`E16iiA.lean`, `E16ii.lean`). The memoir's §19 multiplies two `q^{1/5}`-dissections and takes the
  integral part `L`. That step is not needed: Lemma 5.1 is the statement that the components of the 5-dissection of
  `f(−q^{1/5})` are `f²(−q²,−q³)/f(−q)` etc., and each component identity is one quintuple product (`quint1`). So
  with `a₁ = f(−q⁴,−q⁶)`, `a₂ = f(−q²,−q⁸)`, `b₁ = f(−q²⁶,−q³⁹)`, `b₂ = f(−q¹³,−q⁵²)`, `A = a₁b₁ + q³a₂b₂`:
  `a₂E₀ = f(−q¹⁰)a₁`, `a₁E₄ = f(−q¹⁰)a₂` (and the same at `q¹³`) give `A² = f(−q²)f(−q¹³)·Bk16` (`core16`).
  `Bk16 = ψ(q)φ(−q¹³) − qf(−q)f(−q²⁶)` is the memoir's (19.17) + (19.24): a 15-coset Type I cover of `f(1,q)φ(−q¹³)`
  and a Type II on `3x²+10xy+17y²−x+7y` (covers of det 3 with one vanishing coset, and det 15). Then
  `X² = χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³)`; the square root is pinned by the constant term (`entry_3_16_ii_unique`).
* **3.32 and 3.31** (`E32a.lean`, `E32.lean`, `E31.lean`). Scoping found Yesilyurt, *A generalization of a
  modular identity of Rogers*, J. Number Theory 129 (2009) 1256–1271, §5: elementary proofs of 3.30, 3.31, 3.32 from a
  generalised Rogers identity plus a 3-dissection. The 3-dissection is avoided here: with `g(q) = f(−q²,−q³)`,
  `h(q) = f(−q,−q⁴)` and `Φ(q) = f(q³,q⁵)f(q⁹⁹,q¹⁶⁵) − q¹⁷f(q,q⁷)f(q³³,q²³¹)`, both
  `g(q³)g(q²²) + q⁵h(q³)h(q²²) = χ(−q³)χ(−q³³)Φ` and `h(q⁶)g(q¹¹) − qg(q⁶)h(q¹¹) = χ(−q)χ(−q¹¹)Φ` hold, and each
  is one Type II identity (forms found by a direct search over determinant 396: their det-5 covers collapse by
  `quint1` + Cao (59) to the bracket, their det-4 covers collapse by `quintm` to `Φ`). Dividing gives 3.32. Entry
  3.31 then follows from the memoir's §31 (`N U = 1 − qW`, `M T = −q + 1/W`, both `ring` identities plus Entries 3.4,
  3.7, 3.8).

## Round 7 notes

* **The degree-11 modular equation as a Type II identity** (`E26a.lean`). The form of Entry 3.4,
  `3x²+2xy+4y²+x+4y` with sign `(−1)^x`, also has the determinant-4 cover `(0 −4; 1 1)`. Its cosets give
  `2f(−q²)f(−q²²) = 2ψ(q⁸)φ(q⁴⁴) − 2q²ψ(q²)ψ(q²²) + 2q¹⁰φ(q⁴)ψ(q⁸⁸)` (`L3_26`, in `ℂ((t))` with `t = q`). With
  `φ(q) = φ(q⁴) + 2qψ(q⁸)` this is `φ(q)φ(q¹¹) − φ(−q)φ(−q¹¹) − 4q³ψ(q²)ψ(q²²) = 4q f(−q²)f(−q²²)` (`M3_26`), i.e.
  `χ²(q)χ²(q¹¹) − χ²(−q)χ²(−q¹¹) − 4q³/(χ²(−q²)χ²(−q²²)) = 4q` (`M26chi`). This is the level-11 member of the
  family of 3.17 (`4q·[3.4 bracket] = …`) and the exact replacement for Schröter's equation in Watson's §29.
* **3.26** (`E26.lean`). The four-theta reduction of round 6 was not needed. (29.7) is Lemma 4.1 at `±q`, `q¹¹`
  multiplied out; the terms with exponent `≡ 3 (mod 4)` are Entry 3.4 at `q¹⁶` and `−q⁴`
  (`T26_expand`, `T26_expand_neg`). Hence `YZ(T(−q) − T(q)) = 4q³` (`T26_diff`), with `Y = χ(−q²)χ(−q²²)`,
  `Z = χ(−q⁴)χ(−q⁴⁴)`. `Y²(T(q)T(−q) − 1) = 4q²` (`T26_prod`) is pure algebra: `T(q)T(−q)` minus the product of
  Entry 3.4 at `q` and `−q` is `q²` times Entry 3.20 at `q` and `q¹¹`. With `M26chi` at `q²` these give
  `(TYZ + 2q³)² = (χ(q²)χ(q²²)Z)²`, and the constant term picks the sign.
* **3.27(i)**. (29.14) `U(−q⁴) + q²V(−q⁴) = χ(q²)χ(q²²)χ(−q⁴)χ(−q⁴⁴)` is (29.7) plus 3.26 (`entry_29_14`).
  Pulled back by `S_inj 2` it is `U(−q²) + qV(−q²) = χ(q)χ(q¹¹)χ(−q²)χ(−q²²)` (`star26_plus`); its `q ↦ −q`
  image is `star26_minus`. Their product is 3.27(i) at `−q²`, and `S_inj 2`, `Ng_Ng` undo the substitution.
* **3.15(i)** (`E15.lean`) is new: no modular forms and no theta identity are needed. With
  `L₁ = G(q³)G(q⁷)+q²H(q³)H(q⁷)` and `L₂ = G(q²¹)H(q) − q⁴G(q)H(q²¹)`:
  - Entries 3.7 at `q⁷` and 3.9 at `q³` form a `2 × 2` system in `G(q²¹)`, `H(q²¹)` with determinant `−q³L₁(q²)`.
    Cramer's rule plus Entries 3.8 and 3.10 give
    `L₂(q)L₁(q²)·χ(−q)χ(−q³)χ(−q⁷)χ(−q²¹) = χ²(−q)χ²(−q²¹) + qχ²(−q³)χ²(−q⁷)` (`prod15a`).
  - Entries 3.7 and 3.10 at `q³` form a system in `G(q³)`, `H(q³)` with determinant `−qL₂(q²)`. With 3.8 at `q⁷`
    and 3.9 this gives the same right side for `L₁(q)L₂(q²)` (`prod15b`).
  - So `D = L₁ − L₂` satisfies `D(q)L₂(q²) = L₂(q)D(q²)` and `D(0) = 0`. The lowest coefficient of `D` would sit at
    `n` on the left and `2n` on the right, so `D = 0` (`eq_zero_of_S2`).
  As a by-product, `L(q)L(q²) = u + q/u` with `u = χ(−q)χ(−q²¹)/(χ(−q³)χ(−q⁷))`.

## Round 8 notes

* **Yesilyurt's sums are Type II identities.** Source: H. Yesilyurt, *Elementary proofs of some identities of Ramanujan
  for the Rogers–Ramanujan functions*, JMAA 388 (2012) 420–434 (proofs of 3.28(ii), 3.29, 3.35). His
  `R(ε,δ,l,t,α,β,m,p)` ((2.18), `x = y = 1`) is
  `Σ_{(M,J)∈ℤ²} (−1)^{εM+δJ} q^{[β(2M+t)² + α(2pJ+2mM+mt+pl)²]/(4p)}`, i.e. the binary form
  `λM² + 2αm MJ + αp J² + …` (`λ = (αm²+β)/p`, determinant `αβ`) with its product cover of determinant `p`.
  His Theorems 2.7/2.8 are a second orthogonal cover (determinant `p₁`) of the same form after a unimodular change of
  variables, and his Lemmas 2.5/2.6 are quintuple collapses (`quint1`, `quintm`) of pairs of cosets. So each of his
  identities is one `qf_two` plus collapses, exactly as for 3.30 and 3.32. `scripts/forty/round8/rsum.py` turns his
  parameters into the form; `genw.py` is `gen.py` with a wider numeric window (large coset shifts).
* **The degree-23 modular equation** (`E29a.lean`, `M23`): `χ(q)χ(q²³) − χ(−q)χ(−q²³) = 2q + 2q³/(χ(−q²)χ(−q⁴⁶))`,
  i.e. `φ(−q²)φ(−q⁴⁶) − 2q³ψ(−q)ψ(−q²³) − φ(−q)φ(−q²³) = 2q f(−q)f(−q²³)` (`P23`). This is the determinant-23
  analogue of Cao's (71) (3.18): at `t² = q`, `A − B = t²C` for `A = (4,1,6)`, `B = (2,1,12)`,
  `C = (3,1,8)` with linear part `(1,8)`, glued by one index-2 cover of each form and three unimodular maps
  (`m23a.py`–`m23c.py`, `gen_e29a.py`).
* **3.29** (`E29b`–`E29`). The form `7x²+12xy+15y²+5x+y` (Yesilyurt's (4.1)) with covers `(−5 0; 2 −1)` and
  `(−1 −9; 1 −1)`. With sign `(−1)^x` (`L29p`) the determinant-5 side is `f(−q²)f(−Q²)A(q²)` (`D5p_ι`); with sign
  `(−1)^y` (`L29m`) it is `f(−q²)f(−Q²)A(q)A(−q)` (`D5m_ι`, uses Entry 3.21 at `Q` and `G(q)G(−q) = f(q⁴,q⁶)/f(−q²)`).
  The determinant-10 sides are `Ye ∓ Yo` with the same two groups: `Yo = q²f(−q⁴)f(−Q⁴)A(q²)`,
  `Ye = f(−q⁴)f(−Q⁴)A(q⁴)B(−q²)` (Entry 3.3 at `−q²`, Yesilyurt (4.4)–(4.10)). Hence his (4.13)
  `(v + q)A(q) = B(−q)A(q²)` (`E1_29`) and the analogue of his closing remark for 23,
  `A(q)A(−q) = (1 + 2q²/w)A(q²)` (`E2_29`), which replaces his second functional equation (4.14) (that one needs two
  more lattice identities). With `M23`: `w·AB = (w + 2q²)(u − q)` and then 3.29.
* **3.35, partial** (`E35b`–`E35`). Same pipeline at 47: form `10x²+6xy+15y²+12x+13y`, covers `(−5 0; 1 −1)` /
  `(5 0; −1 1)` and `(−1 3; 0 −10)`, signs `(−1)^x` and `(−1)^{x+y}`. Proved: (5.6) (`E1_47`),
  `A(q)A(−q) = (1 + 2q⁴/w)A(q²)` (`E2_47`; Yesilyurt's closing remark prints `2q²`, which is wrong), and
  **`entry_3_35_AB`**: `{G(q)G(q⁹⁴)+q¹⁹H(q)H(q⁹⁴)}{G(q⁴⁷)H(q²)−q⁹G(q²)H(q⁴⁷)} = (q² + χ(q)χ(q⁴⁷))(1 + 2q⁴/(χ(−q²)χ(−q⁹⁴)))`.
  Given this, Entry 3.35 (squared form) is equivalent to the degree-47 equation, Yesilyurt's (5.24):
  with `L = u + v`, `T = uv = w`, `4T³ − T²L² + 2q²T²L + 8q⁴T² + 4q⁶TL + 4q⁸T − 4q¹² = 0` (sympy: the numerator of
  `D² − q²(4v + 9q² + 8q⁴/v)`, `D = u − v − q² + 2q⁶/w`, is exactly `−(5.24)`). (5.24) itself follows from
  - (5.18) `X₁ = ½(φ(q)φ(Q)+φ(−q)φ(−Q)) + 2q¹²ψ(q²)ψ(Q²) + q²(f(q)f(Q)+f(−q)f(−Q)) + 2q⁸f(−q⁴)f(−Q⁴)` with
    `X₁ = Σ_{x≡y (2)} q^{(x²+47y²)/2} = φ(q²)φ(Q²) + 4q²⁴ψ(q⁴)ψ(Q⁴)` (`f(q) = (−q;−q)_∞`; checked, `m47a.py`), and
  - `X₁² = ½(φ²(q)φ²(Q) + φ²(−q)φ²(−Q)) + 8q²⁴ψ²(q²)ψ²(Q²)` (from `φ²(q) = φ²(q²) + 4qψ²(q⁴)` and `φ(q)ψ(q²) = ψ²(q)`),
  then eliminating `X₁` and cancelling two non-vanishing factors. The missing piece is a lattice proof of (5.18).
  `f(q)f(Q)` is not a combination of the Cao-friendly products (least squares, `m47b.py`/`m47c.py`), but on the two
  cosets `n ≡ m (2)`, `n ≢ m (2)` of `f(−q)f(−Q)` the forms are integral (`72m²+6mk+6k²−24m−k`, …) and `q ↦ −q` is a
  sign character, so all five terms are `QS` of integral forms (`m47d.py`). A search for a tautological refinement
  (index-2 and index-3 splits, depth 2, linear-algebra matching of pieces, `m47e.py`, `m47f.py`) found none.
* **3.28(ii), partial** (`E28b`, `E28c`). The form `5x²+34xy+68y²+x` (Yesilyurt's (3.9)/(3.17)) with covers
  `(0 −4; 1 1)` and `(1 17; 0 −5)`; sign `(−1)^{x+y}` gives `E28p`:
  `f(−q⁸)(φ(−Q⁴)ψ(−q²) − q⁴ψ(−Q²)φ(−q⁴)) = f(−q²)f(−Q²)V(q²)ψ(−q²)` (his (3.13) at `q²`), sign `(−1)^y` gives
  `E28m`: the same with `+` equals `f(−q²)f(−Q²)V(q)V(−q)ψ(−q²)` (his (3.21)). Open: the algebra. In terms of
  `a₁ = χ(q)`, `a₂ = χ(−q)`, `b₁ = χ(Q)`, `b₂ = χ(−Q)`, (3.1) and (3.2) give `U(±q)`, `V(±q)`, `V(q²)` explicitly, and
  (3.5), (3.6), (3.6) at `−q` become three polynomial relations (`e28f.py`). Singular: (3.7) and (3.8) are **not** in
  the ideal they generate, even after multiplying by `(a₁a₂b₁b₂q)^k`, `k ≤ 4` (`round8/e28_ideal.sing`); (3.16) and (3.31) are
  identities in this parametrisation. Yesilyurt's derivation chooses a root at (3.39) → (3.40)
  (`(S²(q²) − X)² = 4q⁴`, `X = S(q)S(−q)S(−q²)S(q⁴)`), which an ideal computation cannot see; a Lean proof has to make
  that choice (via a low-order coefficient) and needs his (3.2), (3.4) (with the 2-dissections (3.23)), (3.5), (3.6).
  But even `(S²(q²)−X−2q²)(S²(q²)−X+2q²)` is not in that ideal (`round8/e28_branch.sing`), so the level-1 relations
  from (3.1), (3.2), (3.5), (3.6) alone are not enough: (3.4) (through (3.23)) or Jacobi's `χ⁸(q) − χ⁸(−q) = 16q/χ⁸(−q²)`
  at `q` and `Q` must enter.

## Round 9 notes

* **3.28(ii) is proved** (`entry_3_28_ii`, quotient form; `entry_3_28_ii'`, cleared:
  `(U⁴V⁴ − qU²V²)χ³(−q)χ³(−q¹⁷) = (χ³(−q¹⁷) + q²χ³(−q))²`). Yesilyurt's §3, organised in three layers:
  - *Series identities* (E28e, E28g; names `Y*`), with `a1 = χ(q)`, `a2 = χ(−q)`, `b1 = χ(Q)`, `b2 = χ(−Q)`,
    `c = a1a2 = χ(−q²)`, `d = b1b2 = χ(−Q²)`: (1.4) `Y14` and its images at `−q, q², −q², q⁴`; (3.13) `Y13A` (from
    `E28p` by `S_inj 2`); (3.21) `Y21` (= `E28m`); (3.15) `Y15` (the `3 × 3` determinant is a ring identity, plus
    Entries 3.2 at `±q` and 3.20); the 2-dissection of `φ` in product form `phi_dis` and his (3.23) `J23`; then (3.1)
    `Y1`, (3.2) `Y2`, (3.3) `Y3`, (3.4) `Y4`, (3.5) `Y5`, (3.28) pulled back `P28`, (3.6) `Y6` and its images
    `Y6m`, `Y6q2`.
  - *Algebra* in an abstract integral domain / field: `glue1`–`glue3`, `alg4`, `alg5`, `alg27`, `alg6` (E28f; each
    certificate checked by `scripts/forty/round9/glue.py`) and `alg28` (E28d), which runs (3.29)–(3.44) with the
    explicit parametrisation by `a1, a2, b1, b2` (`field_simp; ring`) and is applied in `FractionRing ℤ⟦q⟧`.
    `(3.4)` (`alg4`) needs (3.3) at `q²`, (3.1) at `q⁴` and (3.23) at `q` and `Q`, as the round-8 Singular check
    predicted.
  - *The branch* (3.39) → (3.40): `(S²(q²) − R)² = 4q⁴` with the explicit square root
    `R = χ(−q²)V(q)V(−q)U(−q²)V(q⁴)/χ(−Q²)` of (3.35); the other factor
    `(S²(q²) + 2q²)χ(−Q²) − χ(−q²)V(q)V(−q)U(−q²)V(q⁴)` is `≡ 4q² (mod q³)` (`hbr28`), computed in
    `ℤ⟦q⟧ ⧸ (q³)` from `Pinf ≡ Pfin _ _ 2`, `S_a f ≡ f(0)` for `a ≥ 3`, `G ≡ 1 + q + q²`, `G(−q) ≡ 1 − q + q²`,
    `G(q²) ≡ 1 + q²` (`πG`, `πNgG`, `πS2G`). `scripts/forty/round9/branch.py` has the quotients.
* **3.35: the level-47 eta–theta identity** (E35d, `L47`). With `θ(Q) = Σ_{ℤ²} q^{Q(x,y)}`:
  `2q²f(−q)f(−q⁴⁷) = θ(2x²+xy+6y²) − θ(3x²+xy+4y²)` (`h(−47) = 5`; the eta product is half the difference of the
  two non-principal genus-mates). In `t` (`t² = q`): `2f(−q)f(−q⁴⁷)` is the single form `3x²+2xy+16y²+x+16y` with
  sign `(−1)^x` (`m47u.py`), and `A − B = t⁴C` glues by index-2 covers and three unimodular maps (`m47v.py`,
  `gen_e47.py`), exactly as `P23` for 23.
* **3.35: reduction of Yesilyurt's (5.18)** (checked to `q⁷⁰⁰`, `m47x.py`). Put
  `Θ1 = φ(q)φ(Q) + 4q¹²ψ(q²)ψ(Q²)`, `Θ2 = φ(q²)φ(Q²) + 2q⁶ψ(q)ψ(Q) + 4q²⁴ψ(q⁴)ψ(Q⁴)`,
  `Θ3 = φ(q³)φ(Q³) + 2q⁴f(q²,q⁴)f(Q²,Q⁴) + 2q¹⁶f(q,q⁵)f(Q,Q⁵) + 4q³⁶ψ(q⁶)ψ(Q⁶)` (the theta series of
  `x²+xy+12y²`, `2x²+xy+6y²`, `3x²+xy+4y²`; `Θ2`, `Θ3` are `LA47`, `LB47` at `t² = q`). Then
  - (E) `Θ2 − Θ3 = 2q²f(−q)f(−Q)` (`L47`);
  - (R2) `q⁶(ψ(q)ψ(Q) + ψ(−q)ψ(−Q)) = Θ3(q²) − Θ2(q⁴)` (equivalently `Θ2(q) + Θ2(−q) = 2(Θ3(q²) + Θ1(q²) − Θ2(q⁴))`);
  - (R3) `Θ3(q) + Θ3(−q) = 2(Θ2(q²) + Θ3(q²) − Θ3(q⁴))`;
  - `Θ2(q²) = Θ1(q⁴) + 2q¹²ψ(q²)ψ(Q²)` (termwise), `X₁ = Θ1(q²)`, `½(φ(q)φ(Q)+φ(−q)φ(−Q)) = Θ1(q⁴)`.
  So `q²(f(q)f(Q) + f(−q)f(−Q)) = ½[(E) + Ng (E)] = Θ1(q²) − Θ2(q²) − Θ2(q⁴) + Θ3(q⁴)` and
  `2q⁸f(−q⁴)f(−Q⁴) = Θ2(q⁴) − Θ3(q⁴)` (`S 4` of (E)); their sum is (5.18). (R2), (R3) are the Hecke relations at the
  split prime 2 (`x even` ↦ `θ3(q²)`, `y even` ↦ `θ1(q²)`, both even ↦ `θ2(q⁴)`, and the same for `θ3`); as QS identities
  they are tautological: the split-tree search (`tree.py`, `m47r2b.py`) solves (R2) at depth 3 (residual `2·10⁻¹¹`,
  none at depth ≤ 2). Remaining for 3.35: integral gluings for (R2), (R3) extracted from the depth-3 solution, the
  product forms of `L47` (bar thetas via `θ_bar`), the assembly of (5.18), `X₁² = ½(φ²(q)φ²(Q)+φ²(−q)φ²(−Q)) +
  8q²⁴ψ²(q²)ψ²(Q²)` (a Type I for `φ²`), and the algebra (5.20)–(5.24) with the two non-vanishing factors.
* **3.15(ii)**: not attempted beyond scoping. By the uniqueness argument of round 7 it is equivalent to
  `M(q)M(q²) = u + q/u` for `M = Odd[A](s)/s`; since `Odd[A](s) = (A(s) − A(−s))/2` with `A` an eta quotient, this
  is a linear relation among five weight-0 eta quotients (`A(±s)A(±s²)` and `u + q/u`). A Cao-style proof would
  need a common denominator that turns every term into a product of two theta functions; that has not been checked.

## Obstacles for the rest (after round 7)

* **3.15(ii)**. Write `A(q) = χ(q)χ(−q³)χ(q⁷)χ(−q²¹) = f(q,q⁵)f(q⁷,q³⁵)/(f(−q¹²)f(−q⁸⁴))`. The entry says the odd part
  of `A` is `qL(q²)`. It is checked numerically: the odd part is `qL(q²)`, and the even part is a function of `q⁴`
  that is not an eta quotient or a two-term `GG ± HH` combination. Cleared, the entry is
  `L(s)f(−s⁶)f(−s⁴²) = Ψ(s) = f(s²,s¹⁰)f(s²⁸,s⁵⁶) + s³f(s⁴,s⁸)f(s¹⁴,s⁷⁰)` (checked numerically; `Ψ` is
  the odd part of `f(q,q⁵)f(q⁷,q³⁵)`, and `L(s)f(−s³)f(−s⁷)` is a two-term theta sum). This is a weight-2 (4-dimensional) identity. Searches found nothing:
  - the one-`Φ` trick of 3.32 (the brackets `L₁/χχ`, `L₂/χχ` and `L/χ` as two-term products of moduli `(M, 7M)`,
    `(M, 21M)`, `(M, 3M)` with `M ≤ 24`): no match;
  - single-form Type II with two det-5 covers (det-126 forms; the only fit, `9x²+6xy+15y²`, gives identities with
    `G(q³)G(−q⁷)`, i.e. a sign-twisted relative of 3.15(i), not (ii)).
  Since `L` is the unique series with `L(0) = 1` and `L(q)L(q²)Π = χ²(−q)χ²(−q²¹) + qχ²(−q³)χ²(−q⁷)`
  (`Π = χ(−q)χ(−q³)χ(−q⁷)χ(−q²¹)`), it would also suffice to prove the pure product identity
  `Odd(A)(q)·Odd(A)(q²)·Π(q²) = q³(χ²(−q²)χ²(−q⁴²) + q²χ²(−q⁶)χ²(−q¹⁴))`. That identity is not proved.
* **3.28(ii), 3.29, 3.35** (not attempted this round). The elimination trick of 3.15(i) needs other entries at the
  same level. There are none at levels 17·2, 23·2 and 47·2: only 3.28(i) at level 34, and nothing at 46 or 94. The
  route is still Yesilyurt (JMAA 2012), which needs the degree-17/23/47 modular equations as theta identities. The
  3.17/3.26 pattern (a Type II with covers of determinants 3 or 5 and 4) is the natural source for those.

## Obstacles for the rest (after round 6, kept for reference)

* **3.26 and 3.27(i)** (proved in round 7 by a different route). Reduction checked numerically to `q³⁰⁰`: with
  `Br(q) = T(q)·f(q)f(−q¹¹) = f(−q²²,−q³³)f(q,−q⁴) + q²f(−q²,q³)f(−q¹¹,−q⁴⁴)` (`T` = the left side of 3.26),
  Entry 3.26 is equivalent to the four-theta identity
  `Br(q)·f(−q²)f(−q²²) = ψ(q)ψ(−q¹¹)φ(−q⁴)φ(−q⁴⁴) − 2q³ f(q)f(−q¹¹)f(−q⁸)f(−q⁸⁸)`, where `f(q) = (−q;−q)_∞`
  (it uses `χ(q²)f(−q²) = φ(−q⁴)` and `χ(q)χ(−q²) = f(q)/f(−q⁴)`). Given 3.26, (29.14) and then 3.27(i) are algebra
  (Watson §29). The right side has two terms that are not single products, so the one-`Φ` trick used for 3.31/3.32
  does not apply. A proof needs either a 4-dimensional ECS or a multi-form `QS` gluing as in 3.18/3.19(ii). No forms
  and covers were found in this round; the search was not run for lack of time.
* **3.15(i,ii), 3.28(ii), 3.29, 3.35** (scoped only). Yesilyurt, *Elementary proofs of some identities of Ramanujan
  for the Rogers–Ramanujan functions*, J. Math. Anal. Appl. 388 (2012) 420–434, proves 3.28(ii) (the last identity
  that had no proof) and gives elementary proofs of 3.29 and 3.35. His proofs use the generalised Rogers identity of
  the 2009 paper together with Ramanujan's modular equations of degree 23 and 47 and several of the forty identities.
  Those modular equations are not in the repo, so these are the next candidates only if the degree-23/47 equations can
  be written as theta identities. For 3.15 no elementary proof was located in this pass; Andrews–Berndt, *Ramanujan's
  Lost Notebook, Part III*, Ch. 8 is said to give elementary proofs of all forty and is the reference to check. No
  2025–2026 arXiv paper (Cao or others) giving Type I/II/III proofs of these entries was found.

## Obstacles for the rest (after round 5, kept for reference)

* **3.26 and 3.27(i)**. Everything in Watson's proof (§29) is elementary except one step. (29.2)/(29.3) are
  `lemma41a`/`lemma41b`. (29.5)–(29.9) are algebra with Entries 3.4, 3.20 and 3.24. Those give
  `χ(−q²)χ(−q⁴)χ(−q²²)χ(−q⁴⁴)T(q) = U(−q⁴) + q²V(−q⁴) − 2q³`, `T(−q) − T(q) = 4q³/(…)` and
  `1 − T(q)T(−q) + 4q²/(χ²(−q²)χ²(−q²²)) = 0`. The missing step is (29.13),
  `T(q) + T(−q) = 2χ(q²)χ(q²²)/(χ(−q²)χ(−q²²))`. It is equivalent to (29.14),
  `U(−q⁴) + q²V(−q⁴) = χ(q²)χ(−q⁴)χ(q²²)χ(−q⁴⁴)`. Watson gets it from Schröter's degree-11 modular equation and a
  square root. A Cao-style route would prove (29.14) directly. After clearing `f(−q^a)` it is a four-product theta
  identity, probably over forms of determinant 11 or 44. It is the analogue of what `QS` now does for 3.18 and 3.19(ii),
  but no forms and covers have been found yet. Given (29.14), 3.26 follows from (29.7) and 3.27(i) from
  (29.14)·(29.15), both by algebra. Estimate: a search with `ecs.py`/`gen3.py` over det-11/44 forms, then about half
  a day if a gluing exists.
* **Modular-only entries (3.15(i,ii), 3.16(ii), 3.28(ii), 3.29, 3.31, 3.32, 3.35)**: unchanged; see below. 3.16(ii)
  has an elementary proof in Berndt et al. §19 (a square-root argument as for 3.3), so it is the next candidate.

## Obstacles and estimates (after round 4, kept for reference)


* **3.20 and 3.21 are done.** The `q ↦ −q` toolkit is in `NgTools.lean`: `Ng ∘ S_{2k} = S_{2k}`, `Ng ∘ S₅ = S₅ ∘ Ng`,
  `(−q;−q)_∞ = f(−q²)χ(q)`, `φ(−q)` and `ψ`.
* **3.34** reduces, via 3.20 + 3.21 and `G(q)G(−q) = f(q⁴,q⁶)/f(−q²)`, to the four-product theta identity (33.6) of
  Berndt et al. That identity mixes moduli `(10,190)`, `(8,152)`, `(40,760)` (and `(2,38)` in the memoir's proof).
  `scripts/forty/combo.py` searched for (33.6) as a ℚ-linear combination of ECS relations. The search covered every
  determinant-19 and 76 form tried, all sign characters, linear terms in `[−3,3]`, and covers with entries up to 10.
  It found none. The memoir's proof also needs one-variable 2-dissections (33.10) and the identities (20.3), (20.5) and
  (20.6). So the engine needs a 1D-dissection relation added to the search basis. Estimate: about half a day.
* **(Round 2 note, now resolved: 3.13, 3.14, 3.16(i) and 3.30 are proved.)** Cao's Type III ("zoom out / zoom in") needs specialised quintuple products
  `f(−x²,−λx)f(−λx³)/f(−x,−λx²) = f(−λ²x³,−λx⁶) + x f(−λ,−λ²x⁹)` in theta form. The repo's quintuple product
  (`MockTheta5.JTP.formal_quintuple_product_identity`, `thetaA*thetaB = qfac2InfL*quintTheta`) lives in
  `ℤ[z^{±1}]⟦q⟧`. Using it needs an evaluation map `z ↦ c tᵉ` into `ℂ((t))` with a summability proof.
  - A specialised quintuple product is not a single two-form ECS relation: the determinants `M₁M₂` of its two sides
    differ by a non-square. This was confirmed by a search on `2x²+2xy+2y²`.
  - Estimate: one to two days for the bridge, then about an hour per entry.
* **3.17, 3.18, 3.19(ii)**. 3.19(ii) mixes the inequivalent forms `x²+39y²` and `3x²+13y²` with `5x²+2xy+8y²`. No
  single form represents all the needed values (checked), so it needs a multi-form combination. 3.17 and 3.18
  (Bressoud) are similar.
* **3.26 and 3.27(i,ii)**. Berndt et al.'s only elementary proof (§29) uses Schröter's modular equation of degree 11,
  `(αβ)^{1/4} + ((1−α)(1−β))^{1/4} + 2^{4/3}(αβ(1−α)(1−β))^{1/12} = 1`, in terms of moduli. That equation is not in
  the repo. 3.27 is derived from 3.26 in §29. A theta-function proof would need a substitute for that modular
  equation.
* **3.34** reduces to Berndt et al. (33.6) via 3.20, 3.21 (both proved) and `G(q)G(−q) = f(q⁴,q⁶)/f(−q²)` (an easy
  product identity). (33.6) follows from:
  - (33.7), which is `P3_17` at `q²`;
  - the 20-coset Type I cover `B = (1 −19; 1 1)` of `φ(q)φ(q¹⁹)` (20.4)/(20.5);
  - the 5-coset cover of `ψ(−q)ψ(−q¹⁹)` (20.6);
  - the 2-dissections (33.10) (`dis2`).

  Every ingredient is available. Estimate: about half a day.
* **3.18, 3.19(ii)**: Cao's proofs glue sums of three different forms of determinant 31 or 39 by parity splits. This
  needs `SummableFamily` versions of non-product form sums. `hs_split` already accepts arbitrary families, so the
  missing piece is constructing the sums `Σ q^{Q(x)}` as families (positive-definite finiteness). Estimate: one day.
* **3.33** (§32) uses 3.6, 3.7, 3.8 and modular-equation manipulations. Not attempted.
* **Superseded round-3 note**, kept for reference. Its 3.22–3.24 items are now done: 3.23 and 3.24 follow the memoir §§26–27. They need two
  Type I covers of `φ(−q¹²)ψ(q)` and `f(−1,−q²⁴)ψ(q)` (Rogers' Theorem 4.5), plus 2-dissections of the negative-nome
  thetas `f(−q²,q³)`. The latter is done by applying `Ng` to a `dissect2` product identity. Estimate: about 2 h each.
  3.22 needs Watson's Lemma 4.1 (4.23) and (4.24). Each is a quintuple collapse (`quint1`/`quintm`) plus two `dis2`
  and the `NgOdd` product forms, about 1.5 h each; then 3.22 is algebra from 3.5. Original note: `G(−q) = f(−q¹⁰)²/(f(q,q⁹)f(−q⁴,−q⁶))` is a quotient of two thetas, so these
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
