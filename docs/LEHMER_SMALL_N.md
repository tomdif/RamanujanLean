# Lehmer's method for small n: `τ(n) ≠ 0` for `1 ≤ n < 21 492 863 999`

Directory: `RamanujanTau/LehmerSmall/` (8 Lean files plus one generator script; no existing file modified).
Target function: the repo's computable `RamanujanTau.tau` (coefficients of `q∏(1−qⁿ)²⁴`), linked to
`TauCong.tauPS` by `tau_eq_tauPS`.

## Headline (evidence level 1: Lean, axiom-clean)

```lean
theorem RamanujanTau.LehmerSmall.lehmer_below_21492863999 :
    ∀ n, 1 ≤ n → n < 21492863999 → τ n ≠ 0
```
(`FinalDeep.lean`.) `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. There are no `sorry`s, no
new axioms and no `native_decide`. The finite checks use `decide +kernel`, `norm_num` and `omega`.

Lehmer's 1947 bound is `214 928 639 999 = 2¹¹·3⁵·5⁴·691 − 1`. This result is exactly 10 times smaller.
* Our modulus is `2⁹·3⁵·5³·691`, so the gap is one factor `2²·5`.
* With Wilton's mod-23 restriction `(p/23) = −1` added, the first surviving candidate would be exactly
  Lehmer's number (see "What remains").

Earlier headlines in the same directory, still valid and axiom-clean:
* `lehmer_below_74627999` (`Final.lean`), from moduli `2⁵·3²·5²·691`;
* `lehmer_below_258710399` (`Final64.lean`), from moduli `2⁶·3²·5²·691`.

## Milestones (all axiom-clean)

| file | theorem | statement |
|---|---|---|
| `PrimePower.lean` | `tau_prime_pow_ne_zero` | `p` prime, `τ p ≠ 0` ⇒ `τ (p^k) ≠ 0` for all `k` |
| `PrimePower.lean` | `exists_prime_dvd_tau_eq_zero` | `τ n = 0`, `n ≥ 1` ⇒ `∃ p` prime, `p ∣ n`, `τ p = 0` (so the least zero is prime) |
| `PrimePower.lean` | `tau_ne_zero_of_primes_below` | no prime zero below `N` ⇒ no zero in `[1, N)` |
| `Congruences.lean` | `E4_mul_E6`, `E4_sq` | `E₄E₆ = 1 − 264Σσ₉qⁿ`, `E₄² = 1 + 480Σσ₇qⁿ` in `ℤ⟦q⟧` |
| `Congruences.lean` | `tau_mod7_all` | `τ(n) ≡ nσ₃(n) (mod 7)`, all `n ≥ 1` |
| `Congruences.lean` | `tau_mod25_all` | `τ(n) ≡ nσ₉(n) (mod 25)`, all `n ≥ 1` |
| `Congruences.lean` | `tau_mod3_all`, `core3` | `τ(n) ≡ n²σ₇(n) (mod 3)`, and the exact identity `320n²σ₇ = 160σ₇ + 176σ₉ + 3Z_n − 256τ` |
| `Refined.lean` | `tau_mod9_all` | `256τ ≡ 160σ₇ + 176σ₉ − 320n²σ₇ + 2(σ₁ + 5σ₃ − 6nσ₁) + 6σ₁ (mod 9)` |
| `Refined.lean` | `tau_E4cube_int`, `E4_cube` | `691[qⁿ]E₄³ = 65520σ₁₁ + 432000τ` in `ℤ`; `E₄³ = 1 − 720S₃ + 1440S₇ + 13824000S₃³` |
| `Refined.lean` | `two_adic_of_tau_eq_zero` | `τ(n) = 0` ⇒ `691(1440σ₇ − 720σ₃) ≡ 65520σ₁₁ (mod 2¹²)` |
| `Final.lean` | `prime_zero_conditions` | `τ p = 0` ⇒ `p ≡ −1` mod 691, 25, 9, 32, and `p ≡ 3,5,6 (mod 7)` |
| `Final.lean` | `no_candidate_below`, `lehmer_below_74627999` | the first sieve |
| `TwoAdic64.lean` | `sigma_odd_nonsquare_zmod2`, `sigma_zmod2_support` | `σ_k(m)` is even for odd non-square `m`; `σ_k(m)` odd ⇒ `m ≡ 0,1,2,4 (mod 8)` |
| `TwoAdic64.lean` | `S3_cube_even`, `two_adic8192_of_tau_eq_zero`, `prime_zero_mod64` | `[qⁿ]S₃³` even for `n ≡ 7 (mod 8)`; the 2-adic condition holds mod `2¹³`; a prime zero is `≡ −1 (mod 64)` |
| `Final64.lean` | `lehmer_below_258710399` | `τ(n) ≠ 0` for `n < 258 710 399` |
| `QuasiLin.lean` | `tE2_1 … tE2_5`, `tE4_1 … tE4_4`, `tE6_1 … tE6_3`, `tF8_1 … tF8_2`, `tF10_1` | `12ʲθʲF = P_{F,j}(E₂,E₄,E₆)` in `ℤ⟦q⟧`, from Ramanujan's ODEs |
| `QuasiLin.lean` | `linA` | `2520(1−E₂)²(E₄−E₂²)² = 725760θ³E₂ − 4354560θ⁴E₂ + 5225472θ⁵E₂ + 72576θ²E₄ − 580608θ³E₄ + 808704θ⁴E₄ − 69120θ²E₆ + 155520θ³E₆ + 20160θ²E₈ + 16E₄³ − 16E₆²` |
| `QuasiLin.lean` | `linB` | `360(E₄−E₂²)(E₄−1)² = −4320θE₂ + 5184θ²E₄ + 2880θE₆ − 720θ²E₈ − 864θE₁₀ + 128E₄³ − 128E₆²` |
| `QuasiLin.lean` | `condA`, `condB` | at a prime `p` with `τ(p)=0`: `2⁹3⁵ ∣ Q_A(p)` and `5³ ∣ Q_B(p)` (polynomials below) |
| `QuasiLin.lean` | `prime_zero_deep` | `τ p = 0` ⇒ `p ≡ −1` mod `512`, mod `243` and mod `125` |
| `FinalDeep.lean` | `no_candidate_below_21492863999`, `lehmer_below_21492863999` | the sieve and the headline |
| `TauModInstances.lean` | `linA_coeff` | `linA` at every `n ≥ 1`: `2520·24²·288²·[qⁿ]S₁²(θS₁)² = Σ_{d∣n} P_A(n,d) + 27648τ(n)` |
| `TauModInstances.lean` | `tau_mod27_coprime`, `instTauMod27` | `τ(n) ≡ n²σ₇(n) (mod 27)` for `3 ∤ n`; fills the hypothesis class `TauMod27` |
| `TauModInstances.lean` | `tau_mod256_odd`, `instTauMod2_8` | `τ(n) ≡ σ₁₁(n) (mod 2⁸)` for odd `n`; fills `TauMod2_8` |

## Method

1. **The least zero is prime.** Factor `X² − τ(p)X + p¹¹ = (X−x)(X−y)` over `ℂ`. The Hecke recurrence
   (`tau_hecke_recurrence`) gives `(x−y)τ(pᵏ) = x^{k+1} − y^{k+1}`.
   * If `x = y`, then `τ(pᵏ) = (k+1)xᵏ ≠ 0`.
   * If `x ≠ y` and `τ(pᵏ) = 0`, then `ζ = x/y` is a root of unity. So `ζ + ζ⁻¹ = τ(p)²/p¹¹ − 2` is a
     rational algebraic integer of absolute value at most 2, which gives `τ(p)² = m·p¹¹` with `m ∈ {0,…,4}`.
   * Counting `p`-adic valuations leaves only `(p,m) = (2,2)` and `(3,3)`. Both are false because
     `τ(2) = −24` and `τ(3) = 252`.
   * `m = 0` means `τ(p) = 0`.

   Multiplicativity (`tau_mul_coprime`) then finishes the argument. *Note:* the module docstring of the
   existing `LehmerReduction.lean` says `τ(pᵏ)` "can vanish independently of `τ(p)`". That is false, and
   `tau_prime_pow_ne_zero` refutes it. The file was left unchanged.
2. **Congruences, all from repo theorems.** The inputs are:
   * Ramanujan's ODEs over `ℤ` (`RamanujanODEProof.ramanujanODE`);
   * `E₄³ − E₆² = 1728Δ` (`ModP.ev_disc`);
   * the level-one structure theorem (`ModP.exists_poly_Eis` plus `exists_div`), used for `E₈ = E₄²` and
     `E₁₀ = E₄E₆`;
   * the `E₁₂` relation (`Mod691.tau_mod_relation`).

   How each congruence is derived:
   * **mod 7:** in `𝔽₇⟦q⟧` we have `E₆ = 1`, so `E₂ = E₄²` and `3θE₄ = 1728Δ`.
   * **mod 25:** `6θ(E₄E₆) = 5G − 5184Δ`, and `G` vanishes mod 5 because in `𝔽₅⟦q⟧` we have `E₄ = 1` and
     `E₂ = E₆`.
   * **mod 3:** `36θ²(E₄²) = 18X − 13824Δ` with `X = 3(W + 2Y) + 9Z`.
   * **mod 9:** add `Z ≡ 2S₁² + 2S₁ (mod 3)` and `12S₁² = S₁ + 5S₃ − 6θS₁`.
   * **2-adic:** `691·E₄³ = 691 + 65520S₁₁ + 432000Δ` together with the expansion of `E₄³` above, whose
     `S₃³` coefficient `13824000` is divisible by `2¹²`.
3. **At a prime zero** (using `σ_k(p) = 1 + pᵏ`), each congruence becomes a polynomial condition on
   `p mod m`, checked by `decide +kernel` over `ZMod m` for `m = 691, 25, 9, 7, 4096`.
   * The small primes 2, 3, 5 and 7 are excluded by their nonzero `τ` values.
   * The result is `p ≡ −1 (mod 4 975 200 = 691·25·9·32)` and `p mod 7 ∈ {3,5,6}`.
   * Below `74 627 999 = 15·4975200 − 1`, every `4975200j − 1` (`1 ≤ j ≤ 14`) is either composite
     (`norm_num`) or `≢ 3,5,6 (mod 7)`. `74 627 999` itself is prime, `≡ 5 (mod 7)`, and is the first
     candidate.

### The classical all-`n` congruences mod 27 and mod 2⁸ (`TauModInstances.lean`)

Both follow from the same identity `linA`, read at an arbitrary `n`. Write `n = de`.

* **mod 27.** `P_A(de,d) + 27648(de)²d⁷ = 2¹⁰3⁵·d⁴e²(d−e)h(d,e)`, and `(d−e)h(d,e) ≡ 0 (mod 3)` for `3 ∤ d, e`
  (checked over `ZMod 3`). So `27648(τ − n²σ₇) ≡ 0 (mod 3⁶)`.
* **mod 2⁸.** Put `g(d) = P_A(n,d) + 27648d¹¹`.
  * `g(d) + g(e) = 27648(d−e)²(d+e)k(d,e)`, and `2⁸ ∣ (d−e)²(d+e)k(d,e)` for odd `d, e`
    (`decide +kernel` over `ZMod 256`).
  * `g(d) = 0` when `d = e`.
  * The involution `d ↦ n/d` on the divisors then gives `Σ g ≡ 0 (mod 2¹⁸)`, i.e. `27648(τ − σ₁₁) ≡ 0 (mod 2¹⁸)`.

Kolberg's mod-2¹¹ class `TauMod2_11` is **not** reached: the `2`-power on the left of `linA` caps this route at
`τ` mod `2⁹`.

### Deeper congruences: quasimodular integrality (`TwoAdic64.lean`, `QuasiLin.lean`)

4. **mod 64 (elementary).** Work in `𝔽₂⟦q⟧` with `A = S₃ mod 2`.
   * `A` is supported on `n ≡ 0,1,2,4 (mod 8)`, by the divisor involution `d ↔ m/d` plus multiplicativity at 2.
   * `[qʲ]A² = 0` for `j ≡ 1,3,5,6,7 (mod 8)`, by the swap involution in characteristic 2.
   * Hence `[qⁿ]A³ = 0` for `n ≡ 7 (mod 8)`. The `S₃³` term `2¹²·3375·c(n)` therefore vanishes mod `2¹³`, which
     forces `p ≡ −1 (mod 64)`.

   This is superseded by the next item, but it is kept as a separate milestone.
5. **Integrality of quasimodular monomials (the main new idea).** Take any product `M` of the integer series
   `S_k` and `θʲS_k` with top weight `≤ 12`. Then `M` is an integer `q`-series and a quasimodular form, so
   `M = Σ a_{j,k} θʲE_k + b(E₄³ − E₆²) + …` with explicit rational `a, b`.
   * At a prime `p` with `τ(p) = 0`, every term on the right is a polynomial in `p`: use `σ_k(p) = 1 + pᵏ`, and
     note that `E₄³ − E₆² = 1728Δ` contributes `0`.
   * The integrality of `[q^p]M` therefore becomes a polynomial congruence on `p`.
   * A sympy search over all 41 such monomials showed that two of them already give everything the method can
     give:

     | monomial | relation to `E`'s | congruence at a prime zero |
     |---|---|---|
     | `A = S₁²(θS₁)²` | `(1−E₂)²(E₄−E₂²)² = 24²·288²·A` | `Q_A(p) = 350p⁹ − 2835p⁸ + 8280p⁷ − 9576p⁶ − 126p⁵ + 10170p⁴ − 8505p³ + 2240p² ≡ 0 (mod 2⁹·3⁵)`, whose only root prime to 6 is `p ≡ −1` (`decide +kernel` over `ZMod 512` and `ZMod 243`) |
     | `B = θS₁·S₃²` | `(E₄−E₂²)(E₄−1)² = 288·240²·B` | `Q_B(p) = 33p¹⁰ − 50p⁹ − 210p⁶ + 180p⁵ + 145p² − 162p ≡ 0 (mod 5³)`, forcing `p ≡ −1 (mod 125)` |

   * The exact identities `linA`/`linB` are proved from `θ`-chains `12ʲθʲF = P_{F,j}`. Each chain step is
     `θ`-Leibniz expansion followed by `linear_combination` with the three ODEs, using coefficients
     `∂P/∂E₂`, `4∂P/∂E₄` and `6∂P/∂E₆`.
   * The coefficient extraction uses `E4_sq` (`E₈ = E₄²`), `E4_mul_E6` (`E₁₀ = E₄E₆`) and `disc_eq`.
   * The certificates are produced by `scripts/lehmersmall/quasilin_gen.py`, which regenerates
     `QuasiLin.lean` byte-for-byte.
6. **Sieve.** A prime zero is `≡ −1 (mod 10 746 432 000 = 2⁹·3⁵·5³·691)` and `≡ 3,5,6 (mod 7)`.
   * The only number `≡ −1` below `21 492 863 999` is `10 746 431 999`. It is prime but `≡ 2 (mod 7)`.
   * `21 492 863 999` itself is prime and `≡ 5 (mod 7)`, so it is the first candidate.

## Numerical validation (evidence level 4, PARI/gp + sympy)

For `n ≤ 10⁵`, there are zero failures of:
* `τ ≡ nσ₃ (mod 7)`, `τ ≡ nσ₉ (mod 25)` (all `n`), `τ ≡ n²σ₇ (mod 3)`;
* the mod-9 formula (checked for `n ≤ 2·10⁴`);
* the classical `τ ≡ n²σ₇ (mod 27)` (all `n ≤ 5000`; fails mod 81) and `τ ≡ σ₁₁ (mod 2⁸)` for odd `n`;
* `τ ≡ n⁻³⁰σ₇₁ (mod 125)` for `5 ∤ n` and `τ ≡ nσ₉ (mod 49)` for `(n/7) = −1` (`n ≤ 2·10⁴`).

The residues of `p mod 2¹⁸` satisfying the mod-`2¹²` condition are exactly those `≡ 31 (mod 32)`.

The quasimodular search was run on all products of up to 6 factors `θᵃS_k` (`k ≤ 9`) with top weight `≤ 12`,
41 monomials in all. Each was fitted against `{nʲσ_k(n)} ∪ {τ(n)}` exactly on `n ≤ 45`. Combining all of
them gives no more than `p ≡ −1` mod `2⁹`, `3⁵`, `5³`, and `(p/7) = −1`. Imposing integrality at
`n = mp`, `p²`, `p³`, `p⁴` as well (using `τ(mp) = 0`, `τ(p²) = −p¹¹`, `τ(p⁴) = p²²`) gives nothing new. So
weight-`≤ 12` integrality is saturated at the proved modulus.

The first candidate under each set of conditions:

| conditions used | first candidate (= bound) | status |
|---|---|---|
| 691, 25, 7 | 863 749 | |
| 691, 25, 7, 9, 32 | 74 627 999 | proved (`Final.lean`) |
| 691, 25, 7, 9, 64 | 258 710 399 | proved (`Final64.lean`) |
| **691, 7, 2⁹, 3⁵, 5³** | **21 492 863 999** | **proved (`FinalDeep.lean`)** |
| + Wilton `(p/23) = −1` | 214 928 639 999 (= Lehmer) | not proved |
| + `2¹¹` or `5⁴` | 214 928 639 999 | not proved |
| + mod 49, `p⁹ ≡ −1` | 526 575 167 999 | not proved |
| + mod 49 and 23 | 1 117 628 927 999 | not proved |

## What remains (to reach and pass Lehmer's 2.1·10¹¹)

* **Only two candidates stand between us and Lehmer's bound** (numerical, PARI/sympy).
  * Below `214 928 639 999`, the numbers `k·10746432000 − 1` that are prime and `≡ 3,5,6 (mod 7)` are exactly
    `k = 2` (`21 492 863 999`) and `k = 7` (`75 225 023 999`).
  * Both have `(p/23) = +1`.
  * The coefficient `a(p)` of `q∏(1−qⁿ)(1−q²³ⁿ)` is `−1` for the first and `2` for the second. This was computed
    by the pentagonal double sum `a(p) = Σ_l (−1)^{k+l}` over `ω(k) + 23ω(l) = p − 1`.
  * `Δ ≡ η(z)η(23z) (mod 23)` is already proved in the repo (`hΨ` inside `TauCong.tau_mod23`). So
    `τ(p) ≡ a(p) ≢ 0 (mod 23)` for both, which would give Lehmer's bound **without** Wilton's general theorem.
  * What is needed is a Lean certificate of `a(p)` for these two `p`:
    * reindex the antidiagonal sum to the `~2·10⁵` values of `l`, using `coeff_pentSeries_support`;
    * kernel-check the non-pentagonality of `p − 1 − 23ω(l)`, using `r² < 24m+1 < (r+1)²` with a fuel-bounded
      integer square root.
  * Estimate: 1 session.
* **Wilton mod 23 in general.** Needed: `(p/23) = 1` ⇒ `τ(p) ≢ 0 (mod 23)`.
  * `Δ ≡ η(z)η(23z) (mod 23)` is elementary; the repo's `tau_mod23` uses it in the other direction.
  * The missing input is the weight-1 theta identity `η(z)η(23z) = ½(θ_{x²+xy+6y²} − θ_{2x²+xy+3y²})`. It gives
    `a(p) ∈ {2, −1}` for split `p`.
  * This needs level-23 modular-form or Sturm-bound infrastructure, which the repo does not have (there is no
    `FormalSturm`), or an elementary `q`-series proof of the identity.
  * Then the existing sieve, with `j ≤ 19` candidates, reaches `214 928 639 999`.
* **`2¹¹`, `5⁴` (Kolberg / Bambah–Chowla)** are out of reach of weight-`≤ 12` integrality (shown above). They need
  weight `> 12`, where cusp forms other than `Δ` appear, or theta-function arguments.
* **mod 49** (`τ ≡ nσ₉` for `(n/7) = −1`; checked numerically for `n ≤ 2·10⁴`) is likewise not reachable at weight
  `≤ 12`.
* **Lehmer's own computation** of `τ(p)` at surviving candidates was not attempted.

## Literature

D. H. Lehmer, *The vanishing of Ramanujan's function τ(n)*, Duke Math. J. **14** (1947) 429–433;
S. Ramanujan (1916); G. N. Watson / J. R. Wilton (1929–30); O. Kolberg (1962);
H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of modular forms*
(LNM 350, 1973).
