# Lehmer's method for small n: `τ(n) ≠ 0` for `1 ≤ n < 74 627 999`

Directory: `RamanujanTau/LehmerSmall/` (4 new files; no existing file modified).
Target function: the repo's computable `RamanujanTau.tau` (coefficients of `q∏(1−qⁿ)²⁴`), linked to
`TauCong.tauPS` by `tau_eq_tauPS`.

## Headline (evidence level 1: Lean, axiom-clean)

```lean
theorem RamanujanTau.LehmerSmall.lehmer_below_74627999 :
    ∀ n, 1 ≤ n → n < 74627999 → τ n ≠ 0
```
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`. There are no `sorry`s, no new axioms and
no `native_decide`. The finite checks use `decide +kernel` and `norm_num`'s `Nat.Prime` extension.

Lehmer's 1947 bound is `214 928 639 999`. This result is about 2.9·10³ times smaller. The gap comes from the
congruences we did not prove (see "What remains").

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
| `Final.lean` | `no_candidate_below`, `lehmer_below_74627999` | the sieve and the headline |

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

## Numerical validation (evidence level 4, PARI/gp)

For `n ≤ 10⁵`, there are zero failures of:
* `τ ≡ nσ₃ (mod 7)`, `τ ≡ nσ₉ (mod 25)` (all `n`), `τ ≡ n²σ₇ (mod 3)`;
* the mod-9 formula (checked for `n ≤ 2·10⁴`);
* the classical `τ ≡ n²σ₇ (mod 27)` and `τ ≡ σ₁₁ (mod 2⁸)` for odd `n`.

The residues of `p mod 2¹⁸` satisfying the 2-adic condition are exactly those `≡ 31 (mod 32)`. The least
candidate primes:

| conditions used | first candidate (= bound) |
|---|---|
| 691, 25, 7 | 863 749 |
| 691, 25, 7, 3 | 3 316 799 |
| 691, 25, 7, 9 | 6 529 949 |
| **691, 25, 7, 9, 32 (proved)** | **74 627 999** |
| + mod 64 | 258 710 399 |
| + mod 64, 27 | 388 065 599 |

## What remains (to approach Lehmer's 2.1·10¹¹)

* **mod 64 (next step, elementary):** in `two_adic_of_tau_eq_zero` the `S₃³` term is `691·13824000·c₃(n)`,
  where `13824000 = 2¹²·3375`. If `c₃(p)` is even, the condition can be taken mod `2¹³`, and that forces
  `p ≡ −1 (mod 64)`.
  * Why `c₃(p)` is even for `p ≡ 7 (mod 8)`: `σ₁(m)` odd ⇒ `m ≡ 0,1,2,4 (mod 8)`. The only multiset of
    those residues with sum `≡ 7` is `{1,2,4}`, whose 6 orderings cancel mod 2.
  * Payoff: the bound rises to `258 710 399`. Estimated 1–2 sessions (parity of `σ₁`, then a support
    argument in `𝔽₂⟦q⟧`).
* **mod 27, 125, 49 and 2¹¹:** the classical forms are:
  * `τ ≡ n²σ₇ (mod 27)`;
  * `τ ≡ n⁻³⁰σ₇₁ (mod 125)`;
  * `τ ≡ nσ₉ (mod 49)` for `(n/7) = −1`;
  * Kolberg's mod-`2¹¹` congruence.

  These need second-order `ℓ`-adic information (the `θ`-iteration used here for mod 9 has to be pushed one
  more digit, or moved to higher level). The repo has these only as hypothesis classes
  (`Congruences/Mod3.lean` etc.).
* **mod 23:** "`(p/23) = 1` ⇒ `τ(p) ≢ 0 (mod 23)`" needs Wilton's theta-series identity for the
  class-number-3 forms of discriminant −23. The repo's `tau_mod23` covers only the other direction.
* **Lehmer's own computation** of `τ(p)` at the surviving candidates: not attempted. Kernel evaluation at
  `p ~ 10⁸` is infeasible.

## Literature

D. H. Lehmer, *The vanishing of Ramanujan's function τ(n)*, Duke Math. J. **14** (1947) 429–433;
S. Ramanujan (1916); G. N. Watson / J. R. Wilton (1929–30); O. Kolberg (1962);
H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of modular forms*
(LNM 350, 1973).
