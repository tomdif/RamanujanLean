# Kolberg's congruence: `τ(n) ≡ σ₁₁(n) (mod 2¹¹)` for `n ≡ 1 (mod 8)` (the class `TauMod2_11`)

Directory: `RamanujanTau/KolbergTau/` (`Parity.lean`, `Main.lean`; new files only, nothing existing modified,
not imported from `RamanujanTau.lean`). Built with `lake build RamanujanTau.KolbergTau.Main`.

## Headline (evidence level 1: Lean, axiom-clean)

```lean
theorem RamanujanTau.KolbergTau.tau_mod2048_one_mod8 {n : ℕ} (hn : n ≠ 0) (h8 : n % 8 = 1) :
    (2048 : ℤ) ∣ TauCong.tauPS n - (σ 11 n : ℤ)
instance RamanujanTau.KolbergTau.instTauMod2_11 : TauMod2_11
theorem RamanujanTau.KolbergTau.tauMod2_11_holds {n : ℕ} (hn : n ≥ 1) (h8 : n % 8 = 1) :
    τ n ≡ sigma11 n [ZMOD 2048]
```
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each. There is no `sorry`, no new axiom and no
`native_decide`. This matches the class exactly (`Congruences/Mod2.lean`: `n ≥ 1 → n % 8 = 1 → τ n ≡ σ₁₁ n [ZMOD 2048]`).
With this instance, every congruence hypothesis class in `Congruences/` now has an instance.

## Milestones (all axiom-clean)

| file | theorem | statement |
|---|---|---|
| `Parity.lean` | `supp_mul`, `supp_res` | exponent supports mod 8 add under multiplication |
| `Parity.lean` | `S_decomp`, `T_decomp` | `S₁ = a + b + 2c`, `θS₁ = d + 2e`, with `a, d` supported on `1 mod 8` and `b` on `{0,2,4} mod 8` |
| `Parity.lean` | **`coeff_A_mod4`** (K1) | `n ≡ 1 (mod 8)` ⇒ `4 ∣ [qⁿ]S₁²(θS₁)²` |
| `Main.lean` | **`pair_dvd`** (K2) | `d` odd, `8 ∣ e − d` ⇒ `2¹¹ ∣ (d−e)²(d+e)k(d,e)` |
| `Main.lean` | **`sum_g_dvd`** (K3) | `n ≡ 1 (mod 8)` ⇒ `2²¹ ∣ Σ_{d∣n} (P_A(n,d) + 27648d¹¹)` |
| `Main.lean` | **`tau_mod2048_one_mod8`** | the headline |

## Method: the same identity `linA`, read 3 bits deeper

The weight-12 identity `linA` (`LehmerSmall/QuasiLin.lean`), read at `n` (`LehmerSmall.linA_coeff`), gives

  `27648·(τ(n) − σ₁₁(n)) = 2520·47775744·c(n) − Σ_{d∣n} g(d)`,

where `c(n) = [qⁿ]S₁²(θS₁)²`, `g(d) = P_A(n,d) + 27648d¹¹`, `2520·47775744 = 2¹⁹·229635` and `27648 = 2¹⁰·27`.

The earlier mod-2⁸ proof used only that `c(n)` is an integer, which gives `2¹⁸ ∣ Σg` and so 2⁸. The "cap at 2⁹"
noted in `LEHMER_SMALL_N.md` holds only for integrality alone. Knowing `c(n) mod 4` gives two more bits on the
left, and a sharper divisor pairing gives the rest:

1. **K1: `c(n) ≡ 0 (mod 4)` for `n ≡ 1 (mod 8)`.**
   * By `sigma_zmod2_support` (`TwoAdic64.lean`), `σ₁(m)` is even for `m ≡ 3,5,6,7 (mod 8)`, and `mσ₁(m)` is even
     unless `m ≡ 1 (mod 8)`.
   * So `S₁ = a + b + 2c` and `θS₁ = d + 2e`, where `a` and `d` are the `1 mod 8` parts, `b` is the
     `{0,2,4} mod 8` part of `S₁`, and `c, e` are integer series.
   * Then `S₁²(θS₁)² = a²d² + 2abd² + b²d² + 4Z` (by `ring`). The three terms are supported on residues
     `{4}`, `{3,5,7}` and `{0,2,4,6}` mod 8, so none of them reaches the residue 1.
2. **K2/K3: `Σg ≡ 0 (mod 2²¹)` for `n ≡ 1 (mod 8)`.**
   * Divisors pair as `d ↔ e = n/d`, and `de ≡ 1 (mod 8)` forces `d ≡ e (mod 8)`.
   * `g(d) + g(e) = 27648(d−e)²(d+e)k(d,e)`.
   * With `e = d + 8m`, this is `128·m²(d+4m)k(d,d+8m)`, and `16 ∣ m²(d+4m)k(d,d+8m)` for odd `d`
     (`decide` over `ZMod 16`, 256 cases).
   * Square divisors have `g(d) = 0`, and `Finset.sum_involution` finishes.
3. **Assembly.** `2¹⁰·27(τ − σ₁₁) = 2²¹(229635u − t)`, and `omega` gives `2¹¹ ∣ τ − σ₁₁`.

Routes (a) (higher-weight quasimodular forms), (b) (theta and Jacobi triple product) and (c) (Sturm bound) were all
unnecessary. The repo's only Sturm theorem is analytic, on Γ₀(6) (`TheoremA/LevelSixModularSturm.lean`), and has no
mod-2ᵏ form.

## Numerical validation (evidence level 4, numpy, exact τ mod 2¹⁴ for `n ≤ 10⁵`)

* `τ(n) ≡ σ₁₁(n) (mod 2¹¹)` holds for every `n ≡ 1 (mod 8)` with `n ≤ 10⁵`.
* Mod `2¹²` it fails for 3715 of those `n`, so `2¹¹` is sharp.
* For `n ≡ 1 (mod 8)` and `n ≤ 4000`: `c(n) mod 4 = 0` and `Σg/2¹⁸ mod 8 = 0`, as K1 and K3 predict.
* For the other odd classes, `c mod 4` and `Σg/2¹⁸ mod 8` vary. For example, at `n ≡ 3 (mod 8)` the true
  statement is `τ ≡ 1217σ₁₁ (mod 2¹³)`, not `σ₁₁`.

## Lehmer-type conditions (reported only)

* `TauMod2_11` does not apply at a prime zero: those are `≡ −1 (mod 512)`, so `≡ 7 (mod 8)`, not 1.
* The same method suggests a route to `p ≡ −1 (mod 2¹¹)` at a prime zero:
  * **(4)** Numerically, `c(p) ≡ 0 (mod 4)` for all 406 primes `p ≡ 15 (mod 16)` below `3·10⁴`. It fails for
    composite `n ≡ 15 (mod 16)`, for example `n = 15`.
  * **(4)** If `c(p) ≡ 0 (mod 4)`, then `linA` at a prime zero forces `p ≡ −1 (mod 2¹¹)`. This was checked over all
    `p ≡ 15 (mod 16)` below `2¹⁴`.
  * **(3)** By the K1 decomposition, `c(p)/2 mod 2` is the parity of `#{s, t, u odd > 0 : s² + 4t² + 2u² = p}`.
    That is a ternary, class-number-type parity, which is not proved here.
* **Effect on the sieve: none on its own.** With modulus `2¹¹·3⁵·5³·691 = 42 985 728 000` the first candidate is
  `5·42985728000 − 1 = 214 928 639 999`, which is exactly Lehmer's bound, already proved (`Lehmer1947.lean`).
  Getting past it needs `5⁴` or mod 49 as well (see the table in `LEHMER_SMALL_N.md`).

## Literature

O. Kolberg, *Congruences for Ramanujan's function τ(n)*, Årbok Univ. Bergen Mat.-Natur. Ser. 1962 no. 11;
R. P. Bambah, S. Chowla, H. Gupta, D. B. Lahiri, Quart. J. Math. 18 (1947);
H. P. F. Swinnerton-Dyer, LNM 350 (1973).
