# Andrews 1966 for the coefficients of f(q): the full asymptotic conditional on one named hypothesis `Hb`, and the k = 1 term unconditionally

`f(q) = Σ q^{n²}/(−q;q)_n² = Σ α(n) qⁿ`, where `α(n) = N(0,2,n) − N(1,2,n)` (`Dragonette.α`).

> **Later status (2026-11-04): `Hb` is proved, so everything below is unconditional.** `MockCusp.Hb_holds`
> proves `Hb (max Ceven Codd) (3/2)` and `MockCusp.HbSharp_holds` proves `Hb Csharp 1`. Plugged into the
> conditional theorems of this document they give `MockCusp.andrews_1966_unconditional` (printed main term,
> error `O(n log n)`) and **`MockCusp.andrews_1966_sqrt_log_unconditional`** (printed main term, Andrews' own
> error `O(√n log n)`); see [MOCK_THETA_CUSPS](MOCK_THETA_CUSPS.md). The "paper only" and "what is left"
> items below describe the state before that, and all these files are now in the root import.

Andrews (1966) proved

  `α(n) = π(24n−1)^{−1/4} Σ_{k ≤ √n} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)/k · I_{1/2}(π√(24n−1)/(12k)) + O(√n log n)`.

**What is proved here.**

1. **(Lean, axiom-clean, unconditional)** The `k = 1` term with a power-saving error (`andrews_k1_isBigO`, Part I
   below). It also proves the transformation of `b` at every cusp.
2. **(Lean, axiom-clean, conditional on one named hypothesis `Hb`)** The **full** Andrews asymptotic: the main
   terms summed over `k ≤ ⌊√n⌋/2`, with error `O(N^{2D−1} log N)`, `N = ⌊√n⌋`. Under `Hb` with `D ≤ 1` this is
   Andrews' `O(√n log n)` (`andrews_1966_of_Hb`, `andrews_1966_isBigO_of_Hb`, `andrews_1966_sqrt_log_of_Hb`).
   The Kloosterman sum is that of the multiplier of `b`, which is proved to be
   `ω_b(h,k) = e^{πi(2s(h,k) − 3s(h,2k))}` (`omegaB_eq_dsum`).
3. **(Lean, axiom-clean, unconditional)** Andrews' sign and shift (`Ab_printed`):
   `(−1)^k A_b(k,n) = (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)`, where `A_K(x) = Σ e^{πi s(h,K) − 2πixh/K}` is
   Rademacher's sum (`AAnd`; `AAnd_nat`: equals `Rademacher.Ak` at integers). It follows from the Dedekind-sum
   congruence `2s(h,k) − 4s(h,2k) ≡ ⌊(k+1)/2⌋ − k + h(1+(−1)^k)/4 (mod 2)` (`T_cong`), which is proved by a
   Euclidean induction that uses only reciprocity. **Hence the headline is stated with Andrews' printed main term,
   over his range `k ≤ √n`** (`andrews_1966_printed_of_Hb`, `andrews_1966_printed_isBigO_of_Hb`).
4. **(numerical)** `Hb` is checked at 772 points: 18 denominators `K ≤ 30`, `|z|` down to `2·10⁻⁴`, `|f|` up to
   `1.5·10¹³`. The printed main sum over `k ≤ ⌊√n⌋` matches the exact `α(n)` to within **0.65** for every `n ≤ 2000`
   (`numerics/mainsum_full.txt`). Over `k ≤ ⌊√n⌋/2` the error is `≤ 3`.

### Headline, as printed (`Printed.lean`, conditional on `Hb`, axiom-clean)

```lean
def Andrews66.AAnd (K : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.range K).filter (fun h => Nat.Coprime h K), cexp (π * I * dsum h K - 2 * π * I * x * h / K)
def Andrews66.shiftA (k n : ℕ) : ℝ := n - k * (1 + (-1) ^ k) / 4
def Andrews66.andrewsPrinted (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (Nat.sqrt n), (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n) * (MK (2 * k) n : ℂ)
theorem Andrews66.Ab_printed {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (-1 : ℂ) ^ k * Ab k n = (-1 : ℂ) ^ ((k + 1) / 2) * AAnd (2 * k) (shiftA k n)
theorem Andrews66.T_cong : ∀ k : ℕ, 0 < k → ∀ h : ℕ, Nat.Coprime h (2 * k) →
    ∃ m : ℤ, 2 * Tq h k - Gq h k = 4 * m      -- Tq = 2s(h,k) − 4s(h,2k), Gq = (k mod 2) − k + [k even]·h
theorem Andrews66.andrews_1966_printed_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n → ‖(Dragonette.α n : ℂ) - andrewsPrinted n‖ ≤
      A₁ * ((Nat.sqrt n : ℝ) ^ (2 * D - 1) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n
theorem Andrews66.andrews_1966_printed_isBigO_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : D ≤ 1) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsPrinted n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n))
```

`MK (2k) n = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k` (`MK_two`). So `andrewsPrinted` is exactly Andrews' sum.

**How the congruence is proved (`Ded.lean`).** Write `T(h,k) = 2s(h,k) − 4s(h,2k)` and `U(k,h) = 2s(k,h) − 4s(2k,h)`.
- Two applications of reciprocity give `T(h,k) + U(k,h) = 1/2 − k/(2h)`.
- Since `U(k,h)` depends only on `k mod h`, `T(h,k) = T(h, k mod h) − ⌊k/h⌋/2`.
- `T` is `2k`-periodic in `h`, and `T(2k−h,k) = −T(h,k)` (`dsum_neg`).
- The base case is `T(1,k) = (1−k)/2`.
- The integer `G` obeys the same recursion mod 4. This is the parity computation `G_step`.
- Strong induction on `k` then gives `T_cong`.

**Extending the range to `k ≤ √n`.** For `N/2 < k ≤ N` the Bessel argument is `≤ 3`. So each extra term has
norm `≤ 2√24·e³` (`extra_term_le`), and together they cost `O(N)`.

## The hypothesis `Hb` (milestone M-b)

```lean
-- q = Rademacher.qp h K z = e^{2πi(h+iz)/K},  ε_K = (−1)^{K/2} (K even), 0 (K odd)
def Andrews66.epsK (K : ℕ) : ℂ := if Even K then (-1) ^ (K / 2) else 0
def Andrews66.Hb (C D : ℝ) : Prop :=
  ∀ K : ℕ, 0 < K → ∀ h : ℕ, Nat.Coprime h K → ∀ z : ℂ, 0 < z.re → (K : ℝ) / 2 ≤ (1 / z).re →
    ‖fA (Rademacher.qp h K z) - epsK K * bE (Rademacher.qp h K z)‖ ≤ C * ‖z‖ ^ (-D)
```

Here `fA = MockTheta3.Radial.fA` is `f`, and `bE = F(q²)²/F(q)³ = (q;q)³_∞/(q²;q²)²_∞` is `b`.

**The region.** It is `τ = (h+iz)/K` with `Re(1/z) ≥ K/2`, i.e. the disc `|z − 1/K| ≤ 1/K`. In `τ` this is the
disc of radius `1/K²` tangent to ℝ at `h/K`, twice the Ford disc. Every point of every Farey arc of order `N`
on the line `Im τ = 1/N²` lies in it (`re_inv_ge`).

**Why it is weak.** It asks only for a polynomial bound in `1/|z|`, with no main term. Any `D` will do, and `Hb_mono`
shows that smaller `D` implies larger `D`. The Ramanujan/Watson phenomenon it encodes is that at even
denominators `f` and `(−1)^{K/2}b` have the same exponentially large principal part `ω z^{−1/2}e^{π/(12Kz)}`, with
the sign independent of `h`, and that at odd denominators `f` has no principal part. What remains after
subtracting is the Mordell-integral part, of size about `|z|^{−1/2}`. This is what the general-cusp transformation
of `f` (Watson 1936; Gordon–McIntosh; Zwegers' μ) gives. It is the input to be discharged later.

**Numerical check** (`Andrews66/numerics/hb2.py`, `hb3.py`, 60-digit mpmath):
- `f` is summed from its `q`-series.
- `b` comes from its proved transformation `b_transform_even`, so it can be evaluated arbitrarily close to the
  cusp. The multiplier is fitted at `z = 1/K`.
- The sample points are `w = 1/z = K(r + iv)` with `r ∈ {0.5, 2, 3, 8, 30, 100}`, `v ∈ {0, ±1, 2, 4, 10, 16, 40, 50, −100}`.
  This includes the tangential boundary `r = 1/2`.
- The cusps are `K ∈ {1,…,6, 7, 8, 9, 10, 12, 16, 21, 24, 30}`, with several `h` each.

Results:
- `sup |f − ε_K b|·|z| = 2.09` and `sup |f − ε_K b|·|z|^{1/2} = 2.66` over the sample. So `Hb(3, 1)`, and even
  `Hb(3, 1/2)`, is consistent with every sample point.
- The cancellation is real. At `K = 30, h = 1, w = 30(100 − 100i)` we have `|f| = 1.5·10¹³` but `|f − b| = 9.9`.
  Using the wrong sign, or `ε` depending on `h`, would fail by 13 orders of magnitude.
- The largest `|f − ε b|` seen is `43`, at the odd cusp `21` on the tangential boundary with `|z| = 4.8·10⁻⁴`. This
  is consistent with Mordell-integral growth `|z|^{−1/2}`.

## Headline results, part II (Lean, conditional on `Hb`, axiom-clean)

```lean
-- M_{2k}(n) = √24/(√k√(24n−1)) sinh(π√(24n−1)/(12k)) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k   (MK_two)
def Andrews66.MK (K n : ℕ) : ℝ := √48 / (√K * √(24 * (n : ℝ) - 1)) * Real.sinh (π * √(24 * (n : ℝ) - 1) / (6 * K))
-- the Kloosterman sum of the canonical multiplier ω_b of b at h/2k
def Andrews66.Ab (k n : ℕ) : ℂ := ∑ h ∈ (Finset.range (2 * k)).filter (fun h => Nat.Coprime h (2 * k)),
    omegaB h (2 * k / 2) * cexp (-(2 * π * I * n * h / ((2 * k : ℕ) : ℂ)))
def Andrews66.andrewsMain (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 (Nat.sqrt n / 2), (-1) ^ k * Ab k n * MK (2 * k) n

theorem Andrews66.andrews_1966_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(Dragonette.α n : ℂ) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt n / 2), (-1) ^ k * Ab k n * MK (2 * k) n‖ ≤
        A₁ * ((Nat.sqrt n : ℝ) ^ (2 * D - 1) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n
theorem Andrews66.andrews_1966_isBigO_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : 1 ≤ D) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (D - 1 / 2) * (1 + Real.log n))
theorem Andrews66.andrews_1966_sqrt_log_of_Hb {C D : ℝ} (hHb : Hb C D) (hC : 0 ≤ C) (hD : D ≤ 1) :
    (fun n : ℕ => (Dragonette.α n : ℂ) - andrewsMain n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n))
-- the multiplier, explicitly (s = Rademacher.dsum, Dedekind sum)
theorem Andrews66.omegaB_eq_dsum {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) :
    omegaB h k = cexp (π * I * (2 * Rademacher.dsum h k - 3 * Rademacher.dsum h (2 * k)))
theorem Andrews66.Ab_eq_dedekind {k : ℕ} (hk : 0 < k) (n : ℕ) : Ab k n = ∑ h ∈ …, cexp (π * I * (2 s(h,k) − 3 s(h,2k)) − 2πinh/(2k))
```

The constants are explicit in the proof: `A₁ = 2e^{8π}C` and `A₂ = 2e^{8π}(C_b + e^{π/3}) + 4√10 e^{π/3+8π}`, where
`C_b` comes from `bE_near`. They are not optimized.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem in parts I and II. There is no
`sorry`, no `native_decide` and no new axiom. `Hb` is a `def` and enters only as a hypothesis.

### Proof architecture, part II (the full sum)

1. **The coefficient integral on a line** (`Circle.coeff_line`): `∫_{x₀}^{x₀+1} f(e^{2πiτ})e^{−2πinτ}dx = α(n)` for
   `τ = x + iy`, `y > 0`.
2. **Farey dissection of order `N = ⌊√n⌋` on `Im τ = 1/N²`** (`Circle.farey_line`, `arcs_approx`). The arc of
   `h/k` is `[h/k − 1/(k(k+k_p)), h/k + 1/(k(k+k_n))]`, and neighbouring arcs meet at mediants (`Rend_eq_Lend`).
   The arcs of `F_N` tile `[−1/(N+1), N/(N+1)]`. This reuses `Rademacher.Farey` and `fareyList`/`Frac` from
   `Rademacher/Assembly`.
3. **Per arc** (`Arc.arc_bound`). Put `τ = h/K + φ + iy` and `z = K(y − iφ)`. Then
   - `Re(1/z) ≥ K/2` on the arc, so `Hb` applies;
   - `|b(q') − 1| ≤ C_b|q'|` with `|q'| = e^{−2πRe(1/z)/K} ≤ e^{−π}` (`bE_near`, via `dslope`);
   - so `f(q)e^{−2πinτ} = e^{−2πinh/K}[ε_K ω_b m(φ) + O(e^{8π}(C‖z‖^{−D} + C_b‖z‖^{−1/2}))]` (`pt_bound`), where
     `m(φ) = z^{−1/2}e^{π(1/z−z)/(12K)}e^{2πnz/K}`;
   - off the symmetric core `|φ| ≤ θ₀ = 1/(2KN)`, `Re(1/z) ≤ 4K`, so `|m| ≤ e^{8π+π/3}‖z‖^{−1/2}` (`mI_off`).
4. **The core** (`ArcMain.core_eval`, generalizing part I's `MainArc`/`Main` from `K = 2` to every `K`).
   - The substitution `ζ = π/(12Kz)` gives `m dφ = (√β/(iK)) h(ζ)dζ` with `h(ζ) = ζ^{−3/2}e^{ζ+Y/ζ}`,
     `β = π/(12K)` and `Y = π²(24n−1)/(144K²)` (`mI_eq`).
   - The arc becomes its chord `Re ζ = c`, using a primitive on the disc `|ζ − A| < A − c/4` (`core_chord`).
   - Completing the chord to the full line costs `≤ 4e^{c+Yc/(c²+s²)}/√s` (`tail_bound'`), with `c ≤ π/3`,
     `s ≥ 1/10` and `Yc/(c²+s²) = 2π(n − 1/24)y ≤ 8π`.
   - The full line is `bessel_line` with closed form `tsum_bco`, which gives `M_K(n)` (`MK_const`).
5. **The multiplier** (`BNear.omegaB`, `OmegaB.omegaB_eq_dsum`). It is canonical: the `Classical.choose` of
   `IsMultB` is unique and independent of `h'`. It equals `ω_{h,k}²/ω_{h,2k}³` in terms of the canonical
   `η`-multipliers, and hence `e^{πi(2s(h,k)−3s(h,2k))}` by `Rademacher.omega_eq_dsum`.
6. **Summation** (`Final`).
   - Each `K ≤ N` contributes `K·Barc ≤ 2e^{8π}C N^{2D−1}/K + A₂`, using `(K/N²)^{−D} ≤ N^{2D}/K` for `D ≥ 1`
     and `e^{2πn/N²} ≤ e^{8π}`.
   - The harmonic sum gives `N^{2D−1}(1 + log N)`.
   - Odd `K` have `ε_K = 0`. `main_reindex` turns the sum over even `K = 2k ≤ N` into the sum over `k ≤ N/2`.

**On `k ≤ √n/2` versus Andrews' `k ≤ √n`.** The terms with `√n/2 < k ≤ √n` have
`π√(24n−1)/(12k) ≤ 2.6`. So they total `O(√n)` and lie inside the error. Our sum is Andrews' sum up to his error
term.

### Numerical check of the conditional theorem (`numerics/mainsum2.py`, `mainsum2.txt`)

- `α(n)` is computed exactly for `n ≤ 2000` by power-series arithmetic.
- `andrewsMain(n)` is computed in 60-digit arithmetic. It uses the Dedekind-sum form of the Kloosterman sum and
  the identification (now proved, `Ab_printed`).
- Result: `max_{n ≤ 2000} |α(n) − andrewsMain(n)| = 3.0`, attained at `n = 3`, where `N = 1` and the sum is empty.
  For `n ≥ 10` all errors are `< 1.8`. The sizes are `α(2000) ≈ −9.1·10²²` and error `0.11`. So the theorem's
  `O(√n log n)` is far from sharp, as expected (Ahlgren–Dunn).
- `numerics/mainsum.py` computes `ω_b` independently, directly from the function `b` in double precision:
  - `||ω_b| − 1| ≤ 6·10⁻¹⁴`;
  - `(−1)^k A_b(k,n) = (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4)` to `2·10⁻¹³`, for all `k ≤ 22` and all `n < 60`.
    This covers all residues mod `2k`.
- `numerics/ded.py` checks the underlying termwise congruence
  `2s(h,k) − 4s(h,2k) + k ≡ ⌊(k+1)/2⌋ + h(1+(−1)^k)/4 (mod 2)` exactly, in rationals, for all 663 pairs `(h,k)`
  with `k ≤ 40`, `h` coprime to `2k`.

---

# Part I: the k = 1 term with a power saving, and the cusp transformations of b

## Headline results (Lean, axiom-clean)

Directory: `RamanujanTau/Andrews66/`. For every theorem below, `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `native_decide` and no new axiom.

```lean
-- Andrews' k = 1 term:  √24/√(24n−1) · sinh(π√(24n−1)/12)  =  π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/12)
def Andrews66.M1 (n : ℕ) : ℝ := √24 / √(24 * (n : ℝ) - 1) * Real.sinh (π * √(24 * (n : ℝ) - 1) / 12)

theorem Andrews66.andrews_k1_isBigO :
    (fun n : ℕ => (Dragonette.α n : ℝ) - (-1) ^ (n + 1) * M1 n) =O[atTop]
      (fun n : ℕ => Real.exp (π * √((n : ℝ) / 6) - √(24 * (n : ℝ)) / (2450 * π)))

theorem Andrews66.andrews_k1_bound {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) :
    |(α n : ℝ) - (-1) ^ (n + 1) * M1 n| ≤
      Err (1 / tD n) / KD n + √(π * aa) * (4 * Real.exp (3 / 2 * AD n) / √(AD n / 2)) / (2 * π)

-- M-a (first half): b = F(q²)²/F(q)³ at every cusp, with q = qp h k z = e^{2πi(h+iz)/k}, Re z > 0
theorem Andrews66.b_transform_even {h h' : ℤ} {k : ℕ} (hk : 0 < k) (hdvd : ((2 * k : ℕ) : ℤ) ∣ h * h' + 1) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ z : ℂ, 0 < z.re →
      bE (qp h (2 * k) z) = ω / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) * bE (qp h' (2 * k) (1 / z))
theorem Andrews66.b_transform_odd {h h' h₂ : ℤ} {k : ℕ} (hk : 0 < k) (hd1 : (k : ℤ) ∣ h * h' + 1)
    (hd2 : (k : ℤ) ∣ (2 * h) * h₂ + 1) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ z : ℂ, 0 < z.re →
      bE (qp h k z) = ω * (2 / Complex.sqrt z) * cexp (-(π * (2 / z + z) / (12 * k))) *
        (F (qp h₂ k (1 / (2 * z))) ^ 2 / F (qp h' k (1 / z)) ^ 3)
```

**The power saving.** The main term is `≍ e^{π√(n/6)}/√n`. The error exponent `π√(n/6) − √(24n)/(2450π)`
equals `(1 − 12/(2450π²))·π√(n/6) ≈ (1 − 1/2015)·π√(n/6)`, so the error is `O(main^{1−δ})` with
`δ ≈ 1/2015`. This is the "power saving over the leading exponential" that the brief allows. The saving
comes from Dragonette's uniform bound on φ (`Dragonette.phi_bound`, rate `e^{−1/(2400t)}`); the other errors
are much smaller. Andrews' theorem has the optimal `δ = 1/2` minus logs: its next term, `k = 2`, has size
`e^{π√(n/6)/2}`.

**Sanity check** (exact `α(n)` by power-series arithmetic, Python, n ≤ 400). The values of
`α(n) − (−1)^{n+1}M1(n)` are:

| n | α(n) − (−1)^{n+1}M1(n) | e^{π√(24n−1)/24}, the size of the k = 2 term |
|---|---|---|
| 10 | −0.93 | 7.6 |
| 100 | 12.9 | 609 |
| 200 | 167 | 8674 |
| 400 | 4864 | 3.7·10⁵ |

The normalization of the `k = 1` term is therefore correct. The true remainder is the `k ≥ 2` terms, as
Andrews' theorem predicts.

## Proof architecture

1. **Dragonette's decomposition is reused unchanged** (`Dragonette.decomp_D`). It is the circle method at `q = −1`
   with `z = t + iθ` and `t = π/√(24n)`:
   - Watson's `f = 2φ(−q) − b`;
   - the transformation of `b` at `−1`;
   - the uniform φ bound;
   - the minor-arc bound for `(−s;s²)_∞`.

   It gives `2π(−1)^{n+1}α(n) = ∫_{−t}^{t} M(θ)dθ + R` with `‖R‖ ≤ 2π·Err(1/t)/K_n`, where
   `M = (z/π)^{−1/2} e^{π²/(24z) − z/24 + nz}`. Dragonette only evaluated `∫M` asymptotically, by Laplace's
   method; the new work is an exact evaluation.
2. **Substitution `ζ = a/z`, `a = π²/24`** (`MainArc.MD_eq`). This gives `M(θ)dθ = i√(πa)·h(ζ)dζ`, where
   `h(ζ) = ζ^{−3/2}e^{ζ+Y/ζ}` and `Y = a(n−1/24)`. The segment becomes an arc of `|ζ − A/2| = A/2`.
3. **Arc → chord** (`MainArc.major_chord`). Mathlib's `DifferentiableOn.isExactOn_ball` gives a primitive of `h`
   on the disc `|ζ − 3A/4| < 3A/5`, which lies in `Re ζ > 0` and contains both the arc and the chord
   `Re ζ = A/2, |Im ζ| ≤ A/2`. The two path integrals are then compared using
   `Rademacher.integral_eq_of_primitive`. The result is `∫_{−t}^{t}M = √(πa)∫_{−A/2}^{A/2} h(A/2 + iv)dv`.
4. **Chord → full line** (`Main.tail_bound`). For `|v| ≥ c`, `|h(c+iv)| ≤ |v|^{−3/2}e^{c+Y/(2c)}`, and
   `Y/(2c) = (n−1/24)t ≤ A`. So the two tails cost at most `4e^{3A/2}/√c`.
5. **The full line is the order-3/2 Bessel integral** (`Bessel.bessel_line`). This is a copy of
   `Rademacher/Bessel.lean` with `5/2 → 3/2`. The only real change is that `Γ(m+3/2) ≥ 1/2` replaces
   `Γ(m+5/2) ≥ 1`. The proof uses the Laplace transform plus Fourier inversion. The closed form
   (`Bessel.tsum_bco`) is `Σ y^m/(m!Γ(m+3/2)) = 2 sinh(2√y)/(√π·2√y)`.
6. **Constants** (`Main.main_const`): `√(πa)·2sinh(x)/(√π x) = √24 sinh(x)/√(24n−1)` with
   `x = 2√Y = π√(24n−1)/12`.
7. **Assembly** (`andrews_k1_bound`, then `andrews_k1_isBigO`). The proof uses `Err(u) ≤ KE·u²e^{−u/2400}`
   for `u ≥ 1` (`Err_le`).

Remarks:
- The `w = 1/z` line gives `I_{1/2}`, i.e. sinh, exactly as in Andrews. The `z`-line would give `I_{−1/2}`,
  i.e. cosh, which differs from it by `O(1)`.
- No contour deformation with branch cuts and no Hankel contour is needed. The only complex analysis is the
  primitive on a disc.

### Files

| file | lines | content |
|---|---|---|
| `Andrews66/Bessel.lean` | 366 | order-3/2 Bessel line integral and closed form (`bessel_line`, `tsum_bco`, `Gamma_m32`) |
| `Andrews66/MainArc.lean` | 249 | `ζ = a/z` substitution (`MD_eq`), disc membership, `major_chord` |
| `Andrews66/Main.lean` | 367 | line tails, `major_eval`, `M1`, `andrews_k1_bound`, `Err_le`, `andrews_k1_isBigO` |
| `Andrews66/Cusps.lean` | 144 | `bE`, `b_transform_even`, `b_transform_odd` (M-a, first half) |
| `Andrews66/BNear.lean` | 125 | `bE_near` (`b = 1 + O(q)`); canonical multiplier `omegaB`/`IsMultB`/`omegaB_spec`; `epsK`, **`Hb`** |
| `Andrews66/Circle.lean` | 235 | `coeff_line`; Farey arcs on a line, `farey_line`, `arcs_approx` |
| `Andrews66/ArcMain.lean` | 375 | general-`K` core: `mI`, `mI_eq`, `core_chord`, `tail_bound'`, `MK`, `core_eval` |
| `Andrews66/Arc.lean` | 516 | per-arc analysis: `pt_bound`, `b_main_pt`, `mI_off`, geometry, `Barc`, `arc_bound` |
| `Andrews66/Final.lean` | 272 | `Ab`, `MK_two`, summation, `main_reindex`, **`andrews_1966_of_Hb`**, `andrews_1966_isBigO_of_Hb` |
| `Andrews66/OmegaB.lean` | ~140 | `omegaB_eq_dsum`, `Ab_eq_dedekind`, `Hb_mono`, `andrews_1966_sqrt_log_of_Hb` |
| `Andrews66/Ded.lean` | 214 | `Tq`, `Uq`, `Gq`, `TU`, `T_step`, `G_step`, **`T_cong`** (the Dedekind-sum congruence) |
| `Andrews66/Printed.lean` | 245 | `AAnd`, `AAnd_nat`, `shiftA`, `term_eq`, **`Ab_printed`**, `extra_term_le`, **`andrews_1966_printed_of_Hb`**, `andrews_1966_printed_isBigO_of_Hb` |
| `Andrews66/numerics/` | — | `hb2.py`/`hb3.py` (+ outputs): `Hb` check; `mainsum*.py`: main sum vs α(n) and the identification; `ded.py`: the congruence |

Each file was compiled with `lake env lean` and `lake build RamanujanTau.Andrews66.<File>`. Nothing outside
`Andrews66/` was modified apart from this document. Both
`RamanujanTau.Andrews66.Main` and `RamanujanTau.Andrews66.Printed` have since been added to the root import. `Printed` imports
`Ded`, `OmegaB` and `Final`, which import everything else.

## Evidence levels

1. **Lean, axiom-clean (unconditional).**
   - `andrews_k1_isBigO` and `andrews_k1_bound`: the `k = 1` term with a power saving.
   - `b_transform_even` and `b_transform_odd`.
   - `omegaB_eq_dsum`, `Ab_eq_dedekind`: the multiplier of `b` in Dedekind sums.
   - `T_cong`, `Ab_printed`: Andrews' sign `(−1)^{⌊(k+1)/2⌋}` and shift `n − k(1+(−1)^k)/4`.
   - `core_eval`: the exact Bessel evaluation of every major-arc core.
   - `coeff_line`, `farey_line`: the circle method on a line.
   - `bE_near`.
2. **Lean, conditional on the named hypothesis `Hb C D`.**
   - `andrews_1966_of_Hb` (explicit, every `n ≥ 1`).
   - `andrews_1966_isBigO_of_Hb`.
   - `andrews_1966_sqrt_log_of_Hb`: `O(√n log n)` when `D ≤ 1`.
   - **`andrews_1966_printed_of_Hb`** and `andrews_1966_printed_isBigO_of_Hb`: Andrews' printed sum over `k ≤ √n`.
   - `arc_bound`: the per-arc bound.
3. **Paper only.**
   - The truth of `Hb`. It is a consequence of the general-cusp transformation of `f` (Watson 1936; Andrews 1966,
     §§3–4; Gordon–McIntosh), but that is not formalized. (Superseded: `Hb` is now proved in Lean by a different
     route, `MockCusp.Hb_holds` / `MockCusp.HbSharp_holds`.)
4. **Numerical.**
   - `Hb(3,1)` and `Hb(3,1/2)` at 772 points.
   - The termwise Dedekind congruence for `k ≤ 40`, now proved for all `k`.
   - `|α(n) − andrewsMain(n)| ≤ 3` and `|α(n) − andrewsPrinted(n)| ≤ 0.65` for all `n ≤ 2000`.
   - The table in Part I.

## What was left (historical; `Hb` is now proved, see the status note at the top)

- **M-b, discharging `Hb`.** This is the hard part, estimated at 3–6k lines. It needs a transformation law for `f`
  at every cusp `h/K`, at least up to a polynomially bounded remainder:
  - at even `K`, `f(q) = (−1)^{K/2}b(q) + O(|z|^{−D})`;
  - at odd `K`, `f(q) = O(|z|^{−D})`;
  both uniformly in `h`, `K` and the disc `Re(1/z) ≥ K/2`.

  Routes:
  - **(a)** Watson's 1936 transformation of `f` and `ω` under the full modular group, through the third-order
    mock theta "vector" `(f, ω, …)` plus Mordell integrals. The repo has the Watson identities at `q → ±1`,
    Appell–Lerch sums (`RankAL`, `ALBase`) and the `η`-machinery.
  - **(b)** Zwegers: `q^{−1/24}f(q)` is a component of a vector-valued harmonic Maass form of weight 1/2. `Hb`
    then follows from the boundedness of the non-holomorphic Eichler integral of a unary theta series on the
    region `Re(1/z) ≥ K/2`.

  Only the crude bound is needed, not the exact law.
- The sign/shift identification and the range `k ≤ √n` are **done** (`Ded.lean`, `Printed.lean`).

**Estimate to finish.**
- Only `Hb` remains: weeks. It is the formal general-cusp modularity of a mock theta function, the same wall as `docs/ANDREWS_1966.md` G2.

## Literature

- Andrews, *Amer. J. Math.* 88 (1966) 454–490 (the `O(√n log n)` theorem).
- Dragonette, *Trans. AMS* 72 (1952).
- Bringmann–Ono, *Invent. Math.* 165 (2006) (the exact formula).
- Ahlgren–Dunn (2019), convergence and error terms.

The `k = 1`-only statement with a power saving is implied by any of these. It is formalized here, but it is
not new mathematics.
