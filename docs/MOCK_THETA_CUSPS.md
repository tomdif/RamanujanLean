# Mock theta cusps: the bound `Hb` behind Andrews 1966

Target (fixed by `RamanujanTau/Andrews66/BNear.lean`):

```lean
def Andrews66.Hb (C D : ℝ) : Prop := ∀ K : ℕ, 0 < K → ∀ h : ℕ, Nat.Coprime h K → ∀ z : ℂ, 0 < z.re →
  (K:ℝ)/2 ≤ (1/z).re → ‖fA (qp h K z) - epsK K * bE (qp h K z)‖ ≤ C * ‖z‖ ^ (-D)
```

Here `q = qp h K z = e^{2πi(h+iz)/K}`. The sign is `ε_K = (−1)^{K/2}` for even `K` and `0` for odd `K`. The
function `b` is `(q;q)³/(q²;q²)²`.

## Status

**`Andrews66.Hb Csharp 1` is proved in Lean, axiom-clean, at every cusp** (`MockCusp.HbSharp_holds`, 2026-11-04).
Hence **Andrews' 1966 theorem holds unconditionally with his sharp error `O(√n log n)`**
(`MockCusp.andrews_1966_sqrt_log_unconditional`, via `Andrews66.andrews_1966_printed_isBigO_of_Hb`).
The earlier `Hb (max Ceven Codd) (3/2)` (`MockCusp.Hb_holds`, error `O(n log n)`) is kept unchanged.

```lean
theorem MockCusp.HbSharp_holds : Andrews66.Hb Csharp 1
-- Csharp = max (max (4·CphiS) (4·CpsiS + 4)) CoddS, explicit (SharpHb.lean)
theorem MockCusp.andrews_1966_sqrt_log_unconditional :
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsPrinted n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n))
theorem MockCusp.andrews_1966_sqrt_log_main_unconditional :   -- same, with Andrews66.andrewsMain
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n))
```

Previous statements (D = 3/2):

```lean
theorem MockCusp.Hb_holds : Andrews66.Hb (max Ceven Codd) (3 / 2)
-- Ceven = 2592(1+C₀) + 4,  Codd = 216(1+C₀)
theorem MockCusp.andrews_1966_unconditional :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(Dragonette.α n : ℂ) - Andrews66.andrewsPrinted n‖ ≤
        A₁ * ((Nat.sqrt n : ℝ) ^ (2 : ℝ) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n
theorem MockCusp.andrews_1966_isBigO_unconditional :
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ) * (1 + Real.log n))
```

### Lean theorems, D = 3/2 (directory `RamanujanTau/MockCusp/`, 1443 + 1431 lines)

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem in this table. There is no
`sorry`, no `native_decide` and no new axiom.

| theorem | file | statement |
|---|---|---|
| `integral_shift` | Strip | `∫_ℝ G = ∫_ℝ G(·+ci)` for `G` holomorphic on the strip, with decay on its vertical edges and integrable on both lines |
| `norm_one_sub_exp_ge` | Denom | if `v` is at distance `≥ r` from `2πiℤ`, then `‖1 − e^v‖ ≥ min(1,r)/3` |
| `fourier_kern_le` | Kernel | **Mordell-integral bound** for one residue-class kernel `e^{iπX−α(A(ρ+TX)²+B(ρ+TX))}/(1−w e^{−α(D(ρ+TX)+E)})`: shift to `Im X = y`, then integrate the Gaussian modulus explicitly |
| `class_sum` | ALSum | Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`) for one class, with the bound `M/sinh(πy₀)` |
| `al_sum_le` | ALSum | **Key lemma.** For anti-periodic `c(n+T) = −c(n)` (with `‖c‖ ≤ 1`), periodic `ω`, and denominators `≥ m` on the strip `\|Im U\| ≤ Y₀`: `‖Σ_ℤ c(n)e^{−α(An²+Bn)}/(1−ω(n)e^{−α(Dn+E)})‖ ≤ (1/m)√(π/(A Re α)) e^{AY₀²\|α\|²/Re α + B²Re α/(4A)} / sinh(πY₀/T)` |
| `al_sum_cusp` | GenCusp | the key lemma at the optimal shift `Y₀ = π Re(1/α)/(2TA)`, with the pole geometry: if `ω = e^{iθ}` and `\|θ − 2πk\| ≥ δ > πD/(2TA)`, the bound is `≍ e^{−π²Re(1/α)/(4AT²)}` |
| `f_AL` | FAL | **Appell–Lerch form of `f` on the disc**: `f(q)(q;q)_∞ = 1 + 4Σ_{m≥1}(−1)^m q^{m(3m+1)/2}/(1+q^m)`. This is `RankProof.rank_AL` at `z = −1`, transferred by Taylor series |
| `F_bound` | OddCusp | `‖1/(q;q)_∞‖ ≤ (1+C₀)\|z\|^{1/2} e^{π Re(1/z)/(12K)}` at every cusp, from `Rademacher.F_transform` |
| `f_odd_bound` | OddCusp | **odd `K`**: `‖f(e^{2πi(h+iz)/K})‖ ≤ 216(1+C₀)\|z\|^{−3/2}` whenever `Re(1/z) ≥ K/2` |
| `Hb_odd` | Hb | the odd half of `Andrews66.Hb`, in its exact form |
| `Hb_of_even` | Hb | `HbEven C (3/2) → Andrews66.Hb (max C Codd) (3/2)` |
| `bA_eq_bE` | BAE | **`b = (q;q²)_∞ϑ₄(q) = (q;q)³_∞/(q²;q²)²_∞` on the disc**. Formal input: Gauss's `ϑ₄ = (q;q²)²_∞(q²;q²)_∞`, which is `RankProof.jtp_ab 2 1`; `Θ_eq_thetaS` matches the two theta series |
| `T_scale` | RankDisc | Taylor series commute with rescaling: `T(u ↦ F(ρu)) = rescale ρ (T F)` for `\|ρ\| ≤ 1` |
| `rank_disc` | RankDisc | **analytic rank Appell–Lerch identity** for every `z ≠ 0` and `\|Q\| < min(\|z\|, 1/\|z\|)`: `(Q;Q)_∞ Σ Q^{n²}/((zQ)_n(Q/z)_n) = 1 + Σ_{r≥1}(−1)^r Q^{r(3r+1)/2}(1+Q^r)(1−z)(1−z⁻¹)/((1−zQ^r)(1−Q^r/z))`. Transfer of the formal `rank_AL` (constant `z`) on the rescaled disc `u = Q/ρ`, so that `z` may later be a power of `Q` |
| `Ad_bilateral` | Bilateral | the right side equals `(1−z)Σ_{n∈ℤ}(−1)ⁿQ^{n(3n+1)/2}/(1 − zQⁿ)` (`Q = e^L`), given summability and no vanishing denominator |
| `phi_odd_bound` | PhiCusp | **φ at odd `K`**: `‖φ(q)‖ ≤ 432(1+C₀)\|z\|^{−3/2}`, `φ = R(i;·)`; parameters `(A,B,D,T,δ) = (3/2,1/2,1,K,π/(2K))` |
| `watson_disc2` | PsiAL | **`f(q) + 4ψ(−q) = b(q)` on the disc** (`Watson3.watson_W2`, Taylor transfer); `aA = ψ(−·) + 1` |
| `aA_rank` | PsiAL | **`(1−Q)(ψ(Q)+1) = R(Q;Q⁴)`**, `Q = −q`: the terms `2m, 2m+1` of `ψ` pair to the `m`-th rank term |
| `aA_eq_F` | PsiCusp | `ψ(Q)+1 = F(Q⁴) Σ_{n∈ℤ}(−1)ⁿQ^{6n²+2n}/(1−Q^{4n+1})` (from `aA_rank`, `rank_disc` at `z = Q`, base `Q⁴`, `Ad_bilateral`). This is the Watson/Appell–Lerch form of ψ, obtained without any new formal identity |
| `aA_cusp_bound` | PsiCusp | **`K = 4T`**: `‖ψ(−q)+1‖ ≤ 216(1+C₀)\|z\|^{−3/2}`; parameters `(A,B,D,E,T,δ) = (6,2,4,1,K/4,2π/K)` |
| `Hb_two_mod_four` | HbFull | `K ≡ 2 (4)`: `‖f + b‖ = 2‖φ(−q)‖ ≤ 2592(1+C₀)\|z\|^{−3/2}`; `−q = qp((h+K/2)/2, K/2, z/2)` is an odd cusp |
| `Hb_zero_mod_four` | HbFull | `K ≡ 0 (4)`: `‖f − b‖ = 4‖ψ(−q)‖ ≤ (864(1+C₀)+4)\|z\|^{−3/2}` |
| `HbEven_holds`, `Hb_holds` | HbFull | `HbEven Ceven (3/2)`, `Andrews66.Hb (max Ceven Codd) (3/2)` |
| **`andrews_1966_unconditional`** | HbFull | `Andrews66.andrews_1966_printed_of_Hb Hb_holds`: Andrews' printed sum, error `A₁N²(1+log N) + A₂N` |
| `andrews_1966_isBigO_unconditional` | HbFull | `α(n) − andrewsMain(n) = O(n(1 + log n))` |

The ψ Appell–Lerch identity, flagged previously as "the one genuinely new formal input", turned out not to need a
new formal proof: `ψ(Q) + 1 = R(Q;Q⁴)/(1−Q)` is a termwise pairing, and the rank identity is used at `z = Q`
analytically (`rank_disc` allows `|z| < 1`, on the disc `|Q⁴| < |Q|`).

## The proof (all cusps)

**Mechanism.** Write a third-order mock theta function as `S(q)/η-quotient`, where `S` is a level-3
Appell–Lerch sum.
- At the cusp `h/K`, put `q = ζe^{−α}` with `α = 2πz/K`. The coefficient sequence of `S` is then
  **anti-periodic**: `c(n+T) = −c(n)`.
- After Poisson summation in each residue class, the dual frequencies are `(ℓ − ½)/T`. They are never 0.
- The smallest frequency `1/(2T)` gives a Gaussian factor `e^{−π² Re(1/α)/(4AT²)}`. This is **exactly** the
  growth rate of the inverse eta quotient at that cusp.
- What remains is polynomial in `1/|z|`. It comes from the Gaussian width `√(1/Re α)`, the denominator lower
  bound `1/m`, and `|z|^{1/2}` from the eta transformation.
- The only condition is that **no denominator vanishes at the root of unity**. That is the separation
  `δ > πD/(2TA)`.

No exact transformation law of `f` is needed, so there are no Mordell-integral identities, no `μ`-function
and no Kloosterman sums: inequalities suffice. The cancellation `f − ε_K b` is built into Watson's
identities, which turn each even cusp into an odd-type cusp of another mock theta function:

| cusp class | function | Appell–Lerch form | parameters `(A, D, T, δ)` | gap `δ − πD/(2TA)` |
|---|---|---|---|---|
| `K` odd | `f(q)` | `(q;q)f = 2Σ(−1)ⁿq^{n(3n+1)/2}/(1+qⁿ)` | `(3/2, 1, K, π/K)` | `2π/(3K)` |
| `K ≡ 2 (4)` | `f+b = 2φ(−q)`; `Q=−q` has odd order `K/2` | `(Q;Q)φ(Q) = (1−i)Σ(−1)ⁿQ^{n(3n+1)/2}/(1−iQⁿ)` (Lean form: one sum, `ω = iζⁿ`, `R(i;Q)` via `rank_disc`) | `(3/2, 1, K/2, π/K)` | `π/(3K)` |
| `K ≡ 0 (4)` | `f−b = −4ψ(−q)`; `Q=−q` has order `K` | `(Q⁴;Q⁴)(ψ(Q)+1) = Σ(−1)ⁿQ^{6n²+2n}/(1−Q^{4n+1})` (Lean form; equivalently `(Q⁴;Q⁴)ψ = Σ(−1)ⁿQ^{6n²+6n+1}/(1−Q^{4n+1})`) | `(6, 4, K/4, 2π/K)` | `2π/(3K)` |

In every row:
- The decay exponent `π² Re(1/α)/(4AT²)` equals the growth exponent of the eta quotient at that cusp:
  `π Re(1/z)/(12K)`, `π Re(1/z)/(3K)` and `π Re(1/z)/(3K)` respectively.
- The anti-periodicity is a sign computation. For `f`: `c(n+K)/c(n) = (−1)^K(−1)^{h(3K+1)} = −1`.
  For `ψ` (Lean form, `h₀ = h + K/2` odd): `c(n+T)/c(n) = (−1)^T(−1)^{h₀(3T+1)} = −1`, `T = K/4` (`cP_anti`).

For the `K ≡ 2 (4)` row, `Q = qp((h+K/2)/2, K/2, z/2)`, so `α` is unchanged and `Re(1/z') = 2Re(1/z) ≥ K/2`.
For the `K ≡ 0 (4)` row, the eta factor is `F(Q⁴) = F(qp(h+K/2, K/4, z))`.

## The sharp bound `D = 1` (files `BadSet`, `SharpALSum`, `SharpCusp`, `SharpOdd`, `SharpPsi`, `SharpHb`; 1774 lines)

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem below; no `sorry`, no
`native_decide`, no new axiom. The existing MockCusp files are unchanged; the new files reuse them.

**Why the write-up's sketch was not enough.** Integrating `1/|1 − ωe^{…}|` against the Gaussian *inside one class*
gives `log(1/|z|)/|α|` per class, i.e. `(K/|z|)·log` after the `T ≍ K` classes, which is **not** uniform in `K`
(at `|z| ≍ 1/K` it is no better than `|z|^{−2}`). Two gains are needed together:
1. **along the line**: the line `Im X = y` passes close to a pole only on a short interval (the *bad set*);
2. **across the classes**: the worst separation `δ ≍ 1/K` occurs for O(1) classes only; the separations of the
   `T` classes are `(π/K')·min(r, M − r)` for an *injective* residue map `ρ ↦ r`, so `Σ_ρ δ_ρ^{−1/2} ≲ K`
   (instead of `T·√K`).

With the `m^{−1/2}` dependence from (1) the per-class bound is `≍ √(W/(Re α · D · g_ρ))`, `W = √(π/(A Re α))`,
and (2) sums it to `(Re α)^{−3/4} ≲ |z|^{−3/2}` (since `Re α ≥ π|z|²`). With the eta factor `|z|^{1/2}` this is
`|z|^{−1}`: exactly `D = 1`, with no log loss.

| theorem | file | statement |
|---|---|---|
| `gauss_union_le` | BadSet | `∫_{⋃_k (τ₀+ks−ℓ, τ₀+ks+ℓ)} e^{−P(x−x₀)²} ≤ 2ℓ(1 + 32/(Ps²))` for `4ℓ ≤ \|s\|` (lintegral union bound + two-sided geometric series) |
| `bad_integral_le` | BadSet | **non-uniform denominator bound**: if `\|1−e^{v₀+βx}\| ≥ m` on `ℝ`, `0<η≤1`, then `∫ e^{−P(x−x₀)²}/\|1−e^{v₀+βx}\| ≤ (3/η)√(π/P) + (1/m)(2η/\|β\|)(1 + 16\|β\|²/(π²P))`. Off the bad set `{∃k: \|v−2πik\|<η}` use `norm_one_sub_exp_ge`; on it use `m`. If `\|Im β\| ≤ \|Re β\|` the bad set is one interval; otherwise it lies on a progression of spacing `2π Im β/\|β\|²` |
| `opt_eta` | BadSet | `min_{0<η≤1}(a/η + bη) ≤ 2a + 2√(ab)` |
| `fourier_kern_le'` | SharpALSum | `\|𝓕kern(ξ)\| ≤ e^{kC(y)+2πξy} ∫ e^{−P(x−x₀)²}/\|kD(x+iy)\|` (denominator kept inside) |
| `kern_sharp` | SharpALSum | `\|𝓕kern(ξ)\| ≤ e^{kC(y)+2πξy}·Jb`, `Jb = 2a+2√(ab)`, `a = 3√(π/P)`, `b = (2/(m\|α\|DT))(1+16(\|α\|DT)²/(π²P))` |
| `class_sum'`, `al_sum_le'` | SharpALSum | the key lemma with a **per-class** denominator bound `m(ρ)`: `\|S\| ≤ e^{AY₀²\|α\|²/Re α + B²Re α/(4A)} (Σ_{ρ<T} Jb(m ρ)) / sinh(πY₀/T)` |
| `al_sum_cusp'` | SharpCusp | the same at `Y₀ = πRe(1/α)/(2TA)`, per-class separations `δ(ρ) > πD/(2TA)` |
| `Jb_le`, `sumJb_le` | SharpCusp | `Σ_ρ Jb ≤ (6√2 + 2√(18(1+N₁)c₁/D) + 2√(18(1+N₁)c₂/D)·G₀)/(Z√Z)` given `W ≤ 1/Z`, `Z ≤ 2`, `16\|α\|²D²/(π²A Re α) ≤ N₁`, `Z² ≤ c₁\|α\|`, `Z² ≤ c₂ Re α`, `Σ_ρ g_ρ^{−1/2} ≤ G₀T` |
| `class_phase_sum` | SharpCusp | `g(ρ) ≥ c·min(r(ρ), M−r(ρ))`, `r` injective into `[1,M)` ⇒ `Σ_{ρ<T} g(ρ)^{−1/2} ≤ 4√(M/c)` (`sum_inv_sqrt_le`: `Σ_{j≤M} j^{−1/2} ≤ 2√M`) |
| `f_phase_sum`, `phi_phase_sum`, `psi_phase_sum` | SharpOdd, SharpPsi | the class sums: `G₀ = 4√(3/π)`, `4√(24/π)`, `16√(3/(2π))`; residues `(K+2hρ) mod 2K`, `(K+4hρ) mod 4K`, `h₀(4ρ+1) mod K` |
| `sharp_odd_AL` | SharpOdd | the odd-cusp AL sum with any admissible phases is `≤ 3e^{c₀}/sinh(2c₀)·CstO(G₀)/(\|z\|√\|z\|)` |
| `f_odd_bound'` | SharpOdd | `\|f(q)\| ≤ 36(1+C₀)·CstO(4√(3/π))·\|z\|^{−1}` (K odd) |
| `phi_odd_bound'` | SharpOdd | `\|φ(q)\| ≤ 36(1+C₀)·CstO(4√(24/π))·\|z\|^{−1}` (K odd) |
| `aA_cusp_bound'` | SharpPsi | `\|ψ(−q)+1\| ≤ 18(1+C₀)·CstP(16√(3/(2π)))·\|z\|^{−1}` (K = 4T) |
| `Hb_two_mod_four'`, `Hb_zero_mod_four'` | SharpHb | the even cusps with `\|z\|^{−1}` |
| **`HbSharp_holds`** | SharpHb | `Andrews66.Hb Csharp 1` |
| **`andrews_1966_sqrt_log_unconditional`** | SharpHb | `α(n) − andrewsPrinted(n) = O(√n(1+log n))` |
| `andrews_1966_sqrt_log_main_unconditional` | SharpHb | the same with `andrewsMain` |

Constants: `CstO(G₀) = 6√2 + 2√(288/π) + 2√(288/π)·G₀`, `CstP(G₀) = 6√2 + 2√(90/(4π)) + 2√(90/(4π))·G₀`
(`N₁ = 15`, resp. `4`; `c₁ = c₂ = 1/π`).

## What remains

1. **Done:** items 1–3 of the previous plan (`bA = bE`; `K ≡ 2 (4)`; `K ≡ 0 (4)`). The even half is proved.
2. **Done (2026-11-04):** `D = 1` (section above). The sketch "D = 1/2 + ε" from integrating along the line alone is
   not uniform in `K`; the proof needs the per-class phase sum as well. `D < 1` (numerically `Hb(3, 1/2)` holds)
   would need a sharper treatment than the bad-set split (e.g. a genuine `log`-integral of `1/|v − 2πik|`,
   class by class); it is not needed for Andrews' `O(√n log n)`.

## Numerical evidence (level 4)

- `scripts/mockcusp/hb_check.py` uses mpmath at 40 digits. It runs over all `h/K` with `K ≤ 12`, with
  `1/z = K(1+σ)/2 + iτK`, `σ ∈ {0, 0.5, 2, 8, 30}` and `τ ∈ {0, ±1, ±3, ±10, ±30}`.
  - The maximum of `‖f − ε_K b‖/|1/z|^D` is ≤ 2.83 for D = 1/2 and ≤ 2.09 for D = 1.
  - This is consistent with the Andrews66 agent's fits `Hb(3,1)` and `Hb(3,1/2)` (K ≤ 30).
- `scripts/mockcusp/keylemma_check.py` checks the bound of `al_sum_le`/`al_sum_cusp`, with the constants
  exactly as in Lean, against the actual sum:
  - f at odd K ≤ 11: max ratio 0.152;
  - ψ at K ∈ {4, 8, 12}: 0.105;
  - both φ pieces at odd K ≤ 9: 0.155.

  It also asserts the anti-periodicity of the φ and ψ coefficients.
- `scripts/mockcusp/kernel2_check.py` (for the sharp files):
  - `bad_integral_le` against adaptive quadrature at 300 random `(P, x₀, v₀, β)` and `η ∈ {1, …, 0.01}`:
    maximum integral/bound 0.17;
  - the full sharp chain (`al_sum_cusp'` + per-class separations) against the actual sums: f (K ≤ 51) 0.019,
    ψ (K ≤ 12) 0.032, φ (K ≤ 9) 0.021;
  - the bracket `Σ_ρ Jb` times `|z|^{3/2}` stays ≤ 47 for K up to 1001 and `|Im 1/z|` up to `10⁵K`.
- `scripts/mockcusp/al_reps.py` and `psi_series.py` verify the three Appell–Lerch identities as power series.

## Evidence levels

1. **Lean, axiom-clean.** Everything in both theorem tables, in particular `HbSharp_holds` and
   `andrews_1966_sqrt_log_unconditional` (Andrews 1966 with his error `O(√n log n)`), and the earlier `Hb_holds`,
   `andrews_1966_unconditional`.
2. **Lean, conditional on named hypotheses.** None on this track.
3. **Paper proof.** Nothing beyond Lean. (`D < 1` is not attempted.)
4. **Numerical.** `Hb(3, 1/2)` and `Hb(3, 1)` at all sampled points (below).

## Literature

- G. N. Watson, *The final problem: an account of the mock theta functions*, J. London Math. Soc. 11 (1936).
  Source of the Appell–Lerch forms and of `f ± b` in terms of φ, ψ.
- G. E. Andrews, Amer. J. Math. 88 (1966). Andrews used the transformation formulas; the inequality-only
  Poisson route here avoids them.
- Gordon–McIntosh, *A survey of classical mock theta functions* (2012). Table of Appell–Lerch forms.
- Folsom–Ono–Rhoades (2013). Radial limits of `f − (−1)^k b` at even roots of unity, which is consistent with
  `ε_K`.
- Zwegers (2002), Bringmann–Ono (2006). The exact transformation laws, which are not needed here.
