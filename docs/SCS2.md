# `SCS2`: the two-sided shifted-convolution bound — analysis and milestone

Target (`HeckeAFE/Hyp.lean`), with `λ(n) = τ(n)n^{−11/2}`:

    SCS2 η B :  |S(a,b;ℓ,N)| = |Σ_{m,n ≤ N, am − bn = ℓ} λ(m)λ(n)| ≤ C (N+|ℓ|)^{1−η} (ab)^B
                for all a, b ≥ 1, ℓ ≠ 0, N.

**Status (2026-11-06).**

* **Level 1** (Lean, axiom-clean):
  * the trivial bound `SCS2 0 0`;
  * the gcd reduction;
  * the **diagonal case `a = b`** with a genuine power saving, `|S(a,a;ℓ,N)| ≪ N^{1−1/21}|ℓ|^{1/21}`.
* **Level 3** (paper, §2–§4): the coprime case `a ≠ b`.
  * The two-point method extends to it, through `Γ₀(ab)`.
  * It is **not** formalized. The cost estimate is in §4.
* **Caveat (§3):** the two-point method cannot deliver `SCS2` in the stated shape uniformly for `|ℓ| ≍ N`. Even at `a = b = 1` the saving degrades to `0` as `|ℓ| → N`. The shape that is provable is `N^{1−η}|ℓ|^{b}(ab)^B` with `b ≤ η`.

    nice -n 10 lake build RamanujanTau.SCS2.Main      # exit 0

* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/SCS2/`.

## 1. Formalized (`RamanujanTau/SCS2/Basic.lean`)

```lean
theorem abs_shiftSum2_le : ∃ A, 0 ≤ A ∧ ∀ a b ℓ N, 1 ≤ a → 1 ≤ b → |shiftSum2 a b ℓ N| ≤ A * N
theorem scs2_trivial : SCS2 0 0
theorem shiftSum2_mul_left (g a b) (hg : 1 ≤ g) (ℓ N) :
    shiftSum2 (g*a) (g*b) (g*ℓ) N = shiftSum2 a b ℓ N
theorem shiftSum2_eq_zero_of_not_dvd (a b ℓ N) (h : ¬ (gcd a b : ℤ) ∣ ℓ) : shiftSum2 a b ℓ N = 0
theorem shiftSum2_diag (a h N) (ha : 1 ≤ a) : shiftSum2 a a (a*h) N = shiftSum h (N - h)
theorem scs2_diag : ∃ C, 0 ≤ C ∧ ∀ a ℓ N, 1 ≤ a → ℓ ≠ 0 →
    |shiftSum2 a a ℓ N| ≤ C * N^(1 − 1/21) * |ℓ|^(1/21)
```

* `scs2_diag` comes from the unconditional `SCSSharp2.shiftedConvolutionBound_sharp2`, `SCS(1/21,1/21)`.
* By the gcd reduction, the general problem reduces to **coprime `a, b`**. Hence `a = b` reduces to `a = b = 1`.

## 2. The coprime case via the two-point method (paper)

Put `q = ab` (coprime) and `Ψ_{a,b}(z,w) = (z − w̄)^{12} Δ(az) conj Δ(bw)`.

* **Invariance.**
  * `Δ(az)` is a weight-12 form for `Γ₀(a)` and `Δ(bw)` one for `Γ₀(b)`.
  * For `γ ∈ Γ₀(q)` acting diagonally, `γz − γw̄ = (z − w̄)/(j(γ,z) conj j(γ,w))`. So `Ψ_{a,b}(γz,γw) = Ψ_{a,b}(z,w)`, the same cancellation as `SCSProof.Psi_smul`.
  * Only `Γ₀(q)`, not `SL₂(ℤ)`, preserves `Ψ_{a,b}`.
  * Rescaling `(Z,W) = (az, bw)` gives back an `SL₂(ℤ)`-invariant. But then the diagonal horocycle `(Z+x, W+x)` returns the *one-sided* sum `m − n = ℓ`, so the level structure is unavoidable.
* **Diagonal horocycle coefficient** (with `w = x + yζ`):

      ∫₀¹ Ψ_{a,b}(x+iy, x+yζ) e(−ℓx) dx = (y(i−ζ̄))^{12} e^{−2πℓy}·G_{a,b}(2πy(1+iζ̄)),
      G_{a,b}(W) = Σ_{n ≥ 1, a | bn+ℓ} τ((bn+ℓ)/a) τ(n) e^{−bnW},

  since `e(amx)e(−bnx)` integrates to `[am − bn = ℓ]`. The Laplace variable is `bW`, so the scale `σ ↦ bσ` costs powers of `b`.
* **Unfolding.** `P(z,w) = ½ Σ_{γ∈Γ₀(q)} f̃(γz,γw)` with the same box test function. Integrate over `F_q × ℍ`, where `F_q = ⋃_{γᵢ ∈ Γ₀(q)\SL₂(ℤ)} γᵢU`. Then `⟨Ψ, P⟩ = ∫ (coefficient) dμ` exactly as in `SCSProof.Q_eq`.
* **Bruhat.**
  * The terms of `‖P‖²` with `γ ∉ Γ∞` have `c ≡ 0 (mod q)`, so `S(ℓ,ℓ;c)` occurs only for `q | c`, `c ≤ 1/Y`.
  * Weil plus gcd gives `Σ_{c ≤ 1/Y, q|c} |S(ℓ,ℓ;c)|/c ≪ ℓ^{β} q^{−1/2} Y^{−1/2−δ}`. That is a *gain* in `q`.
* **Size of `Ψ`.**
  * `|Δ(az)| ≤ M (a y)^{−6}`, so `|Ψ_{a,b}| ≤ M²(ab)^{−6} Dh⁶`.
  * The ball measure on `F_q × ℍ` grows like `[SL₂(ℤ):Γ₀(q)] ≤ q·∏(1+1/p) ≪ q^{1+ε}`.
  * The prefactor `|y(i−ζ̄)|^{12}` is unchanged.
* **Net effect.** The pointwise bound becomes

      |G_{a,b}(σ+iv)| ≪ q^{B₀} ℓ^{b} (|2v/σ|+3) (bσ)^{−12+s},

  with the same `s = 99/1000`, `b = 1/21` and some fixed `B₀`. Roughly `B₀ ≤ 7`: `q^{1/2}` from the ball, `(ab)^{6}` from rescaling the prefactor against `(ab)^{−6}`, and `b^{12}` from the Laplace scale.
* **Tauberian / Abel step.**
  * It needs Rankin short sums along the progression `n ≡ −ℓ b̄ (mod a)`. Cauchy–Schwarz against the full Rankin sum costs at most `a^{1/2}`.
  * The Abel weight is `(mn)^{−11/2}` with `m = (bn+ℓ)/a`.
  * This yields `|S(a,b;ℓ,N)| ≪ N^{1−η} |ℓ|^{1/21} (ab)^{B}` with `η = 1/21`, `B ≈ 8`. These values are not optimized and are paper-level.

**Hecke multiplicativity does not reduce `a ≠ b` to the one-sided case.**

* Writing `λ(m)` with `am = bn + ℓ` couples `m` and `n` through a single linear equation with coprime coefficients.
* `λ(am')` factors only when `gcd(a, m') = 1`, and even then `λ(a)λ(m')` leaves the constraint `am' − bn = ℓ` intact.
* Only `a = b` (after the gcd reduction, `a = b = 1`) is literally the one-sided sum. That case is `shiftSum2_diag`.

## 3. The `|ℓ| ≍ N` obstruction (method-intrinsic)

The pointwise bound for `G_ℓ(W)` needs `ℓ·Re W ≤ 1`:

* the coefficient carries `e^{−2πℓy}`, and dividing by it costs `e^{ℓσ}`;
* so only partial sums of length `x ≥ ℓ` are reachable.

In `S(1,1;ℓ,N) = Σ_{n ≤ N−ℓ} λ(n)λ(n+ℓ)` the sum has length `N − ℓ`, so:

* for `ℓ ≥ N/2` the range is `x < ℓ`;
* the Abel step must then use Cauchy–Schwarz there, which gives `≍ N` with no saving.

Hence `SCSSharp2` has `B = η`, and `scs2_diag` has the factor `|ℓ|^{1/21}`. The same applies to general `(a,b)`.

`SCS2` in the stated shape, with `(N+|ℓ|)^{1−η}` and no `ℓ`-power, therefore needs a different input for `|ℓ| ≥ N^{1−ε}`: the spectral method (Blomer–Harcos) or the δ-method. **But for the twisted second moment it should not be needed.**

* In `∫|L(6+it)|²(h/k)^{it} w(t/T) dt`, the off-diagonal weight `ŵ(T log(am/bn))` is negligible unless `|am − bn| ≪ (a+b) N T^{−1+ε}`.
* So only `|ℓ| ≤ N^{1−θ}` occurs, with `θ > 0` fixed once `N ≍ T`.
* In that range `N^{1−η}|ℓ|^{η}(ab)^B ≤ N^{1−θη}(ab)^B`, a genuine power saving.

**Recommendation:** restate the hypothesis used by Hafner as `SCS2' η b B`:

    |S(a,b;ℓ,N)| ≤ C N^{1−η} |ℓ|^{b} (ab)^B,   b < η,

or in the restricted range `|ℓ| ≤ N^{1−θ}`. Note that `scs2_diag` has `b = η = 1/21`, so it gives a saving only for `|ℓ| ≤ N^{1−ε}`. A strict `b < η` comes from re-running the chain with `β < 2/21` in `norm_tsum_Iγ_le_gcd`, which is a parameter change.

## 4. Cost of formalizing the coprime case

| block | reuse | new |
|---|---|---|
| `Ψ_{a,b}`, invariance under `Γ₀(q)`, coefficient | `TwoPoint`/`TwoPointF` proofs verbatim with `Δ(az)` | ≈ 250 |
| fundamental domain `F_q = ⋃ γᵢU` and unfolding on `F_q × ℍ` | `Unfold2`, `Measures` | ≈ 500 (coset representatives of `Γ₀(q)\SL₂(ℤ)`, measure-zero overlaps) |
| Bruhat restricted to `q | c` | `Bruhat1–8`, `KloostGcd` (filter `c`) | ≈ 600 |
| ball measure on `F_q × ℍ` (`≪ [SL₂:Γ₀(q)] R`) | `SCSSharp.Ball` | ≈ 200 |
| pointwise with `q`-powers | `GeoPoint21`-style | ≈ 400 |
| Tauberian along a progression, Abel with `(mn)^{−11/2}` | `TauRiesz21`, `TauAsum21`, `TauFinal21` | ≈ 900 |

The total is about 3k lines, i.e. 3–5 sessions. The hardest new piece is the unfolding over `Γ₀(q)` with an explicit fundamental domain. Mathlib has `Γ₀(N)` as `CongruenceSubgroup.Gamma0` and finite index, but no fundamental domain.

## 5. Literature

Cited from memory, not re-checked:

* Jutila, *Lectures on a method in the theory of exponential sums* (1987);
* Blomer, "Shifted convolution sums and subconvexity bounds for automorphic L-functions", IMRN 2004: `η` close to `1/2 − θ`, polynomial in `a, b`;
* Blomer–Harcos, "The spectral decomposition of shifted convolution sums", Duke 2008;
* Weil (1948) for Kloosterman sums.
