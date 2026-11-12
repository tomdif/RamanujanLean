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

## 6. Update (2026-11-06): coprime case — stage 1 done, stage 2 started (`RamanujanTau/SCS2Coprime/`)

**Status: checkpoint. Evidence level 1 for the pieces listed below. `SCS2'` for coprime `a ≠ b` is not yet proved.**

* Build: `nice -n 10 lake build RamanujanTau.SCS2Coprime.Main` exits 0.
* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit` or `native_decide`.
* 6 files, about 600 lines.

**Stage 1: `Γ₀(q)` infrastructure (reusable, done).**

* `Bruhat0`. The Bruhat layers of `SCSProof` are indexed by the lower-left entry `c = γ₁₀`, because `slEquiv` parametrizes by the left column and `T^k` keeps it fixed.
  * Hence `tsum_IγQ_eq`: `Σ_{γ ∈ SL₂(ℤ), q∣γ₁₀} I(γ) = Σ_{q∣c} T(c)`.
  * The layer bounds `‖T(c)‖ ≤ gK(|c|)` hold layer by layer. So `norm_tsum_IγQ_le_gK` and `norm_tsum_IγQ_le_gcd` hold with the **same constants as for `SL₂(ℤ)`, uniformly in `q`**:

        ‖Σ_{q∣γ₁₀} I(γ)‖ ≤ C h^β ε³ Y^{−3/2−2δ}.

  * This is a slight under-use: a further gain `q^{−1/2}` from `c ≡ 0 (q)` is available but not needed.
* `Gamma0`: `mem_Gamma0_iff : γ ∈ Γ₀(q) ↔ q ∣ γ₁₀`, `tsum_Gamma0_Iγ`, and `norm_tsum_Gamma0_Iγ_le`. The last is the `‖P_q‖²` input for `Γ₀(q)\(ℍ×ℍ)`.
* `Unfold`: there is **no fundamental domain**. For any subgroup `H ≤ SL₂(ℤ)`:
  * `cosetEquiv : H × (H\SL₂(ℤ)) ≃ SL₂(ℤ)`, `(h, x) ↦ h·x.out`;
  * `lintegral_unfold_sub`: `Σ_x ∫_{U×ℍ} Σ_{h∈H} Ξ(h x.out p) = 2∫Ξ`;
  * `lintegral_unfold_inv`: the same with an `H`-invariant factor `Φ`.

  The integral over `Γ₀(q)\(ℍ×ℍ)` is replaced by `Σ_x ∫_{U×ℍ} (·)∘x.out`. This avoids the geometric construction of `⋃γᵢU` and the measure-zero overlaps (estimated at 500 lines in §4). It also needs no finite index for the `ℝ≥0∞` identities.

**Stage 2: `Ψ_{a,b}` (started).** In `TwoPointAB`:

* `scl_smul`: `a(γz) = γ'_a(az)` with `γ'_a = [[A, aB],[C/a, D]]`, for `a ∣ C`;
* `PsiAB_smul` / `PsiAB_smul_Gamma0`: `Ψ_{a,b}(z,w) = (z−w̄)¹²Δ(az)conj Δ(bw)` is invariant under `γ` with `a, b ∣ γ₁₀`, in particular under `Γ₀(ab)`;
* `norm_PsiAB_le`: `‖Ψ_{a,b}‖ ≤ M (ab)^{−6} Dh⁶`.

**Remaining for `SCS2'`** (estimate about 2.2k lines, 2–3 sessions):

1. The diagonal horocycle coefficient `∫₀¹Ψ_{a,b}(x+iy, x+yζ)e(−ℓx)dx = (y(i−ζ̄))¹² e^{−2πℓy} Σ_{am−bn=ℓ} τ(m)τ(n)e^{−bn·2πy(1+iζ̄)}`. This is a double q-expansion with `∫₀¹e(kx)dx = [k=0]`. About 250 lines.
2. The Hölder/unfolding step on `Γ₀(q)\(ℍ×ℍ)`: copy `CS3`/`CS4`/`NormQ` with `Σ_x ∫_U (·)∘x.out`.
   * The ball measure becomes `[SL₂:Γ₀(q)]·8R`. The index needs a finiteness/size bound: Mathlib has `Gamma0` of finite index; `≤ q²` suffices.
   * About 500 lines.
3. The `Q_eq`-type identity and the pointwise bound for `G_{a,b}`, with `(ab)`-powers. About 600 lines.
4. The Tauberian step along the progression `a ∣ bn+ℓ`, and Abel summation with `(mn)^{−11/2}`. About 900 lines.

**Correction to §3 (the `b < η` claim).** The recommendation "`b < η` by a parameter change" is **wrong**.

* For `|ℓ| = h ≤ N`, the Abel range `t < h` contributes `≍ h` with no cancellation. The pointwise bound only reaches lengths at least `h`.
* So `|S| ≪ N^{1−η}h^{b} + h`. This fits the shape `N^{1−η}|ℓ|^b` only if `b ≥ η` (via `(t+h)^{1/2} ≤ (2h)^{η}(N+h)^{1/2−η}`, as in `TauFinal21`).
* Hence `b = η` is optimal for this method, and `scs2_diag` (`b = η = 1/21`) is already the best diagonal statement.
* `SCS2' η b B` with `b < η` would need spectral input for `|ℓ| ≍ N`.
* For Hafner the right hypothesis is `b = η` together with the range restriction `|ℓ| ≤ N^{1−θ}`, giving `N^{1−θη}(ab)^B`.

## 7. Update (2026-11-06): stage 2, item 1 done (horocycle coefficient); coset count

**Status: checkpoint. Evidence level 1 for the pieces below. `SCS2'` for coprime `a ≠ b` is not yet proved.**

* Build: `nice -n 10 lake build RamanujanTau.SCS2Coprime.Main2` exits 0.
* Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit` or `native_decide`.
* 4 new files, about 340 lines. No committed file was modified.

* `Fourier.lean`:
  * `integral_cexp_int`: `∫₀¹e(kx)dx = [k=0]`;
  * **`fourier_Delta_scl`**: `∫₀¹ Δ(a(x+iy)) e(−Nx) dx = cA(a,N) e^{−2πNy}`, with `cA(a,N) = τ(N/a)` if `a ∣ N`, `N ≥ 0`, else `0`.
* `CoeffAB.lean`: **`coeff_PsiAB`**

      ∫₀¹ Ψ_{a,b}(x+iy, x+yζ) e(−ℓx) dx = (y(i−ζ̄))¹² e^{−2πℓy} G_{a,b,ℓ}(2πy(1+iζ̄)),
      G_{a,b,ℓ}(W) = Σ_n τ(n) cA(a, bn+ℓ) e^{−bnW}.

  The nonzero terms are exactly `am = bn + ℓ`. So the Laplace transform of the two-sided sum appears at the complex point `bW`. This is item 1 of §6.
* `Index.lean`: `index_Gamma0_le : [SL₂(ℤ):Γ₀(q)] ≤ q⁴` and `card_RCos_Gamma0_le`. These go through `Γ(q) ≤ Γ₀(q)` and `|SL₂(ℤ/q)| ≤ q⁴`, and supply the coset count for the Hölder step (item 2).

**Remaining** (estimate about 1.9k lines). The exact target shape stays as §6, `|S(a,b;ℓ,N)| ≪ N^{1−1/21}|ℓ|^{1/21}(ab)^B`, hence `≪ N^{1−θ/21}(ab)^B` for `|ℓ| ≤ N^{1−θ}`.

* **Item 2 (about 450 lines):** the Hölder step `‖∫Ψ_{a,b} conj ft‖ ≤ ½ √(q⁴(M(ab)^{−6}R⁶)²·8R) · √(2‖Σ_{Γ₀(q)} I‖)`.
  * It uses `lintegral_unfold_inv` with `Φ = |Ψ_{a,b}|²·1_{supp}`, which is `Γ₀(q)`-invariant by `PsiAB_smul_Gamma0` and the invariance of `Dh`.
  * Then `card_RCos_Gamma0_le`, the ball bound `lintegral_U_ball'`, and `norm_tsum_Gamma0_Iγ_le`.
* **Item 3 (about 600 lines):** the `Q_eq` analogue with `coeff_PsiAB`. Then the pointwise bound for `G_{a,b,ℓ}` at `bW`, with Lipschitz control via `Σ_n |τ(n) cA(a,bn+ℓ)| e^{−bnσ} ≪ (bσ)^{−12}` (Cauchy–Schwarz plus `coef_sq_laplace`).
* **Item 4 (about 850 lines):** the Tauberian step and unsmoothing for `Σ_{bn ≤ x} τ(n)cA(a,bn+ℓ)`. Rankin short sums apply after Cauchy–Schwarz. Then Abel summation with `(mn)^{−11/2}` and `m = (bn+ℓ)/a`.

## 8. Update (2026-11-06): the two-sided bound is proved for all `a, b ≥ 1` (`SCS2Coprime/Main3`)

**Status: DONE. Evidence level 1 (Lean, axiom-clean, no hypotheses).**

    nice -n 10 lake build RamanujanTau.SCS2Coprime.Main3      # exit 0

* Every `#print axioms` in `Main3.lean` (19 names, items 2–4 and the headlines) gives
  `[propext, Classical.choice, Quot.sound]`.
* A grep finds no `sorry`, `admit`, `native_decide` or `axiom` in the 10 new files.
* 10 new files, about 3.0k lines. No committed file was modified, and nothing outside
  `RamanujanTau/SCS2Coprime/` except this section.

**Headlines** (`RamanujanTau.SCS2Coprime`, `shiftSum2` is the committed `HeckeAFE.shiftSum2`):

```lean
theorem scs2_general : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
    |shiftSum2 a b ℓ N| ≤
      C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12

theorem scs2_gcd : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ g → 1 ≤ a → 1 ≤ b →
    ℓ ≠ 0 → |shiftSum2 (g * a) (g * b) (g * ℓ) N| ≤
      C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12

theorem scs2_range : ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
      |(ℓ : ℝ)| ≤ (N : ℝ) ^ (1 - θ) →
      |shiftSum2 a b ℓ N| ≤ C * (N : ℝ) ^ (1 - θ / 21) * ((a * b : ℕ) : ℝ) ^ 12
```

So the shape is `SCS2'` of §3 with `η = b = 1/21`, `B = 12`:
`|S(a,b;ℓ,N)| ≪ N^{1−1/21} |ℓ|^{1/21} (ab)^{12}`, hence `≪ N^{1−θ/21}(ab)^{12}` for
`|ℓ| ≤ N^{1−θ}`. The stated `SCS2 η B` (with `(N+|ℓ|)^{1−η}` and no `ℓ`-power) is **not** proved;
by §3/§6 it is out of reach of this method for `|ℓ| ≍ N`.

**Coprimality is not needed.** `Ψ_{a,b}` is `Γ₀(ab)`-invariant for every `a, b`
(`PsiAB_smul_Gamma0`), and nothing else uses `gcd(a,b) = 1`. `scs2_gcd` only records that the committed
gcd reduction improves `(ab)^{12}` to `(ab/g²)^{12}` and `|ℓ|` to `|ℓ|/g`. The diagonal `a = b` is
covered too; there the committed `scs2_diag` is sharper (no `(ab)`-power).

### 8a. What was done (items 2–4 of §6/§7)

| file | content |
|---|---|
| `Holder.lean` | `tsum_coset` (`Σ_{SL₂(ℤ)} = Σ_x Σ_{Γ₀(q)}`, `x` over right cosets), `finite_RCos_Gamma0`, `tsum_enorm_ft_le_N0` (`Σ_γ‖ft(γp)‖ ≤ N₀` everywhere), `PtQ` (Poincaré series over `Γ₀(q)`), `SQ = Σ_x |P_q(x.out p)|²`, **`lintegral_SQ_le`**: `∫_{U×ℍ} S_q ≤ 2‖Σ_{h∈Γ₀(q)} I(h)‖` |
| `Holder2.lean` | **`norm_QAB_le`**: `‖∫Ψ_{a,b} conj ft‖ ≤ ½√(c² q⁴ · 8R)·√(2‖Σ_{Γ₀(q)} I‖)`, `c = M(ab)^{−6}R⁶` |
| `QformAB.lean` | `Q_eqAB`, **`main_term_leAB`** (copy of `SCSProof.Qform*`/`Main1` with `Ψ_{a,b}` and `cfAB`) |
| `GboundsAB.lean` | `cR a b ℓ n = τ(n)·[a∣bn+ℓ]τ((bn+ℓ)/a)`, `Gc`, **`GAB_eq`**: `G_{a,b,ℓ}(W) = Gc(cR)(bW)`; generic Lipschitz `norm_Gc_sub_le`; **`cR_laplace`** (trivial bound via the injection `n ↦ (bn+ℓ)/a`) |
| `PointAB.lean` | `cfAB_sub_le`, `norm_G0_leAB`, **`pointwise_parAB`** (`K` independent of `a, b`), **`pointwise_Gc`**: `‖Gc(cR)(σ+iv)‖ ≤ K ℓ^{1/21}(|2v/σ|+3) b¹² σ^{−11901/1000}` for `0<σ≤b`, `ℓσ≤b` |
| `TauberGen.lean` | the Tauberian step for an **arbitrary** real sequence: `laplace_rieszC`, `Rmean2C_le`, **`AsumC_bound`** (pointwise input + total and short-interval `ℓ¹` bounds ⇒ `|Σ_{n≤N}c_n| ≪ x^{12−1/21}`) |
| `RankinAB.lean` | `sum_cAR_sq_le` (Rankin along the progression), `short_cR`, `sum_cR_cs` (Cauchy–Schwarz), **`AsumAB_bound`**: `|Σ_{n≤N} cR(n)| ≤ K ℓ^{1/21}(b+1)¹²(N+1)^{12−1/21}` for `1 ≤ ℓ ≤ N+1` |
| `AbelAB.lean` | weight `wAB(t) = t^{−11/2}((bt+ℓ)/a)^{−11/2}`, `abs_wAB'_le`, **`shiftSum2_eq`**: `S(a,b;ℓ,N) = Σ_{n≤N₁} wAB(n)cR(n)`, `N₁ = min(N, ⌊(aN−ℓ)/b⌋)` |
| `FinalAB.lean` | Abel summation, `integrand_le`, `boundary_le`, **`shiftSum2_bound_pos`** (`ℓ ≥ 1`) |
| `Main3.lean` | `shiftSum2_neg` (`S(a,b;−ℓ) = S(b,a;ℓ)`), the three headlines, `#print axioms` |

### 8b. Where the exponents come from

* **Pointwise.** Hölder over the `≤ q⁴` cosets gives `M(ab)^{−6}·q² = M(ab)^{−4} ≤ M`. The trivial
  bounds for `cR` at `σ = bκY` are `≤ 2C₀(κY)^{−12}` uniformly in `a, b ≥ 1` (the Lipschitz factor `b`
  from `‖bW − bW₀‖` cancels against `(bσ)^{−1}`). So `‖G_{a,b,ℓ}(W₀)‖ ≤ K ℓ^{1/21} A t⁹⁹ Y^{−12}` with
  the **same** `K` as `SCSSharp2.pointwise_par21`. The `b¹²` in `pointwise_Gc` is only the rescaling
  `σ_W = σ/b`, which gives `b^{11901/1000} ≤ b¹²`.
* **Tauberian.** The chain is unchanged: `κ = 2/39`, `ι = 1/273`, `j = 13`, `η = 1/21`. The condition
  `ℓσ ≤ b` at `σ = 1/x` holds for `ℓ ≤ x`, which is weaker than the one-sided `h ≤ x`. The short sums
  of `τ((bn+ℓ)/a)²` run over `m`-intervals of length `≤ bD+1` with `m ≤ (b+1)x`, so Rankin costs
  `(b+1)¹²`.
* **Abel.** For `t ≥ ℓ`, `m(t)^{−11/2} ≤ a^{11/2}t^{−11/2}`. For `t < ℓ`, Cauchy–Schwarz gives
  `≪ (b+1)^{1/2} ℓ^{1/21} N^{1/2−1/21} t^{−1/2}`, with `m(t) ≤ (b+1)ℓ`. For `ℓ > N` the trivial bound
  `≪ N ≤ N^{1−1/21}ℓ^{1/21}` applies. In total this is `a^{11/2}(b+1)^{12} ≤ 2^{12}(ab)^{12}`. This
  is not optimized: `B ≈ 6 + 1/2` looks reachable by tracking `b/a` instead of `b+1`.

### 8c. Remaining / not done

* **The stated `HeckeAFE.SCS2 η B` is not discharged.** Its shape `(N+|ℓ|)^{1−η}(ab)^B` is
  method-intrinsically out of reach (§3, §6 correction).
  * The consumer, the Hafner twisted second moment, should be restated against `scs2_range`
    (`|ℓ| ≤ N^{1−θ}`) or against the `SCS2'` shape of `scs2_general`.
  * That restatement touches `HeckeAFE/Hyp.lean` and its users. It was not done here, because
    committed files were off-limits.
* `SCS2Coprime.Main3` is now included in the root import graph.
* The exponents are not optimized (`B = 12`; `η = 1/21` is inherited from `SCSSharp2`).
