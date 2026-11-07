# Prime number theorem for Ramanujan's `τ`

Lean: `RamanujanTau/TauPNT/` (8 files, about 1480 lines, no `sorry`, no new axiom, no `native_decide`).
Build with `nice -n 10 lake build RamanujanTau.TauPNT.Main` (exit 0). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for every headline.

Notation: `λ(p) = τ(p)p^{−11/2}` (`EdgeNonvanishing.lam`), `L(s) = L(Δ, s+11/2)` (`Lnorm`), and
`Λ_Δ(p^k) = (α_p^k + β_p^k) log p` (`vM`). The Satake parameters `α_p, β_p` satisfy `α_pβ_p = 1`,
`α_p + β_p = λ(p)` and `‖α_p‖² ≤ p`. The last bound is proved without Deligne (`alpha_sq_le`).

## Results

| statement | Lean | hypotheses | evidence |
|---|---|---|---|
| `exp(∑ cc(n) n^{−s}) = L(s)` on `Re s > 1`, with `cc(p^k) = A_k/k` | `exp_LSeries_cc` | none | (1) |
| `−L'/L(s) = ∑ Λ_Δ(n) n^{−s}` on `Re s > 1` | `negLogDeriv_eq_LSeries` | none | (1) |
| `−L'/L` is continuous on `Re s ≥ 1` (no pole) | `continuousOn_negLogDeriv` | none | (1) |
| `∑_p τ(p)p^{−11/2} log p · p^{−σ}` has a finite limit as `σ → 1⁺` | `primeSum_tendsto`, `tau_PNT_smoothed` | none | (1) |
| `∑_p λ(p)² p^{−σ} → ∞` as `σ → 1⁺` | `tendsto_sum_lam_sq` | `[DeligneBound]` | (2) |
| infinitely many primes with `τ(p) > 0`, and infinitely many with `τ(p) < 0` | `tau_prime_sign_changes` | `[DeligneBound]` | (2) |
| `∑_{n<N} Λ_Δ(n) = o(N)` | `psiDelta_littleO` | `[DeligneBound]`, `WienerIkeharaHyp` | (2) |
| **`∑_{p<N} τ(p)p^{−11/2} log p = o(N)`** | `tau_PNT` | `[DeligneBound]`, `WienerIkeharaHyp` | (2) |
| **`∑_{p<N} τ(p) log p = o(N^{13/2})`** | `tau_PNT_tau` | `[DeligneBound]`, `WienerIkeharaHyp` | (2) |

```lean
theorem primeSum_tendsto : Tendsto primeSum (𝓝[>] 1) (𝓝 ((negLogDeriv 1 - tail 1).re))
--   primeSum σ = ∑' p : Nat.Primes, lam p * Real.log p * (p : ℝ) ^ (-σ)
theorem tau_prime_sign_changes [DeligneBound] :
    (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ 0 < tau p) ∧ (∀ N : ℕ, ∃ p, N ≤ p ∧ p.Prime ∧ tau p < 0)
theorem tau_PNT [DeligneBound] (hWI : WienerIkeharaHyp) :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, lam p * Real.log p) / N) atTop (𝓝 0)
theorem tau_PNT_tau [DeligneBound] (hWI : WienerIkeharaHyp) :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p) /
      (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0)
```

## Named hypotheses

* `DeligneBound` is the repo's existing class (`RamanujanTau/Deligne.lean`): `τ(p)² ≤ 4p¹¹`.
* `WienerIkeharaHyp` (`WienerIkehara.lean`) is the Wiener–Ikehara Tauberian theorem. It is a pure
  analysis statement with no number theory in it:

  ```lean
  def WienerIkeharaHyp : Prop :=
    ∀ (f : ℕ → ℝ) (A : ℝ) (G : ℂ → ℂ), (∀ n, 0 ≤ f n) →
      (∀ σ' : ℝ, 1 < σ' → LSeriesSummable (fun n => (f n : ℂ)) σ') →
      ContinuousOn G {s | 1 ≤ s.re} →
      Set.EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - A / (s - 1)) {s | 1 < s.re} →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / N) atTop (𝓝 A)
  ```

  This is the statement of `WienerIkeharaTheorem''` in PrimeNumberTheoremAnd
  (`PrimeNumberTheoremAnd/Wiener.lean`, about 3900 lines with its Fourier dependencies). That
  project uses toolchain v4.32 and this repo uses v4.30, so it cannot be imported. Discharging the
  hypothesis means porting that proof. That file contains two `sorry`s (`prelim_decay_2/3`), and I
  did not check whether the Wiener–Ikehara chain depends on them. Mathlib itself has no
  Wiener–Ikehara or Newman theorem. `PrimesInAP` only sets up the auxiliary function.

## Proofs

1. **The log Euler product** (`LogEuler`). Put `Y = p^{−s}`. The local logarithm is
   `ℓ_p = −log(1−α_pY) − log(1−β_pY) = ∑_k A_kY^k/k`. This uses `Local.list_log` and needs
   `‖α_pY‖ ≤ 2^{(1−2σ)/2} < 1`. The sum over prime powers converges absolutely on `Re s > 1`:
   for `k = 1` this is Rankin's `∑|τ(n)|n^{−σ−11/2} < ∞`, and for `k ≥ 2` it is `|A_k| ≤ 2‖α‖^k`
   with `‖α‖² ≤ p`. Then `HasSum.cexp` together with `HeckeZeros.tauL_eulerProduct` gives
   `exp(∑ cc(n) n^{−s}) = L(s)`.
2. **The log-derivative** (`LogDeriv`). Since `Λ_Δ = log · cc`, Mathlib's `LSeries_hasDerivAt`
   gives `−L'/L = ∑ Λ_Δ n^{−s}`. `L` is entire and nonzero on `Re s ≥ 1`
   (`EdgeNonvanishing.tauL_ne_zero_of_ge`), so `−L'/L` is continuous on the closed half-plane.
3. **The smoothed PNT** (`PrimeSum`, unconditional). Split `∑_n Λ_Δ(n)n^{−σ}` as the prime sum
   plus a tail `T(σ)` over `p^{k+2}`. On `σ ≥ 1` the tail is dominated by
   `Mb(p,k) = [k=0]·4(λ²+2)p^{−7/4} + (8/r)p^{−5/4}r^k` with `r = 2^{−1/2}`. This uses
   `log p ≤ 4p^{1/4}`, `|A_2| ≤ λ²+2`, `∑_p λ(p)²p^{−7/4} < ∞` (the Rankin–Selberg series `RS`
   at 7/4) and `|A_k| ≤ 2p^{k/2}`. Dominated convergence gives `T(σ) → T(1)`, and continuity
   gives `−L'/L(σ) → −L'/L(1)`.
4. **Sign changes** (`Signs`, Deligne).
   - Deligne gives `‖α_p‖ = 1` and `|A_k| ≤ 2`.
   - The local factor of `ζ(2s)R(s)` (`rs_local`) is `exp ∑_k A_k²Y^k/k`. This gives
     `ζ(2σ)R(σ) = exp X(σ)` with `X(σ) ≤ ∑_p λ²p^{−σ} + 32∑_p p^{−2}`.
   - `R(σ) ≥ rsc·ζ(σ) − 5K`, where `rsc > 0` comes from `petNormSqF_pos` and
     `ζ(σ) ≥ 1/(2(σ−1))` from the residue. Together these give `∑_p λ²p^{−σ} → ∞`.
   - Now suppose `ελ(p) ≥ 0` for all `p ≥ P`. Then `λ² ≤ 2ελ` there, so
     `log 2·∑λ²p^{−σ} ≤ 2ε·primeSum(σ) + O_P(1)`. The right side is bounded by step 3, which is a
     contradiction.
5. **The PNT** (`WienerIkehara`, `TauForm`).
   - Deligne gives `|Λ_Δ| ≤ 2Λ`, so `a± = 2Λ ± Λ_Δ ≥ 0`.
   - `∑a±(n)n^{−s} − 2/(s−1) = 2(−ζ'/ζ − 1/(s−1)) ± (−L'/L)`. This is continuous on `Re s ≥ 1`
     by Mathlib's `continuousOn_LFunctionResidueClassAux` with `q = 1`, plus step 2.
   - Wiener–Ikehara gives `(∑_{n<N} a±)/N → 2`. Subtracting gives `∑_{n<N} Λ_Δ = o(N)`.
   - The prime powers contribute at most `2(ψ−θ)(N) ≤ 4√N log N`
     (`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).
   - Abel summation (`abel_identity`, `weighted_littleO`) converts this to `∑ τ(p) log p = o(N^{13/2})`.

## Gaps

* **Wiener–Ikehara.** It is a named hypothesis. Porting the PrimeNumberTheoremAnd proof would
  take an estimated 2–4k lines. Newman's contour proof needs Cauchy's theorem on a non-rectangular
  contour, which Mathlib does not have.
* **Deligne.** Both `tau_PNT` and the sign-change theorem use it:
  - the majorant `|Λ_Δ| ≤ 2Λ`;
  - the `k ≥ 2` terms of `log ζ(2s)R(s)`.

  A Deligne-free PNT would need the majorant `(1 ± A_k)² ≥ 0`, that is, the coefficients of
  `ζ·(ζ(2s)R)`. That in turn needs `ζ(2s)R(s) ≠ 0` on `Re s = 1`, i.e. `L(Sym²Δ, 1+it) ≠ 0`
  (Shimura, Gelbart–Jacquet), which is not formalized. The smoothed result (step 3) is already
  Deligne-free.
* No error term. A zero-free region is not done (see EDGE_NONVANISHING).
* `tau_PNT` sums over `p < N`, with `N ∈ ℕ`. The real-`x` form follows from monotonicity of `⌊x⌋`
  and is not stated separately.

## Literature

Rankin (1939); Ogg, *Modular forms and Dirichlet series* (1969); Moreno, "Prime number theorems
for the coefficients of modular forms", Bull. AMS 1972 / 1974; Jacquet–Shalika (1976);
Wiener–Ikehara (1931–32); PrimeNumberTheoremAnd (Kontorovich–Tao et al.).
