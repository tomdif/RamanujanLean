# Wiener–Ikehara Tauberian theorem: `WienerIkeharaHyp` discharged

Lean: `RamanujanTau/WienerIkehara/` (7 files, about 4360 lines, no `sorry`, no new axiom, no
`native_decide`). Build with `nice -n 10 lake build RamanujanTau.WienerIkehara.Main` (exit 0).
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every headline below.

## Headline results

| statement | Lean | hypotheses | evidence |
|---|---|---|---|
| Wiener–Ikehara (continuous boundary extension form) | `WienerIkehara.wienerIkehara : TauPNT.WienerIkeharaHyp` | none | (1) |
| `∑_{p<N} τ(p)p^{−11/2} log p = o(N)` | `WienerIkehara.tau_PNT_deligne` | `[DeligneBound]` | (2) |
| `∑_{p<N} τ(p) log p = o(N^{13/2})` | `WienerIkehara.tau_PNT_tau_deligne` | `[DeligneBound]` | (2) |
| PNT, discrete form: `(∑_{n<N} Λ(n))/N → 1` | `WienerIkehara.PNT_cumsum` | none | (1) |
| PNT: `ψ(x)/x → 1` (Mathlib's `Chebyshev.psi`) | `WienerIkehara.PNT_psi` | none | (1) |

```lean
theorem wienerIkehara : RamanujanTau.TauPNT.WienerIkeharaHyp
-- ∀ f A G, (∀ n, 0 ≤ f n) → (∀ σ' > 1, LSeriesSummable f σ') → ContinuousOn G {s | 1 ≤ s.re} →
--   EqOn G (fun s => LSeries f s - A/(s-1)) {s | 1 < s.re} →
--   Tendsto (fun N => (∑ n ∈ range N, f n)/N) atTop (𝓝 A)
theorem tau_PNT_tau_deligne [DeligneBound] :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p) /
      (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0)
theorem PNT_psi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)
```

With these results the τ-PNT in `docs/TAU_PNT.md` depends only on `DeligneBound`.

Mathlib (the version pinned here, 2026-05-02) has no prime number theorem and no Wiener–Ikehara
theorem. `PrimesInAP` only sets up the auxiliary function `LFunctionResidueClassAux`, and
`Chebyshev` only gives `ψ(x) = O(x)`. `PNT_psi` is therefore new to this repo's Mathlib.

## Provenance

This is a port, not an independent proof. The analysis is taken from PrimeNumberTheoremAnd
(Apache-2.0), using the local copy at `~/explicit_formula_lean/.lake/packages/PrimeNumberTheoremAnd`
(commit `a5154676`, 2026-08-30, toolchain v4.32). The theorem used is `WienerIkeharaTheorem''`, and
the chain behind it is:

* `limiting_fourier` / `limiting_cor`: smoothed sums `∑ f(n)/n · ψ̂(log(n/x)/2π)` → `A∫ψ` for
  `W21` test functions, using Riemann–Lebesgue and `σ → 1⁺` limits. Only continuity of `G` on
  `Re s ≥ 1` is used; no analytic continuation is needed.
* `wiener_ikehara_smooth` for compactly supported smooth `Ψ` on `(0,∞)`, then
  `WienerIkeharaInterval` (smooth Urysohn squeeze, positivity of `f`), then `WienerIkeharaTheorem'`
  under a Chebyshev hypothesis `cheby f`.
* `auto_cheby`: `cheby f` follows from the hypotheses alone, by `crude_upper_bound`, a short-interval
  bound and a bootstrap induction. This gives `WienerIkeharaTheorem''`.

Changes made in the port:

* Blueprint `@[blueprint …]` and `blueprint_comment` annotations were stripped.
* `convert!`, `convert_to!` and `using!` were changed to `convert`, `convert_to` and `using`.
  These are newer-Mathlib variants; the plain forms on v4.30 behave as needed.
* `sdiff_eq_compl_inter` was changed to `diff_eq_compl_inter`.
* The sorried `prelim_decay_2` and `prelim_decay_3`, together with `AbsolutelyContinuous` and
  `decay_alt` that depend on them, were deleted. Nothing in the Wiener–Ikehara chain used them.
  `#print axioms` confirms this.
* The arithmetic-progression section (`WeakPNT_character` and the sections after it) was dropped.
* Sobolev, Fourier, SmoothExistence and Wiener were moved into namespace `RamanujanTau.WI`.
  A few dotted helper lemmas stay at the root: `Finset.sum_shift_*`,
  `Filter.EventuallyEq.summable`, `BoundedAtFilter.*`, `Asymptotics.IsBigO.{add_isLittleO_right,sq}`,
  `Real.log_eventually_gt_atTop` and `Real.fourierIntegral_conv*`. `Support.lean` and
  `Asymptotics.lean` (small helpers) are also at the root, as in the original.

| file | content |
|---|---|
| `Support.lean`, `Asymptotics.lean` | small helper lemmas |
| `Sobolev.lean` | `CS n E` (compactly supported `C^n`), `trunc`, `W1`, `W21` |
| `Fourier.lean` | Fourier transform of derivatives and of `W21` |
| `SmoothExistence.lean` | smooth bump functions |
| `Wiener.lean` | the Wiener–Ikehara proof (`WienerIkeharaTheorem''`), and `WeakPNT` (under `cheby`) |
| `Main.lean` | `wienerIkehara`, the τ-PNT corollaries, `PNT_cumsum` and `PNT_psi` |

## Gaps

None for the stated goals. The τ results still assume `DeligneBound` (Deligne's theorem), which is
an existing named hypothesis in the repo.


## License

The ported files (`Wiener.lean`, `Sobolev.lean`, `Fourier.lean`, `SmoothExistence.lean`, `Support.lean`,
`Asymptotics.lean`) are derived from *Prime Number Theorem and More* (A. Kontorovich, T. Tao et al.,
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) and remain under the Apache License 2.0; a copy
is in `RamanujanTau/WienerIkehara/LICENSE-PrimeNumberTheoremAnd`. Each file's header records the
modifications made. The rest of this repository is MIT-licensed.
