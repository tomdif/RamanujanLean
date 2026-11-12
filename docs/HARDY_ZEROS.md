# Hardy's theorem for L(Δ,s): infinitely many zeros on Re s = 6

Module: `RamanujanTau/HardyZeros/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on
`propext`, `Classical.choice` and `Quot.sound`. There are no named hypotheses,
no `sorry` and no `native_decide`.

Build and check: `nice -n 10 lake build RamanujanTau.HardyZeros.Main` (exit 0).
The `#print axioms` lines are at the end of `Main.lean`.

## Headlines (`namespace RamanujanTau.HardyZeros`)

```lean
theorem tauL_infinitely_many_critical_zeros : ∀ T : ℝ, ∃ t > T, tauL (6 + t * I) = 0
theorem tauL_critical_zeros_infinite : Set.Infinite {t : ℝ | tauL (6 + t * I) = 0}
theorem tauL_zeros_on_critical_line_infinite : Set.Infinite {s : ℂ | s.re = 6 ∧ tauL s = 0}
theorem heckeLambda_infinitely_many_critical_zeros :
    ∀ T : ℝ, ∃ t > T, heckeLambda (6 + t * I) = 0
theorem Zr_infinitely_many_zeros : ∀ T : ℝ, ∃ t > T, Zr t = 0     -- Zr t = Re Λ(6+it) = Λ(6+it)
```

Here `tauL` is the entire continuation `(2π)^s Γ(s)⁻¹ Λ(s)` of `L(Δ,s) = Σ τ(n) n^{-s}`
(`HeckeL.tauL`, `tauL_eq_LSeries`). `heckeLambda` is Hecke's `Λ(s) = ∫₀^∞ Δ(iy) y^{s−1} dy`.

## Proof

1. **Decay on the critical line** (`Decay.lean`). Write
   `Λ(6+it) = (2π)^{−6−it} Γ(6+it) L(Δ,6+it)`. Stirling (`Stirling.norm_Gamma_le_stirling`)
   and convexity with ε = 1/2 (`HeckeConvex.tauL_convexity`) give
   `‖Λ(6+it)‖ ≤ K(1+|t|)^7 e^{−π|t|/2}`. Hence, for every `b < π/2`,
   `‖Λ(6+it)‖(1+|t|)e^{b|t|} ≤ C(1+t²)⁻¹`
   (`heckeLambda_line_decay`, `integrable_heckeLambda_line`).
2. **Fourier/Mellin identity** (`Fourier.lean`). Define `Φ(w) = ∫ Λ(6+it) e^{−itw} dt`.
   Differentiation under the integral sign shows Φ is holomorphic on the strip
   `|Im w| < π/2` (`differentiableOn_Phi`). For real `u`, Mathlib's
   `mellinInv_mellin_eq` at `x = e^u` gives `Φ(u) = 2π e^{6u} Δ(i e^u)` (`Phi_eq_real`).
   The function `G(w) = e^{6w} Δ(i e^w)` is holomorphic on the strip, so the identity
   theorem gives `Φ = 2πG` there (`Phi_eq_strip`). At `w = iα`:
   `∫ Λ(6+it) e^{αt} dt = 2π e^{6iα} Δ(i e^{iα})` for `|α| < π/2` (`integral_Zc_exp`).
3. **Realness and evenness**. Since `conj(6+it) = 12 − (6+it)`, `heckeLambda_conj` and the
   functional equation make `Λ(6+it)` real (`Zc_conj`, `Zc_eq_Zr`) and even in t (`Zr_neg`).
4. **Boundary decay at the cusp −1** (`Cusp.lean`). Put `α = π/2 − β`. Then
   `z = i e^{iα} = −cos β + i sin β → −1`. With `v = z+1`, we have `Δ(z) = Δ(v)`, and
   `Δ(−1/v) = v¹²Δ(v)` (`Dc_S`). Also `Im(−1/v) ≥ 1/(2 sin β)` and `|v|¹² ≥ sin¹²β`.
   Cusp decay at ∞ then gives `‖Δ(z)‖ ≤ A e^{−π/sin β}/sin¹²β ≤ A(N+12)! β^N` for every N
   (`Dc_rot_decay`).
5. **Hardy's argument, finite-difference form** (`Abstract.lean`, `hardy_abstract`).
   This step is pure real analysis about a continuous even `Z` with
   `|∫ Z e^{(π/2−β)t}| ≤ C_N β^N`. If `Z` had no zeros beyond T, then by the intermediate
   value theorem it would have one sign there; assume without loss of generality that
   `Z > 0` for `|t| ≥ T`. Take an even m, `δ = β/(2m)`, and the weight
   `w(t) = e^{(π/2−β)t}(e^{δt}−1)^m ≥ 0`. Expanding binomially gives
   `|∫ Zw| ≤ 2^m C β^{m+1}`, with every node in `[π/2−β, π/2−β/2]`. Positivity on
   `(T+1, T+2]` gives `∫ Zw ≥ c₀(δ(T+1))^m − K(δT)^m`. Divide by `δ^m` and let β → 0 to get
   `c₀(T+1)^m ≤ K T^m` for every even m. Bernoulli's inequality contradicts this for large m.

   This replaces the moments `∫ Z t^{2n} cosh(αt)` in Hardy's original proof by finite
   differences in α, so the proof never differentiates `G`.

## Files

- `RamanujanTau/HardyZeros/Abstract.lean`: `hardy_abstract`, `core` (imports only Mathlib)
- `RamanujanTau/HardyZeros/Decay.lean`: decay of `Λ(6+it)`
- `RamanujanTau/HardyZeros/Fourier.lean`: `Φ`, `G`, identity theorem, `integral_Zc_exp`, realness
- `RamanujanTau/HardyZeros/Cusp.lean`: `Dc_S`, `Delta_cusp_bound`, `Dc_rot_decay`
- `RamanujanTau/HardyZeros/Main.lean`: assembly and headlines

## Scope and gaps

- The result is qualitative: it proves infinitely many zeros. It gives no count (such as
  Hardy–Littlewood's ≫ T, or ≫ T log T), and it says nothing about simplicity of the zeros.
- `HardyZeros.Main` is included in the root import graph and the [result catalog](RESULTS.md).

## Literature

G. H. Hardy, *Sur les zéros de la fonction ζ(s) de Riemann*, C. R. Acad. Sci. Paris 158 (1914).
For the cusp-form version see e.g. Iwaniec–Kowalski, *Analytic Number Theory*, §5 and the
exercises on Hardy's method, and Hafner's work on zeros of L-functions of cusp forms on the
critical line.
