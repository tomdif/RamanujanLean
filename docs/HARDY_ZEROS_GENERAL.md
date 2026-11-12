# Hardy's theorem for level-one cusp forms with real coefficients

Module: `RamanujanTau/HardyZerosGeneral/` (entry point `Main.lean`).
Evidence level: **(1) Lean, axiom-clean.** Every headline depends only on
`propext`, `Classical.choice` and `Quot.sound`. There are no named hypotheses,
no `sorry` and no `native_decide`.

Build and check: `nice -n 10 lake build RamanujanTau.HardyZerosGeneral.Main` (exit 0).
The `#print axioms` lines are at the end of `Main.lean`.

## Headlines (`namespace RamanujanTau.HardyZerosGeneral`, `k : ℕ`)

```lean
theorem fL_infinitely_many_critical_zeros (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∀ T : ℝ, ∃ t > T, fL f ((k : ℂ) / 2 + t * I) = 0
theorem fL_critical_zeros_infinite (f) (hf) (hreal) :
    Set.Infinite {t : ℝ | fL f ((k : ℂ) / 2 + t * I) = 0}
theorem fL_zeros_on_critical_line_infinite (f) (hf) (hreal) :
    Set.Infinite {s : ℂ | s.re = (k : ℝ) / 2 ∧ fL f s = 0}
theorem heckeLambda_infinitely_many_critical_zeros (f) (hf) (hreal) :
    ∀ T : ℝ, ∃ t > T, heckeLambda f ((k : ℂ) / 2 + t * I) = 0
theorem fL_discriminant_infinitely_many_critical_zeros :
    ∀ T : ℝ, ∃ t > T, fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I) = 0
```

`fL`, `heckeLambda` and `coef` come from `HeckeConvexGeneral`. `coef f n` is the n-th
q-expansion coefficient, and `fL f` is the entire continuation `(2π)^s Γ(s)⁻¹ Λ(f,s)` of
`∑ a_f(n) n^{−s}` (`fL_eq_LSeries`).

Supporting results:

- `hardy_abstract_parity` and `hardy_abstract_odd` (`Abstract.lean`) extend `hardy_abstract`
  from even `Z` to `Z(−t) = ±Z(t)`.
- `integral_Zc_exp` (`Fourier.lean`) is the general Fourier identity.
- `Fc_rot_decay` (`Cusp.lean`) is the general cusp decay at `−1`.
- `eq_zero_of_odd` (`Main.lean`) shows that level-one cusp forms of odd weight vanish.

## Weights covered

**All weights k.**

- **Odd k:** `f = 0`, so the hypothesis `f ≠ 0` fails and there is nothing to prove. The proof
  evaluates the slash action at `−1 ∈ SL₂(ℤ)` (`eq_zero_of_odd`).
- **k < 12:** `f = 0` (`eq_zero_of_lt_twelve`).
- **k ≡ 0 mod 4:** the root number is `i^k = 1`, and `Z(t) = Λ(f,k/2+it)` is real and even.
- **k ≡ 2 mod 4** (for example k = 18, 22, 26, 30): the root number is `i^k = −1`. Then
  `conj Z = −Z` and `Z(−t) = −Z(t)`, so `Z = i·Y` with `Y = Im Z` real and **odd**. (Here
  Λ(f,k/2) = 0 is forced.) Hardy's argument still works, but with odd finite-difference
  orders m. The weight `(e^{δt}−1)^m` then has the sign of t, so `Y(t)(e^{δt}−1)^m ≥ 0`
  on both tails once Y has one sign for large t. `core` in `Abstract.lean` now takes the
  parity class of m as a parameter.

## Proof outline

1. **Decay** (`Decay.lean`). Stirling (`norm_Gamma_le_stirling`, σ = k/2) and the convexity
   bound `fL_convexity` with ε = 1/2 give `‖Λ(f,k/2+it)‖ ≤ K(1+|t|)^{k+1}e^{−π|t|/2}`. Hence
   `‖Λ‖(1+|t|)e^{b|t|} ≤ C(1+t²)⁻¹` for every b < π/2.
2. **Fourier identity** (`Fourier.lean`). `Φ(w) = ∫Λ(f,k/2+it)e^{−itw}dt` is holomorphic on
   `|Im w| < π/2`. Mellin inversion (`mellinInv_mellin_eq`, σ = k/2) gives
   `Φ(u) = 2πe^{(k/2)u}f(ie^u)`, and the identity theorem extends this to the strip:
   `∫Λ(f,k/2+it)e^{αt}dt = 2πe^{i(k/2)α}f(ie^{iα})`.
3. **Realness and parity.** With real coefficients, `f(it)` is real (`heckeF_conj`, from the
   q-series). It follows that `Λ(f, conj s) = conj Λ(f,s)`, and with the Hecke functional
   equation `Λ(f,k−s) = i^kΛ(f,s)` this gives `conj Z = i^k Z` and `Z(−t) = i^k Z(t)`.
4. **Cusp −1** (`Cusp.lean`). Write `z = ie^{i(π/2−β)}` and `v = z+1`. Periodicity and
   `f(−1/v) = v^k f(v)` (slash action of S) give `f(z) = v^{−k} f(−1/v)`. Combined with
   `Im(−1/v) ≥ 1/(2 sin β)`, `|v| ≥ sin β` and Mathlib's `CuspFormClass.exp_decay_atImInfty`,
   this yields `|f(z)| ≤ A e^{−π/sin β}/sin^kβ ≤ A(N+k)!β^N`.
5. **Hardy** (`Abstract.lean` and `Zc_zeros_of_rep`). If `Z = Y·c` with `‖c‖ = 1` and Y real
   of parity ±1, then `|∫Y e^{αt}| = 2π‖f(ie^{iα})‖`. That quantity is O(β^N), so
   `hardy_abstract_parity` applies. Take c = 1 when k ≡ 0 mod 4 and c = i when k ≡ 2 mod 4.

## Files

- `RamanujanTau/HardyZerosGeneral/Abstract.lean`: generalized `core`, `core_parity`,
  `hardy_abstract`, `hardy_abstract_parity`, `hardy_abstract_odd` (imports only Mathlib)
- `RamanujanTau/HardyZerosGeneral/Decay.lean`: `sc k t = k/2 + it`, decay on the critical line
- `RamanujanTau/HardyZerosGeneral/Fourier.lean`: `Zc`, `Phi`, `Fc`, `Gc`, `integral_Zc_exp`,
  `heckeLambda_conj`, `Zc_conj`, `Zc_neg`
- `RamanujanTau/HardyZerosGeneral/Cusp.lean`: `Fc_S`, `cusp_bound`, `Fc_rot_decay`
- `RamanujanTau/HardyZerosGeneral/Main.lean`: `eq_zero_of_odd`, `Zc_zeros_of_rep`, headlines,
  the Δ corollary

## Scope and gaps

- The result is qualitative: it proves infinitely many zeros. It gives no count (such as
  ≫ T) and says nothing about simplicity of the zeros.
- **Real coefficients are a hypothesis.** Hecke eigenforms satisfy it, as does any real
  combination of them. A general `f ∈ S_k` with complex coefficients is not covered:
  `Z(t)` is then not real up to a fixed phase.
- The Δ corollary is stated for `HeckeConvexGeneral.fL Δ`, not for `HeckeL.tauL`. The two
  agree, but that bridge is not formalized here. The direct Δ result is
  `HardyZeros.tauL_infinitely_many_critical_zeros`.
- `HardyZerosGeneral.Main` is included in the root import graph and theorem catalog.

## Literature

G. H. Hardy, C. R. Acad. Sci. Paris 158 (1914). For cusp forms see J. L. Hafner, *Zeros on the
critical line for Dirichlet series attached to certain cusp forms*, Math. Ann. 264 (1983), and
Iwaniec–Kowalski, *Analytic Number Theory*, Ch. 5.
