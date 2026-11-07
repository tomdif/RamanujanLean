# Zeros of L(Δ,s): localization to the closed critical strip

Lean: `RamanujanTau/HeckeZeros/{EulerProduct,Zeros,Main}.lean` (namespace `RamanujanTau.HeckeZeros`).
Build: `lake build RamanujanTau.HeckeZeros.Main`. Not imported from the root `RamanujanTau.lean`.

Coordinates are unnormalized: weight 12, `tauL s = (2π)^s Γ(s)⁻¹ Λ(s)` (entire continuation,
`HeckeL/Main.lean`), functional equation `Λ(12 − s) = Λ(s)`, critical line `Re s = 6`,
critical strip `11/2 ≤ Re s ≤ 13/2`.

## Results (evidence level 1: Lean, axiom-clean `[propext, Classical.choice, Quot.sound]`)

| Theorem | Statement |
|---|---|
| `LSeries_tau_eulerProduct_of_gt` | `13/2 < s.re → HasProd (fun p : Nat.Primes => (1 - τ(p) p^{-s} + p^11 (p^{-s})^2)⁻¹) (LSeries tauC s)` |
| `tauL_eulerProduct` | same product, with limit `tauL s` |
| `tauL_ne_zero_of_gt` | `13/2 < s.re → tauL s ≠ 0` |
| `LSeries_tau_ne_zero_of_gt` | `13/2 < s.re → LSeries tauC s ≠ 0` |
| `heckeLambda_ne_zero_of_gt` / `_of_lt` | `Λ(s) ≠ 0` for `Re s > 13/2` and for `Re s < 11/2` |
| `tauL_eq_zero_iff_of_lt` | `s.re < 11/2 → (tauL s = 0 ↔ ∃ n : ℕ, s = -n)` |
| **`tauL_zeros_in_strip`** | `tauL s = 0 → (∀ n : ℕ, s ≠ -n) → 11/2 ≤ s.re ∧ s.re ≤ 13/2` |
| `tauL_zero_twelve_sub` | non-trivial zero `s` ⇒ `tauL (12 - s) = 0` and `12 - s` non-trivial |
| `heckeLambda_conj`, `tauL_conj` | `Λ(conj s) = conj Λ(s)`, `tauL (conj s) = conj (tauL s)` |
| `tauL_zero_conj` | `tauL s = 0 → tauL (conj s) = 0` |

## Proof outline

1. **Euler product on Re s > 13/2.** The existing `LSeries_tau_eulerProduct` (Re s > 7, Hecke's bound)
   is re-run with Rankin's absolute convergence `HeckeConvex.LSeriesSummable_tau_of_gt_13_2`; the local
   factor identity `P_p(s) · Σ_e τ(p^e)p^{-es} = 1` (`localPoly_mul_tsum`) uses the Hecke recurrence;
   multiplicativity is `tau_mul_coprime` (Mordell); Mathlib's `EulerProduct.eulerProduct_hasProd`.
2. **Non-vanishing.** `Σ_p ‖P_p(s) − 1‖ ≤ Σ_p |τ(p)|p^{-σ} + Σ_p p^{11−2σ} < ∞` (the first from Rankin,
   the second since `2σ − 11 > 2`). Mathlib's `tprod_one_add_ne_zero_of_summable` gives `∏ P_p ≠ 0`, and
   `(∏ P_p)·tauL(s) = ∏ (P_p·P_p⁻¹) = 1` by `HasProd.mul` + uniqueness.
3. **Left half-plane.** `Λ(s) = Λ(12 − s) = (2π)^{s−12} Γ(12 − s) tauL(12 − s) ≠ 0` for `Re s < 11/2`,
   so `tauL s = (2π)^s Γ(s)⁻¹ Λ(s)` vanishes exactly where `Γ(s)⁻¹` does, i.e. at `s ∈ {0, −1, −2, …}`
   (`Complex.Gamma_eq_zero_iff`).
4. **Conjugation.** `Λ` is the Mellin transform of the real function `t ↦ Δ(it)` (`heckeF_real`), so
   `Λ(conj s) = conj Λ(s)` via `integral_conj` and `cpow_conj`; with `Gamma_conj`, `tauL` commutes with `conj`.

## Gaps (not proved here)

* **Non-vanishing on the edges `Re s = 13/2` (equivalently `Re s = 11/2`).** This is the
  prime-number-theorem-type statement for `L(Δ,s)`; the standard proof needs analytic properties of the
  symmetric square `L(Sym² Δ, s)` (Shimura 1975 holomorphy; Ogg 1969, Moreno 1974 / Jacquet–Shalika 1976
  non-vanishing on the edge). **Update (2026-11-05): proved without Sym² or Deligne** in
  [EDGE_NONVANISHING](EDGE_NONVANISHING.md) (`EdgeNonvanishing.tauL_ne_zero_edge`); with
  `tauL_ne_zero_of_ge` / `tauL_ne_zero_of_le` the nontrivial zeros lie in the **open** strip `11/2 < Re s < 13/2`.
* **Zero-free region / RH for L(Δ,s)** (`Re s = 6` for all non-trivial zeros): open (GRH).
* **Existence/counting of zeros** (Riemann–von Mangoldt `N(T) ~ (T/π) log(T/2πe)`-type formula): not done. (Existence on the critical line is now proved, with ≫ T/log log T zeros up to T: [HARDY_ZEROS](HARDY_ZEROS.md), [HARDY_COUNT_LINEAR](HARDY_COUNT_LINEAR.md).)
* The trivial zeros `s = −n` are simple and are exactly the real zeros (`tauL_real_eq_zero_iff`,
  `HeckeL/Positivity.lean`); multiplicity is not formalized.
