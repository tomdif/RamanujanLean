/-
# The prime number theorem for `τ` with the de la Vallée-Poussin error term

See `docs/TAU_PNT_ERROR.md`.
* `landau_pf` — Landau's lemma in partial-fraction form (any analytic `f`).
* `negLogDeriv_bound` — `L(s) ≠ 0` and `‖L'/L(s)‖ ≤ C log²(|t|+2)` on `σ ≥ 1 − c/log(|t|+2)`
  (unconditional).
* `perron_shift`, `contour_bound` — Perron for the Riesz mean and the contour shift.
* `smoothed_bound` — `‖Σ Λ_Δ(n)(1 − n/x)₊‖ ≤ K x exp(−a√log x)` (unconditional).
* `F1_bound_vM` — `‖Σ_{n≤x} Λ_Δ(n)(x − n)‖ ≤ K x² exp(−a√log x)` (unconditional).
* `sum_abs_vH_le` — `Σ_{n≤N} |Λ_Δ(n)|·[n = p^k, k ≥ 2] ≤ C N^{9/10}` (unconditional).
* `psiDelta_error_uncond` — `|Σ_{n≤x} Λ_Δ(n)| ≤ K x exp(−b√log x)` (unconditional).
* `tau_PNT_error_uncond` — `|Σ_{p≤N} τ(p)p^{−11/2} log p| ≤ K N exp(−b√log N)` (unconditional).
* `tau_PNT_tau_error_uncond` — `|Σ_{p<N} τ(p) log p| ≤ K N^{13/2} exp(−b√log N)` (unconditional).
* Deligne versions (earlier, superseded): `psiDelta_error`, `tau_PNT_error`, `tau_PNT_tau_error`.
* `psiDelta_error` — `|Σ_{n≤x} Λ_Δ(n)| ≤ K x exp(−b√log x)` (`[DeligneBound]`).
* `tau_PNT_error` — `|Σ_{p≤N} τ(p)p^{−11/2} log p| ≤ K N exp(−b√log N)` (`[DeligneBound]`).
* `tau_PNT_tau_error` — `|Σ_{p<N} τ(p) log p| ≤ K N^{13/2} exp(−b√log N)` (`[DeligneBound]`).
-/
import RamanujanTau.TauPNTError.Uncond

#print axioms RamanujanTau.TauPNTError.landau_pf
#print axioms RamanujanTau.TauPNTError.negLogDeriv_bound
#print axioms RamanujanTau.TauPNTError.perron_shift
#print axioms RamanujanTau.TauPNTError.contour_bound
#print axioms RamanujanTau.TauPNTError.smoothed_bound
#print axioms RamanujanTau.TauPNTError.F1_bound_vM
#print axioms RamanujanTau.TauPNTError.psiDelta_error
#print axioms RamanujanTau.TauPNTError.tau_PNT_error
#print axioms RamanujanTau.TauPNTError.tau_PNT_tau_error
#print axioms RamanujanTau.TauPNTError.sum_abs_vH_le
#print axioms RamanujanTau.TauPNTError.F1_bound_vP
#print axioms RamanujanTau.TauPNTError.A_vP_error
#print axioms RamanujanTau.TauPNTError.psiDelta_error_uncond
#print axioms RamanujanTau.TauPNTError.tau_PNT_error_uncond
#print axioms RamanujanTau.TauPNTError.tau_PNT_tau_error_uncond
