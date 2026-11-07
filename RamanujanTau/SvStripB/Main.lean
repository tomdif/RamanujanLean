/-
# `SvStripB`: the twisted smoothed sums `J_z` (step 4/5 of `docs/SKQF_PROOF.md` §4), level 1

* `Jz z x = Σ_{m≤x} (fR(m)/m) e^{iz log m} log(x/m)` (`Jz_eq_cpow`: `= Σ fR(m) m^{−(1−iz)} log(x/m)`);
  `Jz_zero`: `J_0 = Isum fR`.
* `Jz_differentiable`: `z ↦ J_z(x)` is entire.
* `Ssum_bound`: `|Σ_{m≤u} fR(m)/m| ≤ K/√(1+log u)` (first clause of `selberg_sum_fR`).
* `Jz_eq_integral`: Abel summation, `J_z(x) = −∫_{(1,x]} φ'(u) S(u) du`.
* `Jz_bound`: `|J_z(x)| ≤ K √(1+log x)(1+|z| log x) x^{|Im z|}` for all `z ∈ ℂ`, `x ≥ 1`.
* `Jz_bound_re`: `|J_z(x)| ≤ K √(1+log x)(1+|Re z| log x) x^{2|Im z|}`.
* `Jz_div_bound`, `yd_bound`, `yd_bound_div`, `yd_holo`: the form used by step 4.
-/
import RamanujanTau.SvStripB.Downstream

open RamanujanTau.SvStripB

#print axioms Jz_zero
#print axioms Jz_eq_cpow
#print axioms Jz_differentiable
#print axioms Ssum_bound
#print axioms Jz_eq_integral
#print axioms Jz_bound
#print axioms Jz_bound_rpow
#print axioms Jz_bound_re
#print axioms Jz_div_bound
#print axioms yd_bound
#print axioms yd_bound_div
#print axioms yd_holo
