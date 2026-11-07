/-
# GORZ for the Riemann Ξ-function and for general sequences — headline statements and axiom audit

* M1 (abstract GORZ): `GORZXi.thm6_coeff`, `GORZXi.thm6_uniform` (Theorem 6), `GORZXi.gorz_thm3`,
  `GORZXi.gorz_thm3_arxiv` (Theorem 3 + Corollary), `GORZXi.gorz_thm3_diff` (difference form),
* M2 (Riemann's formula from Mathlib): `GORZXi.completedRiemannZeta₀_eq`, `GORZXi.gammaMathlib_eq`.
* M4 (GORZ Theorem 1 for Ξ, conditional on the named hypothesis `XiKernelHyp`): `GORZXi.xi_gorz_mathlib`.
-/
import RamanujanTau.GORZXi.XiTaylor
import RamanujanTau.GORZXi.Partition

set_option autoImplicit false

#print axioms GORZXi.thm6_coeff
#print axioms GORZXi.thm6_uniform
#print axioms GORZXi.gorz_thm3
#print axioms GORZXi.gorz_thm3_arxiv
#print axioms GORZXi.gorz_thm3_diff
#print axioms GORZXi.partition_gorz
#print axioms GORZXi.completedRiemannZeta₀_eq
#print axioms GORZXi.gammaMathlib_eq
#print axioms GORZXi.xi_gorz
#print axioms GORZXi.xi_gorz_mathlib
