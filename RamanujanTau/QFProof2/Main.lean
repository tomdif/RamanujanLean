/-
# `QFProof2/` — discharging the hypotheses of `QFProof.qfHyp_of` (checkpoint; `docs/QF_PROOF.md`)

* `rhoP'_zero`, `rhoP'_succ` (level 1): `ρ'_p(a+1) = X log p · λ(p)λ(p^a)/(1+X)²` (gap 1 done).
* `sum_divisors_prod_local` (level 1): `Σ_{d|g} Π_{p|g} φ(p,v_p d) = Π_{p|g} Σ_{e≤v_p g} φ(p,e)`
  (the exchange step of gap 2).
-/
import RamanujanTau.QFProof2.RhoDeriv
import RamanujanTau.QFProof2.DivProd

#print axioms RamanujanTau.QFProof2.Np'_succ
#print axioms RamanujanTau.QFProof2.rhoP'_zero
#print axioms RamanujanTau.QFProof2.rhoP'_succ
#print axioms RamanujanTau.QFProof2.sum_divisors_prod_local
