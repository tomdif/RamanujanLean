/-
# `SubconvexGeneral/`: t-aspect subconvexity for `L(f,s)`, `f ∈ S_k(SL₂(ℤ))` — milestone

Build: `nice -n 10 lake build RamanujanTau.SubconvexGeneral.Main`.  See `docs/SUBCONVEX_GENERAL.md`.

Proved (level 1, axiom-clean):

* `fL_subconvex_of_SCSf` (general reduction): for every level-one cusp form `f` of weight `k` with
  real coefficients, `SCS_f(η,B)` (`0 < η ≤ 1/2`, `B ≥ 0`) implies
  `‖L(f, k/2+it)‖ ≤ C (1+|t|)^{1/2 − δ₂}`, `δ₂ = η/((1+u)(4B+6+2η))` — the *same* exponent as
  for `Δ` (`SCSSharp2.tauL_subconvex_of_SCS2`).
* `fL_subconvex_eigen_of_SCSf`, `exists_subconvex_of_SCSf`: every normalized Hecke eigenform.
* `fL_discriminant_subconvex`: the general pipeline at `k = 12` gives `δ = 1/134` for `L(Δ,6+it)`
  unconditionally (consistency check: weight-parametrization does not change exponents).
* `scsf_trivial`: `SCS_f(0,0)` for every `f`; `approx_fL` (Riesz–Perron at `σ = k/2`).
* Δ-specific core of the SCS proof, generalized: `PsiF_smul`, `norm_PsiF_le`, `coeff_PsiF`
  (two-point invariant `(z − w̄)^k f(z) conj f(w)`), `coef_sq_laplace` (Parseval `σ^{−k}`).

Open (level 3, paper + cost estimate in the doc): the instance `SCSf f (1/21) (1/21)` for general
`f`, i.e. the weight-`k` copy of `SCSProof`/`SCSSharp`/`SCSSharp2` downstream of `TwoPoint`.
-/
import RamanujanTau.SubconvexGeneral.Check
import RamanujanTau.SubconvexGeneral.GboundsF

#print axioms RamanujanTau.SubconvexGeneral.scsf_trivial
#print axioms RamanujanTau.SubconvexGeneral.sum_nlam_sq_div_le
#print axioms RamanujanTau.SubconvexGeneral.mean_value_boundG
#print axioms RamanujanTau.SubconvexGeneral.approx_fL
#print axioms RamanujanTau.SubconvexGeneral.dpoly_bsmF_eq
#print axioms RamanujanTau.SubconvexGeneral.rpoly_boundF
#print axioms RamanujanTau.SubconvexGeneral.fL_subconvex_of_SCSf
#print axioms RamanujanTau.SubconvexGeneral.fL_subconvex_eigen_of_SCSf
#print axioms RamanujanTau.SubconvexGeneral.exists_subconvex_of_SCSf
#print axioms RamanujanTau.SubconvexGeneral.nlam_discriminant
#print axioms RamanujanTau.SubconvexGeneral.scsf_discriminant
#print axioms RamanujanTau.SubconvexGeneral.fL_discriminant_subconvex
#print axioms RamanujanTau.SubconvexGeneral.PsiF_smul
#print axioms RamanujanTau.SubconvexGeneral.norm_PsiF_le
#print axioms RamanujanTau.SubconvexGeneral.coeff_PsiF
#print axioms RamanujanTau.SubconvexGeneral.coef_sq_laplace
