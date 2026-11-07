/-
# M3 (diagonal Mellin evaluation) — entry point

* `Residue`: residue at a pole `iβ` on the imaginary axis (`vline_residue_at`);
* `Mellin`, `Mellin2`, `Remainder`: `∫₁^∞ x^{iv−1} W̃(αx²) dx = (G(iv/2)α^{−iv/2}e^{−v²/4} − 1)/(iv) + O((α/TT)^{1/6})`;
* `Base1`–`Base3`: `Σ (λ(n)²/n) n^{iv} W̃(αn²) = γ W̃(α) + c₀ J(α) − iv ε(v) + O((α/TT)^{1/20})`.
See `docs/SELBERG_KEY.md` (2026-11-06, M3 section).
-/
import RamanujanTau.SelbergKeyDiag2.Remainder
import RamanujanTau.SelbergKeyDiag2.Base3
import RamanujanTau.SelbergKeyDiag2.Final5

open RamanujanTau.SelbergKeyDiag2

#print axioms vline_residue_at
#print axioms mellin_line2
#print axioms vline_fM_residues
#print axioms mellin_Wsh
#print axioms norm_Rsh_le
#print axioms norm_xi_Wd_small
#print axioms hasDerivAt_ft
#print axioms base_abel
#print axioms Et_bound
#print axioms base_eval
#print axioms base_full
#print axioms evC_gps
#print axioms Bs_peel
#print axioms hasSum_Mn_peel
#print axioms Inv_peel
#print axioms twisted_eval
#print axioms ray_term
#print axioms diag_quad
#print axioms phase_U
#print axioms phase_Phi
#print axioms diagLag_eq
#print axioms UXm_sub_Av
#print axioms S_bounds
#print axioms diag_pointwise
#print axioms diagApproxHyp_small
#print axioms diagHypT_of_SKQF'
#print axioms sk_of_SKQF'
#print axioms tauL_positive_proportion_of_SKQF'
