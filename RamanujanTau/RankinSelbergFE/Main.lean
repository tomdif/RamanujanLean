/-
# `RankinSelbergFE`: the Rankin–Selberg theorem proper for `Δ`, and the functional equation of
the completed real-analytic Eisenstein series `E*(z,s)`. See `docs/RANKIN_SELBERG_FE.md`.
-/
import RamanujanTau.RankinSelbergFE.Proper
import RamanujanTau.RankinSelbergFE.EpsteinE

-- Rankin–Selberg theorem proper
#print axioms RamanujanTau.RankinSelbergFE.RStar_one_sub
#print axioms RamanujanTau.RankinSelbergFE.RStar_eq
#print axioms RamanujanTau.RankinSelbergFE.differentiable_RStar₀
#print axioms RamanujanTau.RankinSelbergFE.RStar₀_one_sub
#print axioms RamanujanTau.RankinSelbergFE.differentiableAt_RStar
#print axioms RamanujanTau.RankinSelbergFE.RStar_residue_one
#print axioms RamanujanTau.RankinSelbergFE.RStar_residue_zero
#print axioms RamanujanTau.RankinSelbergFE.petNormSq_ne_zero
#print axioms RamanujanTau.RankinSelbergFE.RStar_eq_of_one_lt
#print axioms RamanujanTau.RankinSelbergFE.RStar_eq_of_one_lt'
#print axioms RamanujanTau.RankinSelbergFE.meromorphicAt_riemannZeta
#print axioms RamanujanTau.RankinSelbergFE.meromorphic_Rcont
#print axioms RamanujanTau.RankinSelbergFE.Rcont_eq
#print axioms RamanujanTau.RankinSelbergFE.differentiableAt_Rcont
#print axioms RamanujanTau.RankinSelbergFE.Rcont_residue_one
-- Lattice theta and Epstein / Eisenstein
#print axioms RamanujanTau.RankinSelbergFE.tsum_gauss_shift
#print axioms RamanujanTau.RankinSelbergFE.theta_inv
#print axioms RamanujanTau.RankinSelbergFE.nzEquiv
#print axioms RamanujanTau.RankinSelbergFE.im_inv_mat
#print axioms RamanujanTau.RankinSelbergFE.ofReal_Theta
#print axioms RamanujanTau.RankinSelbergFE.thetaFE
#print axioms RamanujanTau.RankinSelbergFE.EpsteinStar_one_sub
#print axioms RamanujanTau.RankinSelbergFE.differentiableAt_EpsteinStar
#print axioms RamanujanTau.RankinSelbergFE.EpsteinStar_residue_one
#print axioms RamanujanTau.RankinSelbergFE.EpsteinStar_residue_zero
#print axioms RamanujanTau.RankinSelbergFE.hasSum_EpsteinStar
#print axioms RamanujanTau.RankinSelbergFE.tsum_lq_rpow
#print axioms RamanujanTau.RankinSelbergFE.EpsteinStar_ofReal
