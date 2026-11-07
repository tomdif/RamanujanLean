/-
# Selberg's key lemma (SK) for `L(Δ,s)` — entry point

See `docs/SELBERG_KEY.md`.  Level 1: the shifted product AFE for `Z(u)Z(u')` (`ShiftAFE`), the
lag form of `∫ I²` (`Lag`), the exact expansion and diagonal split of `F(u)F(u+v)` (`Expand`).
Level 2: (SK) ⇐ `SKSplitHyp θ`, and the positive proportion ⇐ `QFHyp ∧ SKSplitHyp θ` (`Reduce`).
Statement only: the purely arithmetic `SKQFHyp θ` (`Arith`).
-/
import RamanujanTau.SelbergKey.Arith

open RamanujanTau.SelbergKey

#print axioms heckeLambda_mul_afe
#print axioms ISh_conj
#print axioms ISh_eq_tsum
#print axioms norm_Ush
#print axioms ZH_mul_ZH_afe
#print axioms intervalIntegral_swap
#print axioms weighted_shortInt_sq
#print axioms sk_le_weighted
#print axioms sk_le_lag
#print axioms wM_expand
#print axioms lag_product
#print axioms lag_split
#print axioms summable_sTerm
#print axioms Sl_sub_diagS
#print axioms lagInt_add
#print axioms weighted_eq_lagInt
#print axioms sk_of_split
#print axioms selbergMollHyp_of_QF_split
#print axioms tauL_positive_proportion_of_QF_split
#print axioms kap_one_one
