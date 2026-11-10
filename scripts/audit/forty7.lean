import RamanujanTau.Forty.Defs
import RamanujanTau.Forty.Lattice
import RamanujanTau.Forty.E02
import RamanujanTau.Forty.E03
import RamanujanTau.Forty.E04
import RamanujanTau.Forty.E05
import RamanujanTau.Forty.E06
import RamanujanTau.Forty.E07
import RamanujanTau.Forty.E08
import RamanujanTau.Forty.E09
import RamanujanTau.Forty.E10
import RamanujanTau.Forty.E11
import RamanujanTau.Forty.E12
import RamanujanTau.Forty.E19
import RamanujanTau.Forty.E28
import RamanujanTau.Forty.E20
import RamanujanTau.Forty.E21
import RamanujanTau.Forty.E13
import RamanujanTau.Forty.E14
import RamanujanTau.Forty.E16
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.E25
import RamanujanTau.Forty.E30
import RamanujanTau.Forty.W41
import RamanujanTau.Forty.W41b
import RamanujanTau.Forty.E22
import RamanujanTau.Forty.R11
import RamanujanTau.Forty.E24
import RamanujanTau.Forty.E23
import RamanujanTau.Forty.E34
import RamanujanTau.Forty.QS
import RamanujanTau.Forty.E18
import RamanujanTau.Forty.E19ii
import RamanujanTau.Forty.E33
import RamanujanTau.Forty.E27
import RamanujanTau.Forty.E16iiA
import RamanujanTau.Forty.E16ii
import RamanujanTau.Forty.E32a
import RamanujanTau.Forty.E32
import RamanujanTau.Forty.E31
import RamanujanTau.Forty.E15
import RamanujanTau.Forty.E26a
import RamanujanTau.Forty.E26

#print axioms Forty.G_eq
#print axioms Forty.H_eq
#print axioms Forty.hs_split
#print axioms Forty.split_two
#print axioms Forty.θθ_lattice
#print axioms Forty.qf_two
#print axioms Forty.θ_bar0
#print axioms Forty.chip_mul
#print axioms Forty.entry_3_1
#print axioms Forty.entry_3_2
#print axioms Forty.entry_3_3
#print axioms Forty.entry_3_4
#print axioms Forty.entry_3_5
#print axioms Forty.entry_3_6
#print axioms Forty.entry_3_7
#print axioms Forty.entry_3_8
#print axioms Forty.entry_3_9
#print axioms Forty.entry_3_10
#print axioms Forty.entry_3_11
#print axioms Forty.entry_3_12
#print axioms Forty.entry_3_19_i
#print axioms Forty.entry_3_28_i
#print axioms Forty.entry_3_20
#print axioms Forty.entry_3_21
#print axioms Forty.entry_3_13
#print axioms Forty.entry_3_14
#print axioms Forty.entry_3_16_i
#print axioms Forty.entry_3_17
#print axioms Forty.entry_3_25
#print axioms Forty.entry_3_30
#print axioms Forty.entry_3_22
#print axioms Forty.entry_3_23
#print axioms Forty.entry_3_24
#print axioms Forty.lemma41a
#print axioms Forty.lemma41b
#print axioms Forty.entry_3_22_neg
#print axioms Forty.entry_3_23_neg
#print axioms Forty.entry_3_24_neg
#print axioms Forty.P11
#print axioms Forty.star1110
#print axioms Forty.star1110_neg
#print axioms Forty.lemma71
#print axioms Forty.P3_4
#print axioms Forty.P3_19
#print axioms Forty.P3_28
#print axioms Forty.lemma71_neg
#print axioms Forty.P23_1
#print axioms Forty.psi_mul
#print axioms Forty.quint1
#print axioms Forty.quintm
#print axioms Forty.dis2
#print axioms Forty.Ng_mul_odd
#print axioms Forty.NgG_prod
#print axioms Forty.NgH_prod
#print axioms Forty.P3_13
#print axioms Forty.P3_16
#print axioms Forty.P3_17
#print axioms Forty.P3_25
#print axioms Forty.P3_30
#print axioms Forty.entry_3_34
#print axioms Forty.entry_3_18
#print axioms Forty.entry_3_19_ii
#print axioms Forty.entry_3_33
#print axioms Forty.entry_3_33'
#print axioms Forty.entry_3_27_ii
#print axioms Forty.QS_of
#print axioms Forty.QS_cover
#print axioms Forty.qmono_cmap
#print axioms Forty.QS_sub
#print axioms Forty.QS_orth
#print axioms Forty.qmono_summ
#print axioms Forty.qmono_par
#print axioms Forty.L34a
#print axioms Forty.L34b
#print axioms Forty.L34d
#print axioms Forty.L33_6
#print axioms Forty.P33_6
#print axioms Forty.F1_J
#print axioms Forty.F2_J
#print axioms Forty.K1_eq
#print axioms Forty.K2_eq
#print axioms Forty.θ0_eq
#print axioms Forty.θm_eq
#print axioms Forty.L3_18
#print axioms Forty.P3_18
#print axioms Forty.L3_19ii
#print axioms Forty.P3_19ii
#print axioms Forty.S_comp
#print axioms Forty.dis3
#print axioms Forty.C6
#print axioms Forty.C7
#print axioms Forty.C8
#print axioms Forty.hN33
#print axioms Forty.hM33
#print axioms Forty.d33_1
#print axioms Forty.d33_2
#print axioms Forty.P29
#print axioms Forty.P30
#print axioms Forty.NM33
#print axioms Forty.entry_3_16_ii
#print axioms Forty.entry_3_16_ii'
#print axioms Forty.entry_3_16_ii_unique
#print axioms Forty.cc_3_16
#print axioms Forty.L16_1
#print axioms Forty.P16_1
#print axioms Forty.L16_2
#print axioms Forty.P16_2
#print axioms Forty.Q16
#print axioms Forty.core16
#print axioms Forty.brk16
#print axioms Forty.entry_3_32
#print axioms Forty.entry_3_31
#print axioms Forty.E32sq
#print axioms Forty.L32U
#print axioms Forty.L32T
#print axioms Forty.M32U
#print axioms Forty.M32T
#print axioms Forty.P32U
#print axioms Forty.P32T
#print axioms Forty.Z32
#print axioms Forty.Z32'
#print axioms Forty.NU31
#print axioms Forty.MT31
#print axioms Forty.entry_3_15_i
#print axioms Forty.prod15a
#print axioms Forty.prod15b
#print axioms Forty.eq_zero_of_S2
#print axioms Forty.L3_26
#print axioms Forty.M3_26
#print axioms Forty.P3_26
#print axioms Forty.M26chi
#print axioms Forty.M26chi2
#print axioms Forty.lemma41a_neg
#print axioms Forty.lemma41b_neg
#print axioms Forty.lemma41a_11
#print axioms Forty.lemma41b_11
#print axioms Forty.e34_16
#print axioms Forty.e34_neg
#print axioms Forty.e34_m4
#print axioms Forty.T26_expand
#print axioms Forty.T26_expand_neg
#print axioms Forty.P2_split
#print axioms Forty.P22_split
#print axioms Forty.T26_diff
#print axioms Forty.e320c
#print axioms Forty.e320c11
#print axioms Forty.T26_prod
#print axioms Forty.entry_3_26'
#print axioms Forty.entry_3_26
#print axioms Forty.entry_29_14
#print axioms Forty.star26_plus
#print axioms Forty.star26_minus
#print axioms Forty.entry_3_27_i
