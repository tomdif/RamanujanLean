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
import RamanujanTau.Forty.E29a
import RamanujanTau.Forty.E29b
import RamanujanTau.Forty.E29c
import RamanujanTau.Forty.E29d
import RamanujanTau.Forty.E29
import RamanujanTau.Forty.E28b
import RamanujanTau.Forty.E28c
import RamanujanTau.Forty.E35b
import RamanujanTau.Forty.E35c
import RamanujanTau.Forty.E35
import RamanujanTau.Forty.E28d
import RamanujanTau.Forty.E28e
import RamanujanTau.Forty.E28f
import RamanujanTau.Forty.E28g
import RamanujanTau.Forty.E28ii
import RamanujanTau.Forty.E35d
import RamanujanTau.Forty.E35e
import RamanujanTau.Forty.E35f
import RamanujanTau.Forty.E35g
import RamanujanTau.Forty.E35h

/-! Round 8 audit: all proved entries (rounds 1–8) and the round-8 lemmas.
Expected for every line: `[propext, Classical.choice, Quot.sound]`. -/
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
#print axioms Forty.M23
#print axioms Forty.L23
#print axioms Forty.P23
#print axioms Forty.LA23
#print axioms Forty.LB23
#print axioms Forty.LC23
#print axioms Forty.S23a
#print axioms Forty.S23b
#print axioms Forty.S23c
#print axioms Forty.S23r
#print axioms Forty.S23s
#print axioms Forty.S23t
#print axioms Forty.L29p
#print axioms Forty.L29m
#print axioms Forty.D5p_eq
#print axioms Forty.D5m_eq
#print axioms Forty.Yo_c
#print axioms Forty.Ye_c
#print axioms Forty.D5p_c
#print axioms Forty.D5m_c
#print axioms Forty.Ng_S_odd8
#print axioms Forty.R44a
#print axioms Forty.R44b
#print axioms Forty.K1
#print axioms Forty.R46a
#print axioms Forty.R46b
#print axioms Forty.GNgG
#print axioms Forty.HNgH
#print axioms Forty.NgE33
#print axioms Forty.E21c
#print axioms Forty.GH2
#print axioms Forty.S_S8
#print axioms Forty.Yo_ι
#print axioms Forty.Ye_ι
#print axioms Forty.D5p_ι
#print axioms Forty.D5m_ι
#print axioms Forty.Ng_A29
#print axioms Forty.E1_29
#print axioms Forty.E2_29
#print axioms Forty.entry_3_29
#print axioms Forty.L28p
#print axioms Forty.L28m
#print axioms Forty.A4p_eq
#print axioms Forty.A4m_eq
#print axioms Forty.A4p_c
#print axioms Forty.A4m_c
#print axioms Forty.B5p_c
#print axioms Forty.B5m_c
#print axioms Forty.A4p_ι
#print axioms Forty.A4m_ι
#print axioms Forty.B5p_ι
#print axioms Forty.B5m_ι
#print axioms Forty.E28p
#print axioms Forty.E28m
#print axioms Forty.L47p
#print axioms Forty.L47m
#print axioms Forty.D5p47_eq
#print axioms Forty.D5m47_eq
#print axioms Forty.Yo47_c
#print axioms Forty.Ye47_c
#print axioms Forty.D5p47_c
#print axioms Forty.D5m47_c
#print axioms Forty.Yo47_ι
#print axioms Forty.Ye47_ι
#print axioms Forty.D5p47_ι
#print axioms Forty.D5m47_ι
#print axioms Forty.E1_47
#print axioms Forty.E2_47
#print axioms Forty.entry_3_35_AB
-- round 9: Entry 3.28(ii)
#print axioms Forty.core28
#print axioms Forty.alg28
#print axioms Forty.glue1
#print axioms Forty.glue2
#print axioms Forty.glue3
#print axioms Forty.alg5
#print axioms Forty.alg27
#print axioms Forty.alg6
#print axioms Forty.alg4
#print axioms Forty.Y14
#print axioms Forty.Y13A
#print axioms Forty.Y21
#print axioms Forty.Y15
#print axioms Forty.phi_dis
#print axioms Forty.Y1
#print axioms Forty.Y13Am
#print axioms Forty.Y14m
#print axioms Forty.Y14q
#print axioms Forty.Y14m2
#print axioms Forty.Y14q4
#print axioms Forty.Y2
#print axioms Forty.Y3
#print axioms Forty.Y1q2
#print axioms Forty.Y5
#print axioms Forty.J23
#print axioms Forty.J23r
#print axioms Forty.J23Q
#print axioms Forty.Y4
#print axioms Forty.P28
#print axioms Forty.Y6
#print axioms Forty.Y6m
#print axioms Forty.Y6q2
#print axioms Forty.πG
#print axioms Forty.πNgG
#print axioms Forty.πS2G
#print axioms Forty.four_x2_ne
#print axioms Forty.hbr28
#print axioms Forty.Y8q2
#print axioms Forty.entry_3_28_ii'
#print axioms Forty.entry_3_28_ii
-- round 9: toward Entry 3.35 (level-47 eta-theta identity)
#print axioms Forty.S47a
#print axioms Forty.S47b
#print axioms Forty.S47c
#print axioms Forty.S47r
#print axioms Forty.S47s
#print axioms Forty.S47t
#print axioms Forty.LA47
#print axioms Forty.LB47
#print axioms Forty.LC47
#print axioms Forty.L47
-- round 10: Entry 3.35 (E35e-E35h)
#print axioms Forty.isUnit_J
#print axioms Forty.ι_ne_zero_of_unit
#print axioms Forty.map_inverse_unit
#print axioms Forty.fb_mul
#print axioms Forty.fb0_mul
#print axioms Forty.θfb
#print axioms Forty.θfb0
#print axioms Forty.S_fb
#print axioms Forty.S_fb0
#print axioms Forty.J_Ng_J
#print axioms Forty.Ng_fb_odd
#print axioms Forty.Ng_fb_even
#print axioms Forty.Ng_fb0
#print axioms Forty.S2X
#print axioms Forty.E47
#print axioms Forty.SR3y
#print axioms Forty.SR3y0p
#print axioms Forty.SR3y0m
#print axioms Forty.SR3y1
#print axioms Forty.SR3w
#print axioms Forty.SR3wy
#print axioms Forty.SR3v
#print axioms Forty.SR3va
#print axioms Forty.SR3vb
#print axioms Forty.LRY1
#print axioms Forty.LRY0m
#print axioms Forty.LRW2
#print axioms Forty.LRW3
#print axioms Forty.LRW33
#print axioms Forty.SR2y
#print axioms Forty.SR2z1p
#print axioms Forty.SR2z1m
#print axioms Forty.SR2w
#print axioms Forty.SR2wy
#print axioms Forty.LRZ0
#print axioms Forty.LRZ1m
#print axioms Forty.LRW22
#print axioms Forty.SkX
#print axioms Forty.S_fb_s
#print axioms Forty.S_fb0_s
#print axioms Forty.Ng_fb_ev
#print axioms Forty.Ng_fb0_ev
#print axioms Forty.Ng_T3
#print axioms Forty.Ng_T2
#print axioms Forty.R3
#print axioms Forty.R2
#print axioms Forty.LphA
#print axioms Forty.LphB
#print axioms Forty.phi_sq
#print axioms Forty.a22
#print axioms Forty.fb12_eq
#print axioms Forty.fb14_mul
#print axioms Forty.fb28_eq
#print axioms Forty.fb12_fb02
#print axioms Forty.J13_eq
#print axioms Forty.E518
#print axioms Forty.M47
#print axioms Forty.chim_w47
#print axioms Forty.isUnit_v47
#print axioms Forty.isUnit_w47
#print axioms Forty.entry_3_35
#print axioms Forty.π2_eq
#print axioms Forty.π2_zero
#print axioms Forty.hx2
#print axioms Forty.hx2n
#print axioms Forty.π2Pinf
#print axioms Forty.π2S
#print axioms Forty.cc_u47
#print axioms Forty.cc_v47
#print axioms Forty.π2_u47
#print axioms Forty.π2_v47
#print axioms Forty.entry_3_35_root
#print axioms Forty.entry_3_35_unique
