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

/-! Ramanujan's forty identities (Berndt et al., Mem. AMS 880, Sec. 3): axiom audit of every proved entry
(round 1: 3.1–3.12, 3.19(i), 3.28(i); round 2: 3.20, 3.21). -/

-- definitions and the Rogers–Ramanujan product forms
#print axioms Forty.G_eq
#print axioms Forty.H_eq

-- the engine: matrix exact covers, products of two thetas, binary quadratic forms
#print axioms Forty.hs_split
#print axioms Forty.split_two
#print axioms Forty.θθ_lattice
#print axioms Forty.qf_two
#print axioms Forty.θ_bar0
#print axioms Forty.chip_mul

-- the entries
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

-- auxiliary theta-function identities
#print axioms Forty.lemma71
#print axioms Forty.P3_4
#print axioms Forty.P3_19
#print axioms Forty.P3_28
#print axioms Forty.lemma71_neg
#print axioms Forty.P23_1
#print axioms Forty.psi_mul
