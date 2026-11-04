import RamanujanTau.AtkinSporadic.Atkin13Main
import RamanujanTau.AtkinSporadic.WeaverMain
open RamanujanTau.AtkinSporadic
-- unconditional
#print axioms Twist13.twisted_eq
#print axioms Weaver.Pser_eq
#print axioms Atkin13.chk11
#print axioms Atkin13.chk37
#print axioms Weaver.chk_13_59
#print axioms Weaver.chk_17_103
-- conditional on the named hypothesis `EtaHecke`
#print axioms Atkin13.twisted_hecke
#print axioms Atkin13.vanish_of_eigen
#print axioms Atkin13.atkin_13
#print axioms Atkin13.atkin_13_class
#print axioms Atkin13.atkin_13_Q37_class
#print axioms Weaver.weaver_index
#print axioms Weaver.ono_13
#print axioms Weaver.weaver_17
#print axioms Weaver.ono_13_73
#print axioms Weaver.ono_17_89
#print axioms Weaver.ono_17_103
#print axioms Weaver.ono_19_101
#print axioms Weaver.ono_23_5
#print axioms Weaver.ono_23_19
#print axioms Weaver.ono_23_37
#print axioms Weaver.ono_23_47
#print axioms Weaver.ono_23_67
-- negative controls: wrong eigenvalue / non-vanishing prime must fail the certificates
example : Atkin13.chk 11 4 1700 33 = false := by decide +kernel
example : Atkin13.chk 37 4 19200 113 = false := by decide +kernel
instance : Fact (Nat.Prime 61) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 43) := ⟨by norm_num⟩
example : Weaver.wchk 13 61 22172 121 = false := by decide +kernel
example : Weaver.wchk 17 43 9169 78 = false := by decide +kernel
#check @Atkin13.atkin_13
#check @Weaver.ono_13
#check @Weaver.weaver_17
#check @Weaver.ono_23_5
#print EtaHecke
#print axioms EtaHecke.toMod
#check @Atkin13.atkin_13
