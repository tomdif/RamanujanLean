import RamanujanTau.AtkinTwisted.All

open RamanujanTau.AtkinTwisted

#print axioms eigen_of_coeffs
#print axioms eigen_of_allOk
#print axioms vanish_ono
#print axioms etaHeckeMod
#print axioms G1.cert
#print axioms G2.cert
#print axioms G3.cert
#print axioms G4.cert
#print axioms allPairs_cover
#print axioms eigen_all
#print axioms G1.atkin_13_11_class
#print axioms G1.atkin_13_11
#print axioms G1.atkin_13_37_class
#print axioms G1.atkin_13_37
#print axioms G1.atkin_13_89_class
#print axioms G1.atkin_13_89
#print axioms G1.ono_13_103_class
#print axioms G1.ono_13_103
#print axioms G2.atkin_13_167_class
#print axioms G2.atkin_13_167
#print axioms G2.ono_13_181_class
#print axioms G2.ono_13_181
#print axioms G2.atkin_13_193_class
#print axioms G2.atkin_13_193
#print axioms G2.ono_13_233_class
#print axioms G2.ono_13_233
#print axioms G3.atkin_13_271_class
#print axioms G3.atkin_13_271
#print axioms G3.ono_13_311_class
#print axioms G3.ono_13_311
#print axioms G3.ono_13_337_class
#print axioms G3.ono_13_337
#print axioms G3.atkin_13_349_class
#print axioms G3.atkin_13_349
#print axioms G4.ono_13_389_class
#print axioms G4.ono_13_389
#print axioms G4.atkin_13_401_class
#print axioms G4.atkin_13_401
#print axioms G4.ono_13_467_class
#print axioms G4.ono_13_467
#print axioms G4.atkin_13_479_class
#print axioms G4.atkin_13_479

-- negative controls (kernel-checked): a wrong eigenvalue fails the Sturm certificate
example : allOk 262132 1695 8 1 11 4 18 33 [(11, 4)] = false := by decide +kernel
example : allOk 262132 1695 8 1 11 4 18 33 [(11, 3)] = true := by decide +kernel
example : allOk 262132 19167 8 1 15 4 18 37 [(37, 4)] = false := by decide +kernel

