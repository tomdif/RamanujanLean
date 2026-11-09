/-
Audit for Son's septic identities (docs/SEPTIC_SON.md).
Every theorem below must depend only on [propext, Classical.choice, Quot.sound].
-/
import RamanujanTau.Septic.SonPage206

set_option autoImplicit false

open RamanujanTau.Septic RamanujanTau.Septic.SonProof

example : SonSextic := sonSextic
example : SonEntryIII := sonEntryIII
example : SepticSonCore := septicSonCore
example : Page206Evaluation := page206_via_son

#print axioms RamanujanTau.Septic.SonProof.SB_identity
#print axioms RamanujanTau.Septic.SonProof.S7_identity
#print axioms RamanujanTau.Septic.SonProof.S6_identity
#print axioms RamanujanTau.Septic.SonProof.sonSextic
#print axioms RamanujanTau.Septic.SonProof.sonEntryIII
#print axioms RamanujanTau.Septic.SonProof.septicSonCore
#print axioms RamanujanTau.Septic.SonProof.page206_via_son
