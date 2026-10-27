exec(open('gen_cert_lean.py').read().split("# common:")[0])
OUT='../../../RamanujanTau/Atkin11Cert'
src=hdr("the meaning-level pieces (`g₂ = GN/GD`, `F_j = e_j Q^{k_j}`)","import RamanujanTau.SPoly")
for nm in ["GN","GD","F3","F4","F5","F6","F7","F8","F9","F10","F11"]:
    src+=defs(f"P{nm}", readp(f'{D}/P_{nm}.txt'))
src+=f"/-- `Q = −c₀c₁c₂c₄c₇`. -/\ndef PQ : SPoly.Poly := [({sum(1024**i for i in range(5))}, -1)]\n"
src+='''
open SPoly PE in
/-- the cleared identities as polynomial expressions. -/
def L (p : SPoly.Poly) : SPoly.PE := .lit p
open SPoly PE in
def Q5 : SPoly.PE := .pow (L PQ) 5
open SPoly PE in
def a3 : SPoly.PE := .add (.mul (.mul (.pow (L PGN) 2) (L PGD)) (L PF11)) (.smul 11 (.mul Q5 (.pow (L PGD) 3)))
open SPoly PE in
def a4 : SPoly.PE := .sub (.mul (.pow (L PGN) 3) (L PF11)) (.smul 11 (.mul Q5 (.pow (L PGD) 3)))
open SPoly PE in
def a2 : SPoly.PE := .mul (.mul (.mul (L PGN) (L PGD)) (.add (L PGD) (L PGN))) (L PF11)
open SPoly PE in
def az : SPoly.PE := .mul (.mul (.add (L PGD) (L PGN)) (.pow (L PGD) 2)) Q5
open SPoly PE in
def ae (F : SPoly.Poly) (k : ℕ) : SPoly.PE := .mul (.mul (.mul (.add (L PGD) (L PGN)) (.pow (L PGD) 2)) (.pow (L PQ) (5 - k))) (L F)
open SPoly PE in
def eE3 : SPoly.PE := .sub (L PF3) (.smul 121 (L PQ))
open SPoly PE in
def eE4 : SPoly.PE := .add (L PF4) (.smul 121 (L PQ))
open SPoly PE in
def eM6 : SPoly.PE := .sub (.sub (.smul 22 a4) (.smul 1331 az)) (ae PF5 2)
open SPoly PE in
def eM5 : SPoly.PE := .sub (.sub (.smul 242 a4) (.smul 1331 az)) (ae PF6 2)
open SPoly PE in
def eM4 : SPoly.PE := .sub (.add (.add (.smul 22 a3) (.smul 1452 a4)) (.smul 14641 az)) (ae PF7 3)
open SPoly PE in
def eM3 : SPoly.PE := .sub (.add (.add (.smul 242 a3) (.smul 5324 a4)) (.smul 73205 az)) (ae PF8 3)
open SPoly PE in
def eM2 : SPoly.PE := .sub (.add (.add (.add (.smul (-11) a2) (.smul 968 a3)) (.smul 11979 a4)) (.smul 161051 az)) (ae PF9 4)
open SPoly PE in
def eM1 : SPoly.PE := .sub (.add (.add (.add (.smul 121 a2) (.smul 2662 a3)) (.smul 14641 a4)) (.smul 161051 az)) (ae PF10 4)
open SPoly PE in
def eQU : SPoly.PE := .sub (.sub (.mul (.pow (L PGN) 5) (.pow (L PF11) 2))
    (.mul (.mul Q5 (L PF11)) (.add (.add (.pow (L PGD) 5) (.smul 13 (.mul (L PGN) (.pow (L PGD) 4))))
      (.smul 34 (.mul (.pow (L PGN) 2) (.pow (L PGD) 3))))))
  (.smul 121 (.mul (.pow (L PQ) 10) (.pow (L PGD) 5)))

end Atkin11Cert
'''
open(f'{OUT}/Pieces.lean','w').write(src)
def mono(fn):
    e,c=readp(fn)[0]; m=0
    for v in reversed(e): m=m*1024+v
    return m
TREE={"M2","M1","QU"}
FASTMEAN={"M3","M2","M1","QU"}  # run-based meaning check (the sort-based one needs >24 GB here)
for nm in ["E3","E4","M6","M5","M4","M3","M2","M1","QU"]:
    fm = nm in FASTMEAN
    src_imp=f"RamanujanTau.Atkin11Cert.{nm}T_S2" if nm in TREE else f"RamanujanTau.Atkin11Cert.{nm}"
    tname=f"{nm}_root" if nm in TREE else f"{nm}_T"
    s=hdr(f"meaning of {nm}",f"import {src_imp}\nimport RamanujanTau.Atkin11Cert.Pieces" + ("\nimport RamanujanTau.SPolyPE" if fm else ""))
    s+=f"theorem {nm}_mean : SPoly.{'eqCheckPER' if fm else 'eqCheckPE'} (SPoly.mulTerm {mono(f'{D}/{nm}_mc.txt')} 1 {tname}) e{nm} = true := by\n  decide +kernel\n\nend Atkin11Cert\n"
    fn=f'{OUT}/{nm}Mean.lean'
    if open(fn).read()!=s: open(fn,'w').write(s)
print("ok")
