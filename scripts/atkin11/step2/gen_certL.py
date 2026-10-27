exec(open('tree_cert.py').read().split('if __name__')[0])
names=["E3","E4","M6","M5","M4","M3","M2","M1","QU"]
TREE=["M2","M1","QU"]; sat={"E3":1,"E4":1}
imports="\n".join(f"import RamanujanTau.Atkin11Cert.{n}Mean" for n in names)
s=f'''/-
# Atkin 11^k: the certified theta identities at the theta point

For each certified identity `X`: the Gröbner certificate (single check, or a tree of unit products and
partial sums) and the vanishing of the Gröbner basis at the theta point give `X_T(c) = 0`; the meaning check
(`X_mean`) turns this into the cleared identity `eX.eval c = 0`.
-/
import RamanujanTau.Atkin11CertEval
import RamanujanTau.SPolyFast
{imports}

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ALz11
open HahnSeries ALz SPoly Atkin11Cert

section Ident
variable {{N : ℕ}} (hN : 1 ≤ N) {{d : ℕ}} (hd : N = 11 * d)
include hN hd

lemma cx_ne : ∀ v ∈ cx hN hd, v ≠ 0 := by
  have h1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have h2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have h3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have h4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have h5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hQ := Qt_ne hd
  intro v hv
  simp only [cx, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact div_ne_zero h4 h2
  · exact neg_ne_zero.mpr (div_ne_zero h2 h1)
  · exact neg_ne_zero.mpr (div_ne_zero h5 h3)
  · exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hQ h1) h5)
  · exact div_ne_zero h3 h4

omit hN hd in
lemma evalL_ne (x : List L) (hx : ∀ v ∈ x, v ≠ 0) : ∀ e : List ℕ, evalL x e ≠ 0 := by
  induction x with
  | nil => intro e; simp [evalL]
  | cons y ys ih =>
    intro e
    cases e with
    | nil => simp [evalL]
    | cons a es =>
      simp only [evalL]
      exact mul_ne_zero (pow_ne_zero _ (hx y (List.mem_cons_self ..)))
        (ih (fun v hv => hx v (List.mem_cons_of_mem _ hv)) es)

lemma evalM_cx_ne (m : ℕ) : evalM (cx hN hd) m ≠ 0 := evalL_ne _ (cx_ne hN hd) _

'''
gz=", ".join(f"G{j}_zero hN hd" for j in range(1,26))
for nm in names:
    k=sat.get(nm,0)
    if nm in TREE:
        units,tree=build(nm)
        for u,(j,piece,R) in enumerate(units):
            s+=f'''lemma {nm}_R{u}_zero : evalP (cx hN hd) {nm}_R{u} = 0 := by
  rw [{"certify_sound" if nm=="QU" else "certifyR_sound"} _ _ _ {nm}_R{u}_ok]; simp [G{j}_zero hN hd]

'''
        prev=[f"{nm}_R{u}" for u in range(len(units))]
        for lv,(groups,nxt) in enumerate(tree):
            last=lv==len(tree)-1; cur=[]; idx=0
            for kk,g in enumerate(groups):
                ch=prev[idx:idx+len(g)]; idx+=len(g)
                name=f"{nm}_S{lv}_{kk}" if not last else f"{nm}_root"
                if nm=="QU" and not last:
                    s+=f'''lemma {name}_zero : evalP (cx hN hd) {name} = 0 := by
  rw [← eqCheck_sound _ _ _ {name}_ok]
  simp only [evalP_append, {", ".join(f"{c}_zero hN hd" for c in ch)}, add_zero]

'''
                    cur.append(name); continue
                s+=f'''lemma {name}_zero : evalP (cx hN hd) {name} = 0 := by
  rw [eqRuns_sound _ _ _ {name}_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, {", ".join(f"{c}_zero hN hd" for c in ch)}, add_zero]

'''
                cur.append(name)
            prev=cur
        tz=f"{nm}_root_zero hN hd"; tn=f"{nm}_root"
        s+=f'''theorem {nm}_eval : e{nm}.eval (cx hN hd) = 0 := by
  rw [{f'← {nm}_meanE' if nm in ('M3','M2','M1','QU') else f'← eqCheckPE_sound _ _ _ {nm}_mean'}, evalP_mulTerm _ _ _ _ (by decide +kernel), {tz}, mul_zero]

'''
    elif k==0:
        s+=f'''theorem {nm}_eval : e{nm}.eval (cx hN hd) = 0 := by
  have hT : evalP (cx hN hd) {nm}_T = 0 := by
    rw [certify_sound _ _ _ {nm}_ok]
    simp [{gz}]
  rw [{f'← {nm}_meanE' if nm in ('M3','M2','M1','QU') else f'← eqCheckPE_sound _ _ _ {nm}_mean'}, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

'''
    else:
        mm=sum(k*1024**i for i in range(5))
        s+=f'''theorem {nm}_eval : e{nm}.eval (cx hN hd) = 0 := by
  have hT0 : evalP (cx hN hd) (mulTerm {mm} 1 {nm}_T) = 0 := by
    rw [certify_sound _ _ _ {nm}_ok]
    simp [{gz}]
  rw [evalP_mulTerm _ _ _ _ (by decide +kernel)] at hT0
  have hT : evalP (cx hN hd) {nm}_T = 0 := by
    rcases mul_eq_zero.mp hT0 with h | h
    · exact absurd h (by simpa using evalM_cx_ne hN hd {mm})
    · exact h
  rw [{f'← {nm}_meanE' if nm in ('M3','M2','M1','QU') else f'← eqCheckPE_sound _ _ _ {nm}_mean'}, evalP_mulTerm _ _ _ _ (by decide +kernel), hT, mul_zero]

'''
s+="end Ident\nend ALz11\n"
open('../../../RamanujanTau/Atkin11CertL.lean','w').write(s)
print("ok")
