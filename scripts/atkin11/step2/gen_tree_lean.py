import sys, os
exec(open('tree_cert.py').read().split('if __name__=="__main__":')[0])
OUT='../../../RamanujanTau/Atkin11Cert'
def lit_d(d): return "[" + ", ".join(str(k*(2**48)+abs(v)*2+(1 if v<0 else 0)) for k,v in sorted(d.items())) + "]"
def defs_d(name, d):
    items=sorted(d.items()); parts=[items[i:i+CH] for i in range(0,len(items),CH)] or [[]]
    src=""; names=[]
    for k,pt in enumerate(parts):
        nm=f"{name}_{k}"; names.append(nm)
        src+=f"def {nm} : List ℕ := {lit_d(dict(pt))}\n"
    src+=f"def {name} : SPoly.Poly := SPoly.ofPacked (" + " ++ ".join(names) + ")\n"
    return src
UB=8
def gen(nm, sat=0, fast=False):
    units,tree=build(nm,sat)
    files=[]
    # unit batches
    for b in range(0,len(units),UB):
        fn=f"{nm}T_U{b//UB}"; files.append(fn)
        s=hdr(f"{nm}: unit products, batch {b//UB}","import RamanujanTau.Atkin11Cert.Common" + ("\nimport RamanujanTau.SPolyFast" if fast else ""))
        for u in range(b,min(b+UB,len(units))):
            j,piece,R=units[u]
            if fast:
                s+=defs_d(f"{nm}_P{u}", todict(piece)); s+=defs_d(f"{nm}_R{u}", R)
                s+=f"theorem {nm}_R{u}_ok : SPoly.certifyR [({nm}_P{u}, G{j})] {nm}_R{u} = true := by\n  decide +kernel\n"
            else:
                s+=defs(f"{nm}_P{u}", piece); s+=defs_d(f"{nm}_R{u}", R)
                s+=f"theorem {nm}_R{u}_ok : SPoly.certify [({nm}_P{u}, G{j})] {nm}_R{u} = true := by\n  decide +kernel\n"
        s+="\nend Atkin11Cert\n"; open(f'{OUT}/{fn}.lean','w').write(s)
    # levels
    prev=[f"{nm}_R{u}" for u in range(len(units))]
    prevfiles=list(files)
    for lv,(groups,nxt) in enumerate(tree):
        last = lv==len(tree)-1
        fn=f"{nm}T_S{lv}"
        lfast = fast or last  # the root always uses the run-based check (the sort-based one needs ~50 GB on QU)
        s=hdr(f"{nm}: tree level {lv}","\n".join(f"import RamanujanTau.Atkin11Cert.{f}" for f in prevfiles) + ("\nimport RamanujanTau.SPolyFast" if lfast and not fast else ""))
        cur=[]
        idx=0
        for k,g in enumerate(groups):
            ch=prev[idx:idx+len(g)]; idx+=len(g)
            name=f"{nm}_S{lv}_{k}" if not last else f"{nm}_root"
            s+=defs_d(name, nxt[k])
            if lfast:
                s+=f"theorem {name}_ok : SPoly.eqRuns [{', '.join(ch)}] {name} = true := by\n  decide +kernel\n"
            else:
                s+=f"theorem {name}_ok : SPoly.eqCheck ({' ++ '.join(ch)}) {name} = true := by\n  decide +kernel\n"
            cur.append((name,ch))
        s+="\nend Atkin11Cert\n"; open(f'{OUT}/{fn}.lean','w').write(s)
        prev=[c[0] for c in cur]; prevfiles=[fn]; files.append(fn)
    # root equals target: compare root to the (shifted) target poly from the standard T file
    return units,tree,files
if __name__=="__main__":
    for nm in sys.argv[1:]:
        u,t,f=gen(nm, fast=(nm!="QU"))
        print(nm, len(u),"units; files:", f)
