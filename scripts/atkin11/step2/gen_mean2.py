"""Meaning checks as a DAG of small checks.

For an identity eX, every sub-expression of the PE tree becomes a literal polynomial node, checked by one
`certifyR` (product) or `eqRuns` (sum/difference/scalar) on literal data only. Products larger than LIMIT raw terms
are chunked (the kernel needs roughly 140 KB per raw term). The leaves are re-sorted copies of the `Pieces`
polynomials (checked once by the sort-based `eqCheck`). A generic lemma `X_meanE x :
evalP x (mulTerm mc 1 X_root) = eX.eval x` glues the node equations together.
For QU the node data is spread over several files of bounded cost.
"""
import sys, os
exec(open('tree_cert.py').read().split('if __name__=="__main__":')[0])
exec(open('gen_tree_lean.py').read().split('UB=8')[0].split("OUT='../../../RamanujanTau/Atkin11Cert'")[1])
OUT='../../../RamanujanTau/Atkin11Cert'
def mono_mc(fn):
    e,c=readp(fn)[0]; m=0
    for v in reversed(e): m=m*1024+v
    return m
LEAF={nm:todict(readp(f'{D}/P_{nm}.txt')) for nm in ["GN","GD","F3","F4","F5","F6","F7","F8","F9","F10","F11"]}
LEAF["Q"]={packm([1]*5):-1}
LNAME={k:("PQ" if k=="Q" else "P"+k) for k in LEAF}
L=lambda n:('lit',n)
Q5=('pow',L('Q'),5)
a3=('add',('mul',('mul',('pow',L('GN'),2),L('GD')),L('F11')),('smul',11,('mul',Q5,('pow',L('GD'),3))))
a4=('sub',('mul',('pow',L('GN'),3),L('F11')),('smul',11,('mul',Q5,('pow',L('GD'),3))))
a2=('mul',('mul',('mul',L('GN'),L('GD')),('add',L('GD'),L('GN'))),L('F11'))
az=('mul',('mul',('add',L('GD'),L('GN')),('pow',L('GD'),2)),Q5)
ae=lambda F,k:('mul',('mul',('mul',('add',L('GD'),L('GN')),('pow',L('GD'),2)),('pow',L('Q'),5-k)),L(F))
EX={
 'M3':('sub',('add',('add',('smul',242,a3),('smul',5324,a4)),('smul',73205,az)),ae('F8',3)),
 'M2':('sub',('add',('add',('add',('smul',-11,a2),('smul',968,a3)),('smul',11979,a4)),('smul',161051,az)),ae('F9',4)),
 'M1':('sub',('add',('add',('add',('smul',121,a2),('smul',2662,a3)),('smul',14641,a4)),('smul',161051,az)),ae('F10',4)),
 'QU':('sub',('sub',('mul',('pow',L('GN'),5),('pow',L('F11'),2)),
        ('mul',('mul',Q5,L('F11')),('add',('add',('pow',L('GD'),5),('smul',13,('mul',L('GN'),('pow',L('GD'),4)))),
          ('smul',34,('mul',('pow',L('GN'),2),('pow',L('GD'),3)))))),
      ('smul',121,('mul',('pow',L('Q'),10),('pow',L('GD'),5)))),
}
LIMIT=int(os.environ.get('LIMIT','30000'))
BUDGET=int(os.environ.get('BUDGET','60000'))

def emit(nm):
    tree = nm in ("M2","M1","QU")
    tname=f"{nm}_root" if tree else f"{nm}_T"
    nd={}; items=[]   # items: (cost, lean-source, eval-lemma-name or None)
    def dic(n): return nd[n]
    cnt=[0]
    def fresh(): cnt[0]+=1; return f"{nm}N{cnt[0]-1}"
    def lemma(name,rhs,pf,extra=""):
        return (f"lemma {name}_eval (x : List R) : SPoly.evalP x {name} = {rhs} := by\n  rw [{pf}]\n"
                f"  all_goals (try simp [SPoly.evalP_negP, SPoly.evalP_smulP{extra}])\n  all_goals (try ring)\n")
    data=[]; checks=[]; evals=[]; simpnames=[]
    def node(name,d,check,cost):
        nd[name]=d; data.append((cost,defs_d(name,d)+check))
    leaves={}
    def leaf(k):
        if k in leaves: return leaves[k]
        name=f"{nm}S{LNAME[k]}"
        node(name,LEAF[k],f"theorem {name}_ok : SPoly.eqCheck {LNAME[k]} {name} = true := by\n  decide +kernel\n",len(LEAF[k]))
        evals.append(lemma(name,f"SPoly.evalP x {LNAME[k]}",f"SPoly.eqCheck_sound x _ _ {name}_ok"))
        simpnames.append(f"{name}_eval"); leaves[k]=name; return name
    def mulnode(A,B):
        dA,dB=dic(A),dic(B)
        if len(dA)<len(dB): A,B,dA,dB=B,A,dB,dA
        C=fresh(); dC=mul(dA,dB)
        if len(dA)*len(dB)<=LIMIT:
            node(C,dC,f"theorem {C}_ok : SPoly.certifyR [({A}, {B})] {C} = true := by\n  decide +kernel\n",len(dA)*len(dB))
            evals.append(lemma(C,f"SPoly.evalP x {A} * SPoly.evalP x {B}",f"SPoly.certifyR_sound x _ _ {C}_ok"))
            simpnames.append(f"{C}_eval"); return C
        # chunk the larger factor A (each chunk run stays sorted)
        it=sorted(dA.items()); step=max(1,LIMIT//len(dB)); chunks=[]; prods=[]
        for i in range(0,len(it),step):
            Ai=f"{C}a{len(chunks)}"; node(Ai,dict(it[i:i+step]),"",0); chunks.append(Ai)
            Pi=f"{C}p{len(prods)}"; dP=mul(nd[Ai],dB)
            node(Pi,dP,f"theorem {Pi}_ok : SPoly.certifyR [({Ai}, {B})] {Pi} = true := by\n  decide +kernel\n",len(nd[Ai])*len(dB))
            evals.append(lemma(Pi,f"SPoly.evalP x {Ai} * SPoly.evalP x {B}",f"SPoly.certifyR_sound x _ _ {Pi}_ok"))
            prods.append(Pi)
        node(C,dC,f"theorem {C}_ok : SPoly.eqRuns [{', '.join(prods)}] {C} = true := by\n  decide +kernel\n"
             f"theorem {C}_chunks_ok : SPoly.eqRuns [{', '.join(chunks)}] {A} = true := by\n  decide +kernel\n",len(dC)+len(dA))
        evals.append(f"lemma {C}_eval (x : List R) : SPoly.evalP x {C} = SPoly.evalP x {A} * SPoly.evalP x {B} := by\n"
                     f"  rw [SPoly.eqRuns_sound x _ _ {C}_ok]\n"
                     f"  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, {', '.join(p+'_eval' for p in prods)}]\n"
                     f"  rw [SPoly.eqRuns_sound x _ _ {C}_chunks_ok]\n"
                     f"  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]\n  ring\n")
        simpnames.append(f"{C}_eval"); return C
    memo={}
    def go(e):
        key=repr(e)
        if key in memo: return memo[key]
        op=e[0]
        if op=='lit': r=leaf(e[1])
        elif op in ('add','sub'):
            a,b=go(e[1]),go(e[2]); r=fresh()
            if op=='add':
                d=addd([dic(a),dic(b)])
                node(r,d,f"theorem {r}_ok : SPoly.eqRuns [{a}, {b}] {r} = true := by\n  decide +kernel\n",len(dic(a))+len(dic(b)))
                evals.append(lemma(r,f"SPoly.evalP x {a} + SPoly.evalP x {b}",f"SPoly.eqRuns_sound x _ _ {r}_ok"))
            else:
                d=addd([dic(a),{k:-v for k,v in dic(b).items()}])
                node(r,d,f"theorem {r}_ok : SPoly.eqRuns [{a}, SPoly.negP {b}] {r} = true := by\n  decide +kernel\n",len(dic(a))+len(dic(b)))
                evals.append(lemma(r,f"SPoly.evalP x {a} - SPoly.evalP x {b}",f"SPoly.eqRuns_sound x _ _ {r}_ok"))
            simpnames.append(f"{r}_eval")
        elif op=='smul':
            a=go(e[2]); r=fresh(); c=e[1]
            node(r,{k:c*v for k,v in dic(a).items()},f"theorem {r}_ok : SPoly.eqRuns [SPoly.smulP ({c}) {a}] {r} = true := by\n  decide +kernel\n",len(dic(a)))
            evals.append(lemma(r,f"({c} : R) * SPoly.evalP x {a}",f"SPoly.eqRuns_sound x _ _ {r}_ok"))
            simpnames.append(f"{r}_eval")
        elif op=='mul':
            r=mulnode(go(e[1]),go(e[2]))
        elif op=='pow':
            a=go(e[1]); r=a
            for _ in range(e[2]-1): r=mulnode(r,a)
        memo[key]=r; return r
    root=go(EX[nm])
    mc=mono_mc(f'{D}/{nm}_mc.txt')
    T=todict(readp(f'{D}/{nm}_T.txt'))
    assert nd[root]=={k+mc:v for k,v in T.items()}, "mean mismatch"
    if tree:
        fin=f"theorem {nm}_fin_ok : SPoly.eqRuns [{root}] (SPoly.mulTerm {mc} 1 {tname}) = true := by\n  decide +kernel\n"
    else:
        fin=f"theorem {nm}_fin_ok : SPoly.eqCheck (SPoly.mulTerm {mc} 1 {tname}) {root} = true := by\n  decide +kernel\n"
    base_imp=f"import RamanujanTau.Atkin11Cert.{nm + 'T_S2' if tree else nm}\nimport RamanujanTau.Atkin11Cert.Pieces\nimport RamanujanTau.SPolyFast"
    # distribute data into part files
    parts=[]; cur=""; cost=0
    for c,src in data:
        if cost+c>BUDGET and cur: parts.append(cur); cur=""; cost=0
        cur+=src; cost+=c
    if cur: parts.append(cur)
    prev=None; files=[]
    for i,pt in enumerate(parts):
        fn=f"{nm}MeanP{i}"; files.append(fn)
        imp=f"import RamanujanTau.Atkin11Cert.{prev}" if prev else base_imp
        open(f'{OUT}/{fn}.lean','w').write(hdr(f"meaning of {nm}, node data part {i}",imp)+pt+"\nend Atkin11Cert\n")
        prev=fn
    s=hdr(f"meaning of {nm}, node by node",f"import RamanujanTau.Atkin11Cert.{prev}")
    s+=fin+"\nsection Eval\nvariable {R : Type*} [CommRing R]\n\n"+"".join(evals)
    s+=f"""
theorem {nm}_meanE (x : List R) : SPoly.evalP x (SPoly.mulTerm {mc} 1 {tname}) = e{nm}.eval x := by
  rw [{"SPoly.eqRuns_sound" if tree else "SPoly.eqCheck_sound"} x _ _ {nm}_fin_ok]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, {", ".join(simpnames)}]
  simp only [e{nm}, a2, a3, a4, az, ae, L, Q5, SPoly.PE.eval]
  push_cast
  ring

end Eval

end Atkin11Cert
"""
    open(f'{OUT}/{nm}Mean.lean','w').write(s)
    print(nm,"nodes",len(nd),"parts",len(files),"max node",max(len(v) for v in nd.values()))
    return files
if __name__=="__main__":
    for nm in sys.argv[1:]: print(emit(nm))
