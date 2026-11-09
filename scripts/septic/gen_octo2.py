"""Generate RamanujanTau/Septic/Octo{1,2}.lean (v2): 8-dimensional lattice identities
   φ(q⁷)⁸ = Σ_{v∈W} Π_i T_{v_i}  for Lagrangians W ⊂ F_7^8 with L_W = M ℤ⁸, MᵀM = 7I.
The bijection ℤ⁸ → L_W → Idx4 × ℤ⁸ is proved with explicit linear certificates (no large omega calls)."""
import itertools, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from gen_octo import MATS, analyse, poly_of, lean_poly, a, b, c, d
import sympy as sp
p = 7
def comp(var, i):
    return var + ".1" * 7 if i == 0 else var + ".1" * (7 - i) + ".2"
def lin(coefs, xs):
    t = [f"({co}) * {x}" for co, x in zip(coefs, xs) if co != 0]
    return " + ".join(t) if t else "0"
def solve_mod7(rows, target):
    """find lam with sum_j lam_j rows[j] == target (mod 7)"""
    m = sp.Matrix(rows).T  # columns = rows
    for lam in itertools.product(range(7), repeat=len(rows)):
        pass
    # linear algebra over GF(7)
    A = sp.Matrix(rows).T.applyfunc(lambda x: x % 7)
    bvec = sp.Matrix(target).applyfunc(lambda x: x % 7)
    # gaussian elimination mod 7
    n_eq, n_var = A.shape
    aug = [[int(A[i, j]) for j in range(n_var)] + [int(bvec[i])] for i in range(n_eq)]
    piv_cols = []; r = 0
    for col in range(n_var):
        pr = next((i for i in range(r, n_eq) if aug[i][col] % 7), None)
        if pr is None: continue
        aug[r], aug[pr] = aug[pr], aug[r]
        inv = pow(aug[r][col], -1, 7)
        aug[r] = [(x * inv) % 7 for x in aug[r]]
        for i in range(n_eq):
            if i != r and aug[i][col]:
                f = aug[i][col]
                aug[i] = [(x - f * y) % 7 for x, y in zip(aug[i], aug[r])]
        piv_cols.append(col); r += 1
    for i in range(r, n_eq): assert aug[i][-1] % 7 == 0
    lam = [0] * n_var
    for i, col in enumerate(piv_cols): lam[col] = aug[i][-1]
    return lam
def gen(idx):
    M, P, forms, cnt = analyse(MATS[idx])
    nm = f"O{idx}"
    MT = [[M[i][j] for i in range(8)] for j in range(8)]  # MT[j][i]
    L = []
    nvars = [comp("n", j) for j in range(8)]
    kvars = [comp("k", i) for i in range(8)]
    for i in range(8):
        L.append(f"def {nm}k{i} (n : Z8) : ℤ := {lin(M[i], nvars)}")
    for j in range(8):
        L.append(f"def {nm}t{j} (k : Z8) : ℤ := {lin(MT[j], kvars)}")
    mem = " ∧ ".join(f"7 ∣ {nm}t{j} k" for j in range(8))
    L.append(f"def {nm}Mem (k : Z8) : Prop := {mem}")
    L.append(f"abbrev {nm}L := {{k : Z8 // {nm}Mem k}}")
    # e1 : Z8 ≃ L
    kn = f"(((((((({nm}k0 n, {nm}k1 n), {nm}k2 n), {nm}k3 n), {nm}k4 n), {nm}k5 n), {nm}k6 n), {nm}k7 n) : Z8)"
    memproof = ", ".join(f"⟨{nvars[j]}, by simp only [{nm}t{j}, {', '.join(f'{nm}k{i}' for i in range(8))}]; ring⟩" for j in range(8))
    # membership: t_j(Mn) = 7 n_j
    tdiv = [f"{nm}t{j} k.1 / 7" for j in range(8)]
    ninv = tdiv[0]
    for j in range(1, 8): ninv = f"({ninv}, {tdiv[j]})"
    L.append(f"""
def {nm}e1 : Z8 ≃ {nm}L where
  toFun n := ⟨{kn}, by
    refine ⟨{', '.join(f'Dvd.intro {nvars[j]} ?_' for j in range(8))}⟩ <;>
      simp only [{', '.join(f'{nm}t{j}' for j in range(8))}, {', '.join(f'{nm}k{i}' for i in range(8))}] <;>
      ring⟩
  invFun k := {ninv}
  left_inv n := by
    obtain ⟨⟨⟨⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := n
    simp only [{', '.join(f'{nm}t{j}' for j in range(8))}, {', '.join(f'{nm}k{i}' for i in range(8))}]
    ext <;> simp only <;> omega
  right_inv k := by
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, hk⟩ := k
    obtain ⟨⟨q0, h0⟩, ⟨q1, h1⟩, ⟨q2, h2⟩, ⟨q3, h3⟩, ⟨q4, h4⟩, ⟨q5, h5⟩, ⟨q6, h6⟩, ⟨q7, h7⟩⟩ := hk
    apply Subtype.ext
    simp only [{', '.join(f'{nm}k{i}' for i in range(8))}] at *
    simp only [{', '.join(f'{nm}t{j}' for j in range(8))}] at *
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (7 : ℤ) ≠ 0)]""")
    # right_inv: need M q = k where 7 q = M^T k ; i.e. 7 (M q)_i = (M M^T k)_i = 7 k_i
    rows = []
    for i in range(8):
        # linear_combination: 7*(Σ_j M_ij q_j) - 7 k_i = Σ_j M_ij (7 q_j - t_j) ;  t_j = (M^T k)_j
        lc = " + ".join(f"({-M[i][j]}) * h{j}" for j in range(8) if M[i][j] != 0)
        rows.append(f"    · have : (7 : ℤ) * ({lin(M[i], [f'q{j}' for j in range(8)])}) = 7 * k{i} := by linear_combination {lc}\n      omega")
    L.append("    ext <;> simp only\n" + "\n".join(rows))
    # e2 : L ≃ Idx4 × Z8
    sdef = []
    for jj in range(4):
        sdef.append(f"⟨({comp('k', P[jj])} % 7).toNat, by omega⟩")
    L.append(f"def {nm}s (k : Z8) : Idx4 := ((({sdef[0]}, {sdef[1]}), {sdef[2]}), {sdef[3]})")
    sv = ["((s.1.1.1 : ℕ) : ℤ)", "((s.1.1.2 : ℕ) : ℤ)", "((s.1.2 : ℕ) : ℤ)", "((s.2 : ℕ) : ℤ)"]
    for i in range(8):
        if i in P:
            L.append(f"def {nm}r{i} (s : Idx4) : ℤ := {sv[P.index(i)]}")
        else:
            L.append(f"def {nm}r{i} (s : Idx4) : ℤ := ({lin(forms[i], sv)}) % 7")
    # divisibility of t_j(7m + r(s)): Σ_i M_ij r_i(s) ≡ 0. r_i = lin_i(s) % 7 = lin_i - 7*(lin_i/7)
    # Σ_i M_ij lin_i(s) = 7 * form_j(s)
    formj = []
    for j in range(8):
        co = [sum(M[i][j] * forms[i][l] for i in range(8)) for l in range(4)]
        assert all(x % 7 == 0 for x in co)
        formj.append([x // 7 for x in co])
    # k ↦ class: 7 ∣ k_i - Σ c_il k_{P_l} from membership: e_i - Σ c e_P = Σ_j λ_j (row j of M^T) + 7 μ
    lam_all = []; mu_all = []
    for i in range(8):
        target = [0] * 8; target[i] += 1
        for l in range(4): target[P[l]] -= forms[i][l]
        lam = solve_mod7(MT, target)
        diff = [target[x] - sum(lam[j] * MT[j][x] for j in range(8)) for x in range(8)]
        assert all(v % 7 == 0 for v in diff)
        lam_all.append(lam); mu_all.append([v // 7 for v in diff])
    G = [f"(7 * {comp('m', i)} + {nm}r{i} st) ^ 2" for i in range(8)]
    ge = G[0]
    for i in range(1, 8): ge = f"({ge} + {G[i]})"
    L.append(f"def {nm}G (st : Idx4) (m : Z8) : ℤ := {ge}")
    mdef = [f"({comp('k.1', i)} - {nm}r{i} ({nm}s k.1)) / 7" for i in range(8)]
    me = mdef[0]
    for i in range(1, 8): me = f"({me}, {mdef[i]})"
    kq = [f"7 * {comp('q.2', i)} + {nm}r{i} q.1" for i in range(8)]
    ke = kq[0]
    for i in range(1, 8): ke = f"({ke}, {kq[i]})"
    # membership proof for invFun: t_j(7m + r) = 7*(t_j(m) + form_j(s) - Σ_i M_ij (lin_i/7))  [pivot coords: r = s exactly]
    memb = []
    for j in range(8):
        terms = []
        for i in range(8):
            if M[i][j] == 0 or i in P: continue
            terms.append(f"({M[i][j]}) * (({lin(forms[i], sv)}) / 7)")
        corr = (" - (" + " + ".join(terms) + ")") if terms else ""
        tm = lin(MT[j], [comp('q.2', i) for i in range(8)])
        memb.append(f"⟨({tm}) + ({lin(formj[j], sv)}){corr}, by simp only [{nm}t{j}, {', '.join(f'{nm}r{i}' for i in range(8))}, Int.emod_def]; ring⟩")
    tq = [f"{nm}t{jj}" for jj in range(8)]
    rlist = ", ".join(f"{nm}r{ii}" for ii in range(8))
    tlist = ", ".join(tq)
    L.append(f"""
lemma {nm}mem_mk (q : Idx4 × Z8) : {nm}Mem {ke} := by
  refine ⟨{', '.join('?_' for _ in range(8))}⟩""")
    for jj in range(8):
        w = memb[jj][1:memb[jj].index(", by")].replace("s.1.1.1 :", "q.1.1.1.1 :").replace("s.1.1.2 :", "q.1.1.1.2 :").replace("s.1.2 :", "q.1.1.2 :").replace("s.2 :", "q.1.2 :")
        L.append(f"  · exact Dvd.intro ({w}) (by simp only [{nm}t{jj}, {rlist}, Int.emod_def]; ring)")
    # s_mk
    L.append(f"""
lemma {nm}s_mk (q : Idx4 × Z8) : {nm}s {ke} = q.1 := by
  obtain ⟨⟨⟨⟨s0, h0⟩, ⟨s1, h1⟩⟩, ⟨s2, h2⟩⟩, ⟨s3, h3⟩⟩ := q.1
  sorry""")
    # simpler: prove s_mk by ext
    L[-1] = f"""
lemma {nm}s_mk (q : Idx4 × Z8) : {nm}s {ke} = q.1 := by
  obtain ⟨⟨⟨⟨⟨s0, h0⟩, ⟨s1, h1⟩⟩, ⟨s2, h2⟩⟩, ⟨s3, h3⟩⟩, m⟩ := q
  simp only [{nm}s, {rlist}]
  ext <;> simp only <;> omega"""
    # class fact: for k ∈ L, 7 m_i + r_i(s k) = k_i
    L.append(f"""
lemma {nm}cls (k : {nm}L) :""")
    concl = []
    for ii in range(8):
        concl.append(f"7 * (({comp('k.1', ii)} - {nm}r{ii} ({nm}s k.1)) / 7) + {nm}r{ii} ({nm}s k.1) = {comp('k.1', ii)}")
    L[-1] += "\n    " + " ∧\n    ".join(concl) + " := by"
    L.append(f"""  obtain ⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, hk⟩ := k
  obtain ⟨⟨q0, g0⟩, ⟨q1, g1⟩, ⟨q2, g2⟩, ⟨q3, g3⟩, ⟨q4, g4⟩, ⟨q5, g5⟩, ⟨q6, g6⟩, ⟨q7, g7⟩⟩ := hk
  simp only [{tlist}] at g0 g1 g2 g3 g4 g5 g6 g7
  simp only [{nm}s, {rlist}, toNat_emod7]
  refine ⟨{', '.join('?_' for _ in range(8))}⟩""")
    kk = [f"k{x}" for x in range(8)]
    for ii in range(8):
        if ii in P:
            L.append("  · omega")
        else:
            lhs = f"k{ii} - ({lin(forms[ii], [f'k{P[l]}' for l in range(4)])})"
            wit = " + ".join([f"({lam_all[ii][jj]}) * q{jj}" for jj in range(8) if lam_all[ii][jj]] + [f"({mu_all[ii][x]}) * k{x}" for x in range(8) if mu_all[ii][x]]) or "0"
            lc = " + ".join(f"({lam_all[ii][jj]}) * g{jj}" for jj in range(8) if lam_all[ii][jj]) or "0"
            L.append(f"  · have hd : {lhs} = 7 * ({wit}) := by linear_combination {lc}\n    omega")
    me_q = me
    L.append(f"""
def {nm}e2 : {nm}L ≃ Idx4 × Z8 where
  toFun k := ({nm}s k.1, {me})
  invFun q := ⟨{ke}, {nm}mem_mk q⟩
  left_inv k := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := {nm}cls k
    apply Subtype.ext
    simp only
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  right_inv q := by
    simp only [{nm}s_mk]
    obtain ⟨st, ⟨⟨⟨⟨⟨⟨⟨m0, m1⟩, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩, m7⟩⟩ := q
    ext <;> simp only <;> omega

def {nm}WL (k : {nm}L) : ℤ := {' + '.join(f'{comp("k.1", ii)} ^ 2' for ii in range(8))}

lemma {nm}W_e1 (n : Z8) : {nm}WL ({nm}e1 n) = W8 n := by
  simp only [{nm}WL, {nm}e1, Equiv.coe_fn_mk, W8, {', '.join(f'{nm}k{ii}' for ii in range(8))}]
  ring

lemma {nm}G_e2 (k : {nm}L) : {nm}G ({nm}e2 k).1 ({nm}e2 k).2 = {nm}WL k := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := {nm}cls k
  simp only [{nm}G, {nm}e2, Equiv.coe_fn_mk, {nm}WL]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  try ring

lemma good_{nm}G (st : Idx4) : Good ({nm}G st) :=
  good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _
    (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)

lemma cnt_{nm}G (st : Idx4) :
    cnt ({nm}G st) = T ({nm}r0 st) * T ({nm}r1 st) * T ({nm}r2 st) * T ({nm}r3 st)
      * T ({nm}r4 st) * T ({nm}r5 st) * T ({nm}r6 st) * T ({nm}r7 st) := by
  simp only [T]
  rw [cnt_mul _ _ (good_T _) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _))
      (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _))
      (good_T _)) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _)
      (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _ (good_prod _ _
      (good_T _) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)) (good_T _)]
  rfl

/-- the polynomial `P_{{W_{idx}}}(a,b,c,d)` (multiplicities of the class patterns on `W_{idx}`). -/
noncomputable def {nm}poly : PowerSeries ℤ :=
      {lean_poly(poly_of(cnt))}

/-- the coset sum `Σ_{{v ∈ W_{idx}}} Π T_{{vᵢ}}`. -/
lemma {nm}sum : ∑ st : Idx4, cnt ({nm}G st) = {nm}poly := by
  simp only [cnt_{nm}G, Fintype.sum_prod_type, Fin.sum_univ_seven, {rlist}]
  norm_num [T4, T5, T6, {nm}poly]
  ring

/-- **8-dimensional lattice identity {idx}**: `φ(q⁷)⁸ = P_{{W_{idx}}}(a, b, c, d)`. -/
theorem octo{idx}_identity : ramF 7 7 ^ 8 = {nm}poly := by
  rw [Phi8_cnt, cnt_congr ({nm}e1.trans {nm}e2) (g := fun p : Idx4 × Z8 => {nm}G p.1 p.2)
    (fun n => by simp only [Equiv.trans_apply]; rw [{nm}G_e2, {nm}W_e1]),
    cnt_fin_prod {nm}G good_{nm}G, {nm}sum]
""")
    return L, (M, P, forms, cnt, formj, lam_all, mu_all, memb, ke, me)
from gen_octo import HEADER
if __name__ == "__main__":
    which = [int(x) for x in sys.argv[1:]] or [1, 2]
    for idx in which:
        L, extra = gen(idx)
        out = f"RamanujanTau/Septic/Octo{idx}.lean"
        hdr = HEADER if idx == 1 else HEADER.replace("import RamanujanTau.Septic.Quaternion", "import RamanujanTau.Septic.Octo1").split("abbrev Z8")[0] + "\n"
        open(out, "w").write(hdr + "\n".join(L) + "\nend RamanujanTau.Septic\n")
        print("wrote", out)
