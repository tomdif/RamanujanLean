# Generator for RamanujanTau/LehmerSmall/QuasiLin.lean (sympy). Run: python3 quasilin_gen.py  (writes ./QuasiLin.lean)
import sympy as sp, itertools, math
e2,e4,e6,x=sp.symbols('e2 e4 e6 x')
def D(P): # 12*theta
    return sp.expand(sp.diff(P,e2)*(e2**2-e4)+4*sp.diff(P,e4)*(e2*e4-e6)+6*sp.diff(P,e6)*(e2*e6-e4**2))
Fs={'E2':(e2,2),'E4':(e4,4),'E6':(e6,6),'E8':(e4**2,8),'E10':(e4*e6,10),'E4c':(e4**3,12),'E6s':(e6**2,12)}
def wt(m): # weighted degree of monomial
    d=sp.Poly(m,e2,e4,e6).monoms()[0]; return 2*d[0]+4*d[1]+6*d[2]
def linearize(T,J=5):
    T=sp.expand(T)
    basis=[]
    for name,(F,w) in Fs.items():
        j=0
        while w+2*j<=12:
            P=F
            for _ in range(j): P=D(P)
            basis.append(((name,j),sp.expand(P*12**(J-j)) if j<=J else None)); j+=1
    syms=sp.symbols('a0:%d'%len(basis)); b0=sp.Symbol('b0')
    expr=sp.expand(T*12**J - sum(s*P for s,(_,P) in zip(syms,basis)) - b0)
    eqs=sp.Poly(expr,e2,e4,e6).coeffs()
    sol=sp.solve(eqs,list(syms)+[b0],dict=True)
    assert len(sol)==1
    sol=sol[0]
    return [(lab,sol.get(s,0)) for s,(lab,_) in zip(syms,basis)], sol.get(b0,0)
coef={'E2':(-24,1),'E4':(240,3),'E6':(-504,5),'E8':(480,7),'E10':(-264,9)}
def atprime(lin,b0):
    # returns 691 * coefficient of RHS at prime p (tau=0) as polynomial in x
    tot=0
    for (name,j),a in lin:
        if a==0: continue
        if name in coef:
            c,k=coef[name]; tot+=691*a*x**j*c*(1+x**k)
        else:  # E4c or E6s : 691*[.]= 65520 sigma11 at tau=0
            tot+=a*x**j*65520*(1+x**11)
    return sp.expand(tot)
import math
V={'e2':'E₂','e4':'E₄','e6':'E₆'}
def lean(P):
    P=sp.Poly(sp.expand(P),e2,e4,e6)
    terms=[]
    for (a,b,c),co in zip(P.monoms(),P.coeffs()):
        mon=[]
        for v,k in (('E₂',a),('E₄',b),('E₆',c)):
            if k==1: mon.append(v)
            elif k>1: mon.append(f"{v} ^ {k}")
        co=int(co)
        m=' * '.join(mon) if mon else None
        terms.append((co,m))
    s=''
    for i,(co,m) in enumerate(terms):
        sign='-' if co<0 else '+'; a=abs(co)
        body = (f"{a} * {m}" if a!=1 else m) if m else f"{a}"
        if i==0: s = ('-' if co<0 else '')+body
        else: s += f" {sign} {body}"
    return s if s else '0'
def lc(P): # Lean coefficient expression in parentheses
    return '('+lean(P)+')'
Fpoly={'E2':e2,'E4':e4,'E6':e6,'F8':e4**2,'F10':e4*e6}
Fname={'E2':'E₂','E4':'E₄','E6':'E₆','F8':'F8','F10':'F10'}
def chain(F,J):
    out=[]; P=Fpoly[F]; Ps=[P]
    for j in range(1,J+1):
        Pn=D(Ps[-1]); Ps.append(Pn)
    simpset="theta_mul, Igusa.theta_add, theta_sub, theta_neg', theta_ofNat', Igusa.theta_one, pow_succ, pow_zero, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero"
    for j in range(1,J+1):
        Pp=Ps[j-1]
        c2=sp.diff(Pp,e2); c4=4*sp.diff(Pp,e4); c6=6*sp.diff(Pp,e6)
        name=f"t{F}_{j}"
        s=f"lemma {name} : ({12**j} : PowerSeries ℤ) * theta^[{j}] {Fname[F]} = {lean(Ps[j])} := by\n"
        s+="  obtain ⟨R1, R2, R3⟩ := RamanujanODEProof.ramanujanODE\n"
        if j==1:
            s+="  rw [Function.iterate_one]\n"
            if F in ('F8','F10'): s+=f"  rw [{F}]\n"
            s+=f"  try simp only [{simpset}]\n"
        else:
            s+=f"  have h := t{F}_{j-1}\n  rw [Function.iterate_succ_apply']\n"
            s+=f"  have hθ : theta (({12**(j-1)} : PowerSeries ℤ) * theta^[{j-1}] {Fname[F]}) = theta ({lean(Pp)}) := by rw [h]\n"
            s+=f"  simp only [{simpset}] at hθ\n"
        lcs=[]
        if j>1: lcs.append("12 * hθ")
        for c,R in ((c2,'R3'),(c4,'R1'),(c6,'R2')):
            if sp.expand(c)!=0: lcs.append(f"{lc(c)} * {R}")
        s+="  linear_combination "+" + ".join(lcs)+"\n"
        out.append(s)
    return out, Ps
coefF={'E2':(-24,1),'E4':(240,3),'E6':(-504,5),'F8':(480,7),'F10':(-264,9)}
def monomial(tag, T, Tlean, K, primes_targets):
    lin,b0=linearize(T); assert b0==0
    lin=[((('F8' if n=='E8' else 'F10' if n=='E10' else n),j),a) for (n,j),a in lin if a!=0]
    L=1
    for (n,j),a in lin:
        L=sp.ilcm(L, sp.Rational(a/ (12**j if n not in ('E4c','E6s') else 1)).q)
    L=int(L)
    # RHS
    terms=[]; lcs=[]; needs={}
    for (n,j),a in lin:
        c=int(L*a)
        if n=='E4c': t='E₄ ^ 3'
        elif n=='E6s': t='E₆ ^ 2'
        elif j==0: t={'E2':'E₂','E4':'E₄','E6':'E₆','F8':'E₄ ^ 2','F10':'E₄ * E₆'}[n]
        else:
            t=f"theta^[{j}] {Fname[n]}"; needs[n]=max(needs.get(n,0),j)
            lcs.append((-sp.Rational(L*a,12**j), f"t{n}_{j}"))
        terms.append((c,t))
    rhs=''
    for i,(c,t) in enumerate(terms):
        body=f"{abs(c)} * {t}" if abs(c)!=1 else t
        rhs += (('-' if c<0 else '')+body) if i==0 else (f" - {body}" if c<0 else f" + {body}")
    for c,_ in lcs: assert c.q==1
    lcstr=' + '.join(f"({int(c)}) * {h}" for c,h in lcs)
    # prime polynomial
    poly=0; Lc=0
    for (n,j),a in lin:
        c=int(L*a)
        if n in ('E4c','E6s'): Lc+=c
        else:
            cf,k=coefF[n]; poly+=c*x**j*cf*(1+x**k)
    big=sp.expand(691*poly+Lc*65520*(1+x**11))
    cs=[int(c) for c in sp.Poly(big,x).all_coeffs()]
    C=math.gcd(*cs); Q=sp.expand(big/C)
    MOD=1
    for l in primes_targets:
        e=sp.multiplicity(l,691*L*K)-sp.multiplicity(l,C); MOD*=l**e
    R=sp.Rational(691*L*K, C*MOD); assert R.q==1
    return dict(lin=lin,L=L,rhs=rhs,lcstr=lcstr,needs=needs,Lc=Lc,C=C,Q=Q,MOD=MOD,R=int(R),K=K,Tlean=Tlean)
def leanQ(Q,var):
    P=sp.Poly(Q,x); s=''
    for i,((k,),c) in enumerate(zip(P.monoms(),P.coeffs())):
        c=int(c); m = f"{var} ^ {k}" if k>1 else (var if k==1 else None)
        body = (f"{abs(c)} * {m}" if abs(c)!=1 else m) if m else f"{abs(c)}"
        s += (('-' if c<0 else '')+body) if i==0 else (f" - {body}" if c<0 else f" + {body}")
    return s
m1=monomial('A',(1-e2)**2*(e4-e2**2)**2,'(1 - E₂) ^ 2 * (E₄ - E₂ ^ 2) ^ 2',24**2*288**2,[2,3])
m2=monomial('B',(e4-e2**2)*(e4-1)**2,'(E₄ - E₂ ^ 2) * (E₄ - 1) ^ 2',288*240**2,[5])
needs={}
for m in (m1,m2):
    for k,v in m['needs'].items(): needs[k]=max(needs.get(k,0),v)
out=[]
out.append('''import RamanujanTau.LehmerSmall.Final64

/-! # Quasimodular integrality: `τ(p) = 0 ⇒ p ≡ −1 (mod 2⁹·3⁵·5³)`

GENERATED by a sympy script (certificates only; every step is checked by Lean).

Method. A product of the integer series `S_k = Σσ_k(n)qⁿ` and their `θ`-derivatives is an integer
`q`-series. When its top weight is `≤ 12` it is a quasimodular form, so it equals an explicit `ℚ`-linear
combination of `θʲE_k` (`k = 2,4,6,8,10`) and `E₄³, E₆²`. Clearing denominators gives an identity in
`ℤ⟦q⟧`. At a prime `p` with `τ(p) = 0`, every coefficient on the right is a polynomial in `p`
(`σ_k(p) = 1 + pᵏ`; the `E₄³ − E₆²` part is `1728·τ(p) = 0`). The integrality of the left side then
becomes a congruence on `p`. Two monomials suffice:
* `A = S₁²(θS₁)²`, with `(1 − E₂)²(E₄ − E₂²)² = 24²·288²·A`: gives `p ≡ −1 (mod 2⁹)` and `(mod 3⁵)`;
* `B = θS₁·S₃²`, with `(E₄ − E₂²)(E₄ − 1)² = 288·240²·B`: gives `p ≡ −1 (mod 5³)`.

The `θ`-chains `12ʲθʲF = P_{F,j}(E₂,E₄,E₆)` come from Ramanujan's ODEs (`RamanujanODEProof.ramanujanODE`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace RamanujanTau.LehmerSmall
open RamanujanTau PowerSeries ModP Igusa
open scoped ArithmeticFunction.sigma

local notation "E₂" => Igusa.E2 ℤ
local notation "E₄" => ModP.E4 ℤ
local notation "E₆" => ModP.E6 ℤ

noncomputable def F8 : PowerSeries ℤ := E4 ℤ ^ 2
noncomputable def F10 : PowerSeries ℤ := E4 ℤ * E6 ℤ

lemma theta_neg' (f : PowerSeries ℤ) : theta (-f) = -theta f := by ext n; simp [coeff_theta]

lemma theta_ofNat' (c : ℕ) [c.AtLeastTwo] : theta (no_index (OfNat.ofNat c : PowerSeries ℤ)) = 0 := by
  rw [show (OfNat.ofNat c : PowerSeries ℤ) = PowerSeries.C (OfNat.ofNat c : ℤ) from (map_ofNat _ _).symm]
  exact theta_C _

lemma coeff_iter (j n : ℕ) (f : PowerSeries ℤ) : coeff n (theta^[j] f) = (n : ℤ) ^ j * coeff n f := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', coeff_theta, ih]; ring
''')
for F in ('E2','E4','E6','F8','F10'):
    if F in needs:
        o,_=chain(F,needs[F]); out.append('\n'.join(o))
out.append('''
/-! ## coefficients -/

lemma cE2 {n : ℕ} (hn : n ≠ 0) : coeff n E₂ = -24 * (σ 1 n : ℤ) := by
  rw [E2_eq, map_sub, coeff_one, if_neg hn, coeff_ofNat_mul', coeff_Sk]; ring
lemma cE4 {n : ℕ} (hn : n ≠ 0) : coeff n E₄ = 240 * (σ 3 n : ℤ) := by rw [coeff_E4, if_neg hn]
lemma cE6 {n : ℕ} (hn : n ≠ 0) : coeff n E₆ = -504 * (σ 5 n : ℤ) := by rw [coeff_E6, if_neg hn]
lemma cF8 {n : ℕ} (hn : n ≠ 0) : coeff n F8 = 480 * (σ 7 n : ℤ) := by
  rw [F8, E4_sq, map_add, coeff_one, if_neg hn, coeff_ofNat_mul', coeff_Sk]; ring
lemma cF10 {n : ℕ} (hn : n ≠ 0) : coeff n F10 = -264 * (σ 9 n : ℤ) := by
  rw [F10, E4_mul_E6, map_sub, coeff_one, if_neg hn, coeff_ofNat_mul', coeff_Sk]; ring
lemma cE6sq (n : ℕ) : coeff n (E₆ ^ 2) = coeff n (E₄ ^ 3) - 1728 * TauCong.tauPS n := by
  have := congrArg (coeff n) (disc_eq (R := ℤ))
  rw [map_sub, coeff_ofNat_mul', coeff_Dq, Int.cast_id] at this
  linear_combination -this

lemma one_sub_E2 : 1 - E₂ = 24 * Sk 1 := by rw [E2_eq]; ring
lemma E4_sub_one : E₄ - 1 = 240 * Sk 3 := by rw [E4_eq]; ring
lemma E4_sub_E2sq : E₄ - E₂ ^ 2 = 288 * theta (Sk 1) := by
  obtain ⟨-, -, R3⟩ := RamanujanODEProof.ramanujanODE
  have h : theta E₂ = -(24 * theta (Sk 1)) := by
    rw [E2_eq, theta_sub, Igusa.theta_one, theta_ofNat_mul]; ring
  linear_combination R3 - 12 * h

lemma TA_eq : (1 - E₂) ^ 2 * (E₄ - E₂ ^ 2) ^ 2 = 47775744 * (Sk 1 ^ 2 * theta (Sk 1) ^ 2) := by
  rw [one_sub_E2, E4_sub_E2sq]; ring
lemma TB_eq : (E₄ - E₂ ^ 2) * (E₄ - 1) ^ 2 = 16588800 * (theta (Sk 1) * Sk 3 ^ 2) := by
  rw [E4_sub_one, E4_sub_E2sq]; ring
''')
for tag,m,X in (('A',m1,'Sk 1 ^ 2 * theta (Sk 1) ^ 2'),('B',m2,'theta (Sk 1) * Sk 3 ^ 2')):
    out.append(f'''/-- Linearization of `T{tag}` (exact identity in `ℤ⟦q⟧`). -/
theorem lin{tag} : ({m['L']} : PowerSeries ℤ) * ({m['Tlean']}) =
    {m['rhs']} := by
  linear_combination {m['lcstr']}

/-- Integrality of `{X}` at a prime zero of `τ`. -/
theorem cond{tag} {{p : ℕ}} (hp : p.Prime) (h0 : TauCong.tauPS p = 0) :
    ({m['MOD']} : ℤ) ∣ {leanQ(m['Q'],'(p : ℤ)')} := by
  have hn := hp.ne_zero
  have hk := congrArg (coeff p) lin{tag}
  rw [T{tag}_eq] at hk
  simp only [map_add, map_sub, map_neg, neg_mul, coeff_ofNat_mul', coeff_iter, cE2 hn, cE4 hn, cE6 hn,
    cF8 hn, cF10 hn, cE6sq, h0] at hk
  simp only [sigma_prime_cast hp] at hk
  refine ⟨{m['R']} * coeff p ({X}), ?_⟩
  apply mul_left_cancel₀ (show ({m['C']} : ℤ) ≠ 0 by norm_num)
  linear_combination (-691) * hk
''')
out.append(f'''
lemma dA512 : ∀ x : ZMod 512, {leanQ(m1['Q'],'x')} = 0 → x.val % 2 = 0 ∨ x.val = 511 := by
  decide +kernel
lemma dA243 : ∀ x : ZMod 243, {leanQ(m1['Q'],'x')} = 0 → x.val % 3 = 0 ∨ x.val = 242 := by
  decide +kernel
lemma dB125 : ∀ x : ZMod 125, {leanQ(m2['Q'],'x')} = 0 → x.val % 5 = 0 ∨ x.val = 124 := by
  decide +kernel

/-- **A prime zero of `τ` is `≡ −1` modulo `2⁹`, `3⁵` and `5³`.** -/
theorem prime_zero_deep {{p : ℕ}} (hp : p.Prime) (h : τ p = 0) :
    p % 512 = 511 ∧ p % 243 = 242 ∧ p % 125 = 124 := by
  have ht : TauCong.tauPS p = 0 := by rw [← tau_eq_tauPS]; exact h
  have h2 : p ≠ 2 := by rintro rfl; rw [tau_two] at h; norm_num at h
  have h3 : p ≠ 3 := by rintro rfl; rw [tau_three] at h; norm_num at h
  have h5 : p ≠ 5 := by rintro rfl; rw [tau_five] at h; norm_num at h
  obtain ⟨k, hk⟩ := condA hp ht
  obtain ⟨k', hk'⟩ := condB hp ht
  refine ⟨?_, ?_, ?_⟩
  · have hz : (({leanQ(m1['Q'],'(p : ℤ)')} : ℤ) : ZMod 512) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_trans (by norm_num) ⟨k, hk⟩
    push_cast at hz
    rcases dA512 (p : ZMod 512) hz with hx | hx <;> rw [ZMod.val_natCast] at hx
    · exact absurd (prime_eq_of_dvd hp Nat.prime_two (by omega)) h2
    · exact hx
  · have hz : (({leanQ(m1['Q'],'(p : ℤ)')} : ℤ) : ZMod 243) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_trans (by norm_num) ⟨k, hk⟩
    push_cast at hz
    rcases dA243 (p : ZMod 243) hz with hx | hx <;> rw [ZMod.val_natCast] at hx
    · exact absurd (prime_eq_of_dvd hp Nat.prime_three (by omega)) h3
    · exact hx
  · have hz : (({leanQ(m2['Q'],'(p : ℤ)')} : ℤ) : ZMod 125) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨k', hk'⟩
    push_cast at hz
    rcases dB125 (p : ZMod 125) hz with hx | hx <;> rw [ZMod.val_natCast] at hx
    · exact absurd (prime_eq_of_dvd hp Nat.prime_five (by omega)) h5
    · exact hx

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.linA
#print axioms RamanujanTau.LehmerSmall.linB
#print axioms RamanujanTau.LehmerSmall.prime_zero_deep
''')
open('QuasiLin.lean','w').write('\n'.join(out))
print("written")
