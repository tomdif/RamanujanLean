import RamanujanTau.FiniteArithmetic.Rank2Main
import RamanujanTau.FiniteArithmetic.PackedPrime
import RamanujanTau.FiniteArithmetic.ModularCertificate

/-!
# Rank two from one packed kernel computation

`Rank2Packed.run` computes, modulo `p²`, packed prefixes of the basis forms
`fᵢ = Δ^{jᵢ} E₄^{aᵢ} E₆^{bᵢ}`, of `Φ fᵢ`, of `E_{p-1}⁻¹ Φ fᵢ`, and of `Φ`
(`PackedPrime.prelude`). `check` compares the needed lanes with proposed matrices.
`bEll_of_check` turns a successful check, and finitely many identities in `ZMod p`, into
Boylan–Webb's `b_p(m) = 2m − 1` for every `m ≥ 1` (`Rank2.Data2.bEll_eq`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank2Packed

open PowerSeries Packed PackedPrime BoylanWebb AtkinOBrien AtkinOBrienFinal
open MockTheta5.JTP (qfacInf partitionGF)

/-! ### Certified `U` from coefficients -/

theorem U_eq_of_coeffs (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : ℕ) (he : 1 ≤ e) (w : ℤ) (m : ℕ)
    (hw : w + (m : ℤ) * ((p - 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ))
    (a b : PowerSeries ℤ) (ha : IntForm ((e + 1 : ℕ) : ℤ) a)
    (ha0 : coeff 0 a = 0) (hb : IntForm w b)
    (check : ∀ n, n ≤ (e + 1) / 12 → coeff (p * n) (Ψ p a) = coeff n (Ψ p b)) :
    U p (Ψ p a) = Ψ p b := by
  obtain ⟨A, hA, hAe⟩ := exists_hasse_lift p hp
  have htarget : Ψ p (b * A ^ m) = Ψ p b := by
    rw [map_mul, map_pow, hAe, one_pow, mul_one]
  have h := U_eq_of_sturm p e he a (b * A ^ m) ha ha0 ((hb.mul (hA.pow m)).cast hw)
    (fun n hn => by rw [htarget]; exact check n hn)
  exact h.trans htarget

/-! ### The program -/

/-- `a^e`, by repeated multiplication. -/
def powP (p N a : ℕ) : ℕ → Option ℕ
  | 0 => some 1
  | e + 1 => do
    let b ← powP p N a e
    mulP p N b a

/-- `Δ^j E₄^a E₆^b`. -/
def mono (p N : ℕ) (pr : Prelude) (ex : ℕ × ℕ × ℕ) : Option ℕ := do
  let x ← powP p N pr.dq ex.1
  let y ← powP p N pr.e4 ex.2.1
  let z ← powP p N pr.e6 ex.2.2
  let xy ← mulP p N x y
  mulP p N xy z

structure Params where
  p : ℕ
  N : ℕ
  c : ℕ
  R : ℕ
  d : ℕ
  k : ℕ
  n : ℕ
  ku : ℕ
  kb : ℕ
  kc : ℕ
  ex : Fin 3 → ℕ × ℕ × ℕ

structure Out where
  pr : Prelude
  F : Fin 3 → ℕ
  PF : Fin 3 → ℕ
  EF : Fin 3 → ℕ

def run (P : Params) : Option Out := do
  let pr ← prelude 13 P.p P.N P.c P.R P.d P.k P.n P.ku P.kb P.kc
  let F0 ← mono P.p P.N pr (P.ex 0)
  let F1 ← mono P.p P.N pr (P.ex 1)
  let F2 ← mono P.p P.N pr (P.ex 2)
  let G0 ← mulP P.p P.N pr.phi F0
  let G1 ← mulP P.p P.N pr.phi F1
  let G2 ← mulP P.p P.N pr.phi F2
  let H0 ← mulP P.p P.N pr.einv G0
  let H1 ← mulP P.p P.N pr.einv G1
  let H2 ← mulP P.p P.N pr.einv G2
  return ⟨pr, ![F0, F1, F2], ![G0, G1, G2], ![H0, H1, H2]⟩

/-- The proposed data. -/
structure Table where
  B : Fin 3 → Fin 3 → ℕ
  Um : Fin 3 → Fin 3 → ℕ
  Dm : Fin 3 → Fin 3 → ℕ
  seed : Fin 3 → ℕ
  w : Fin 3 → ℕ
  z : Fin 3 → ℕ
  zL2 : ℕ

/-- `Σⱼ Mⱼᵢ · lane(Fⱼ, n)`. -/
def combLane (M : Fin 3 → Fin 3 → ℕ) (F : Fin 3 → ℕ) (i : Fin 3) (n : ℕ) : ℕ :=
  M 0 i * lane (F 0) n + M 1 i * lane (F 1) n + M 2 i * lane (F 2) n

def obsLane (p : ℕ) (w : Fin 3 → ℕ) (a : ℕ) : ℕ :=
  w 0 * lane a (p ^ 2 * 1) + w 1 * lane a (p ^ 2 * 2) + w 2 * lane a (p ^ 2 * 3)

/-- All lane comparisons. -/
def check (P : Params) (T : Table) (o : Out) : Bool :=
  let p := P.p
  let δ := (p ^ 2 - 1) / 24
  (List.finRange 3).all fun i =>
    ((List.finRange 3).all fun k => lane (o.F i) (k.val + 1) % p == T.B k i) &&
    ((List.range 4).all fun n => lane (o.F i) (p * n) % p == combLane T.Um o.F i n % p) &&
    ((List.range (δ + 4)).all fun n => lane (o.PF i) (p * n) % p == combLane T.Dm o.F i n % p) &&
    (obsLane p T.w (o.EF i) % p ^ 2 == p * T.z i % p ^ 2) &&
    ((List.range (δ + 1)).all fun n =>
      lane o.pr.phi (p * n) % p == (T.seed 0 * lane (o.F 0) n + T.seed 1 * lane (o.F 1) n +
        T.seed 2 * lane (o.F 2) n) % p) &&
    (obsLane p T.w o.pr.phi % p ^ 2 == p * T.zL2 % p ^ 2)

/-- The kernel-evaluated statement. -/
def ok (P : Params) (T : Table) : Bool :=
  match run P with
  | some o => check P T o
  | none => false

/-! ### Unrolling the program -/

section Spec
variable {p N lv : ℕ} [hp : Fact p.Prime]

lemma powP_rep (hQ : p ^ 2 ≤ 2 ^ 21) (hlv : lv < 20) (hN : N ≤ 2 ^ lv) (hN0 : 0 < N) {a : ℕ}
    {f : PowerSeries (Rr p)} (ha : Rep N 22 a f) (e : ℕ) {r : ℕ} (h : powP p N a e = some r) :
    Rep N 22 r (f ^ e) := by
  induction e generalizing r with
  | zero =>
    obtain rfl : 1 = r := Option.some.inj h
    simpa using rep_one (p := p) hN0
  | succ e ih =>
    obtain ⟨b, h0, h1⟩ := bind_some h
    rw [pow_succ f e]
    exact rmul hQ hlv hN (ih h0) ha h1

lemma mono_rep (hQ : p ^ 2 ≤ 2 ^ 21) (hlv : lv < 20) (hN : N ≤ 2 ^ lv) (hN0 : 0 < N) {pr : Prelude}
    (hd : Rep N 22 pr.dq (ModP.Dq (Rr p))) (h4 : Rep N 22 pr.e4 (ModP.E4 (Rr p)))
    (h6 : Rep N 22 pr.e6 (ModP.E6 (Rr p))) (ex : ℕ × ℕ × ℕ) {r : ℕ}
    (h : mono p N pr ex = some r) :
    Rep N 22 r (rd p (Dz ^ ex.1 * Mod691.p4 ^ ex.2.1 * Mod691.p6 ^ ex.2.2)) := by
  unfold mono at h
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨z, hz, h⟩ := bind_some h
  obtain ⟨xy, hxy, h⟩ := bind_some h
  have r := rmul hQ hlv hN (rmul hQ hlv hN (powP_rep hQ hlv hN hN0 hd _ hx)
    (powP_rep hQ hlv hN hN0 h4 _ hy) hxy) (powP_rep hQ hlv hN hN0 h6 _ hz) h
  simpa [map_mul, map_pow, ModP.Dq, ModP.E4, ModP.E6] using r

/-- The coefficient bridge from a packed lane modulo `p²` to `Ψ p`. -/
lemma coeff_psi {g : PowerSeries ℤ} {a : ℕ} (h : Rep N 22 a (rd p g)) {n : ℕ} (hn : n < N) :
    coeff n (Ψ p g) = ((lane a n : ℕ) : ZMod p) := by
  have h1 := h.coeff n hn
  rw [rd, coeff_map] at h1
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h2 := congrArg (ZMod.castHom hdvd (ZMod p)) h1
  simp only [map_intCast, map_natCast, eq_intCast] at h2
  rw [Ψ, coeff_map, eq_intCast]
  exact h2.symm

lemma natCast_mod_p (a : ℕ) : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := ZMod.natCast_mod a p

end Spec

/-! ### The data, from tables -/

/-- The basis form with exponents `(j, a, b)`. -/
noncomputable def fz (ex : ℕ × ℕ × ℕ) : PowerSeries ℤ := Dz ^ ex.1 * Mod691.p4 ^ ex.2.1 * Mod691.p6 ^ ex.2.2

/-- The identities in `ZMod p`, proposed with the tables. -/
structure Extra where
  Binv : Fin 3 → Fin 3 → ℕ
  lam : ℕ
  θ : ℕ
  μ : Fin 3 → ℕ
  k₀ : ℕ
  k₁ : ℕ

section Tables
variable (p : ℕ)

def castM (M : Fin 3 → Fin 3 → ℕ) : Fin 3 → Fin 3 → ZMod p := fun j i => (M j i : ZMod p)

def oddT (T : Table) : ℕ → Fin 3 → ZMod p
  | 0 => fun j => (T.seed j : ZMod p)
  | n + 1 => Rank2.mv (castM p T.Dm) (Rank2.mv (castM p T.Um) (oddT T n))

def linT (T : Table) (k : Fin 3) (v : Fin 3 → ZMod p) : ZMod p := ∑ i, castM p T.B k i * v i

def detT (T : Table) : ZMod p :=
  linT p T 1 (oddT p T 0) * linT p T 2 (oddT p T 1) - linT p T 1 (oddT p T 1) * linT p T 2 (oddT p T 0)

def initT (T : Table) (X : Extra) : ZMod p :=
  ∑ i, Rank2.mv (castM p T.Um) (oddT p T 1) i * (T.z i : ZMod p) -
    (X.k₁ : ZMod p) * ∑ i, Rank2.mv (castM p T.Um) (oddT p T 0) i * (T.z i : ZMod p) -
      (X.k₀ : ZMod p) * (T.zL2 : ZMod p)

/-- Everything checked in `ZMod p`. -/
structure Identities (T : Table) (X : Extra) : Prop where
  BBinv : ∀ k j, ∑ i, castM p T.B k i * castM p X.Binv i j = if k = j then 1 else 0
  BinvB : ∀ i j, ∑ k, castM p X.Binv i k * castM p T.B k j = if i = j then 1 else 0
  kill : ∀ i, ∑ j, (∑ k, ((T.w k : ℕ) : ZMod p) * castM p T.B k j) * castM p T.Um j i =
    (X.lam : ZMod p) * castM p T.B 0 i
  theta : ∀ i, ((T.z i : ℕ) : ZMod p) =
    (X.θ : ZMod p) * (∑ k, ((T.w k : ℕ) : ZMod p) * castM p T.B k i) +
      ∑ j, (X.μ j : ZMod p) * castM p T.Dm j i
  cay : oddT p T 2 = (X.k₁ : ZMod p) • oddT p T 1 + (X.k₀ : ZMod p) • oddT p T 0
  k₀ : (X.k₀ : ZMod p) ≠ 0
  det : detT p T ≠ 0
  θ₀ : (X.θ : ZMod p) ≠ 0
  init : initT p T X ≠ 0

end Tables

/-- The size and parameter conditions, all decidable. -/
structure Sizes (P : Params) : Prop where
  h29 : 29 ≤ P.p
  hsturm : (P.p - 1) / 12 + 1 ≤ 4
  h24 : 24 * ((P.p ^ 2 - 1) / 24) + 1 = P.p ^ 2
  hQ : P.p ^ 2 ≤ 2 ^ 21
  hN0 : 0 < P.N
  hN : P.N ≤ 2 ^ 13
  hN5 : P.N ≤ 5 * P.p ^ 2
  hp3 : P.N < P.p ^ 3
  hN3 : 3 * P.p ^ 2 < P.N
  hNd : P.p * ((P.p ^ 2 - 1) / 24 + 3) < P.N
  hc : (24 * P.c + 1) % P.p = 0
  hk : P.ku + P.kb + 13 < 64
  hno : 2 ^ 22 + P.p ^ 2 * 2 ^ P.kc ≤ x
  hn : P.k * 2 ^ P.d ≤ 2 ^ 20
  hJ : P.N ≤ PartitionPrefix.pentLow (P.k * 2 ^ P.d)
  hw : ∀ i, 12 * (P.ex i).1 + 4 * (P.ex i).2.1 + 6 * (P.ex i).2.2 = P.p - 1
  hj : ∀ i, 1 ≤ (P.ex i).1
  hmD : (P.p - 1) + (P.p + 1) / 2 * (P.p - 1) = 12 * ((P.p ^ 2 - 1) / 24) + (P.p - 1)
  hmS : (P.p - 1) + (P.p - 1) / 2 * (P.p - 1) = 12 * ((P.p ^ 2 - 1) / 24)

section Run
variable {P : Params} [hp : Fact P.p.Prime]

theorem run_spec (hs : Sizes P) {o : Out} (h : run P = some o) :
    (∀ i, Rep P.N 22 (o.F i) (rd P.p (fz (P.ex i)))) ∧
    (∀ i, Rep P.N 22 (o.PF i) (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz (P.ex i)))) ∧
    (∀ i, Rep P.N 22 (o.EF i) (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
      (Einv P.p (by have := hs.h29; omega)) * (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz (P.ex i))))) ∧
    Rep P.N 22 o.pr.phi (rd P.p (BoylanWebb.Φ P.p)) := by
  have hp5 : 5 ≤ P.p := by have := hs.h29; omega
  unfold run at h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨F0, hF0, h⟩ := bind_some h
  obtain ⟨F1, hF1, h⟩ := bind_some h
  obtain ⟨F2, hF2, h⟩ := bind_some h
  obtain ⟨G0, hG0, h⟩ := bind_some h
  obtain ⟨G1, hG1, h⟩ := bind_some h
  obtain ⟨G2, hG2, h⟩ := bind_some h
  obtain ⟨H0, hH0, h⟩ := bind_some h
  obtain ⟨H1, hH1, h⟩ := bind_some h
  obtain ⟨H2, hH2, h⟩ := bind_some h
  obtain rfl := Option.some.inj h
  have sp := prelude_spec hp5 hs.hQ hs.hN0 (by norm_num) hs.hN (by have := hs.hN5; omega) hs.hp3 hs.hc hs.hk hs.hno hs.hn hs.hJ hpr
  have rF : ∀ i : Fin 3, ∀ r, mono P.p P.N pr (P.ex i) = some r → Rep P.N 22 r (rd P.p (fz (P.ex i))) :=
    fun i r hr => mono_rep hs.hQ (by norm_num) hs.hN hs.hN0 sp.dq sp.e4 sp.e6 _ hr
  have r0 := rF 0 _ hF0
  have r1 := rF 1 _ hF1
  have r2 := rF 2 _ hF2
  have q0 := rmul hs.hQ (by norm_num) hs.hN sp.phi r0 hG0
  have q1 := rmul hs.hQ (by norm_num) hs.hN sp.phi r1 hG1
  have q2 := rmul hs.hQ (by norm_num) hs.hN sp.phi r2 hG2
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, sp.phi⟩
  · fin_cases i
    · exact r0
    · exact r1
    · exact r2
  · fin_cases i
    · exact q0
    · exact q1
    · exact q2
  · fin_cases i
    · exact rmul hs.hQ (by norm_num) hs.hN sp.einv q0 hH0
    · exact rmul hs.hQ (by norm_num) hs.hN sp.einv q1 hH1
    · exact rmul hs.hQ (by norm_num) hs.hN sp.einv q2 hH2

omit hp in
theorem check_spec {T : Table} {o : Out} (h : check P T o = true) :
    (∀ i k : Fin 3, lane (o.F i) (k.val + 1) % P.p = T.B k i) ∧
    (∀ i : Fin 3, ∀ n < 4, lane (o.F i) (P.p * n) % P.p = combLane T.Um o.F i n % P.p) ∧
    (∀ i : Fin 3, ∀ n < (P.p ^ 2 - 1) / 24 + 4,
      lane (o.PF i) (P.p * n) % P.p = combLane T.Dm o.F i n % P.p) ∧
    (∀ i : Fin 3, obsLane P.p T.w (o.EF i) % P.p ^ 2 = P.p * T.z i % P.p ^ 2) ∧
    (∀ n < (P.p ^ 2 - 1) / 24 + 1, lane o.pr.phi (P.p * n) % P.p =
      (T.seed 0 * lane (o.F 0) n + T.seed 1 * lane (o.F 1) n + T.seed 2 * lane (o.F 2) n) % P.p) ∧
    (obsLane P.p T.w o.pr.phi % P.p ^ 2 = P.p * T.zL2 % P.p ^ 2) := by
  simp only [check, List.all_eq_true, List.mem_finRange, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, forall_const, true_implies] at h
  refine ⟨fun i k => (h i).1.1.1.1.1 k, fun i n hn => (h i).1.1.1.1.2 n hn,
    fun i n hn => (h i).1.1.1.2 n hn, fun i => (h i).1.1.2, fun n hn => (h 0).1.2 n hn, (h 0).2⟩

end Run

/-! ### Forms, combinations and coefficient bridges -/

section Final
variable {P : Params} {T : Table} {X : Extra} [hp : Fact P.p.Prime]

lemma form_fz (hs : Sizes P) (i : Fin 3) : IntForm ((P.p - 1 : ℕ) : ℤ) (fz (P.ex i)) := by
  have h := ((IntForm.disc.pow (P.ex i).1).mul (IntForm.E4.pow (P.ex i).2.1)).mul
    (IntForm.E6.pow (P.ex i).2.2)
  refine h.cast ?_
  rw [← hs.hw i]; push_cast; ring

lemma cusp_fz (hs : Sizes P) (i : Fin 3) : coeff 0 (fz (P.ex i)) = 0 := by
  rw [fz, mul_assoc]; exact coeff_zero_Dz_pow (hs.hj i) _

/-- `Σⱼ Mⱼᵢ fⱼ`. -/
noncomputable def bcomb (P : Params) (M : Fin 3 → Fin 3 → ℕ) (i : Fin 3) : PowerSeries ℤ :=
  ∑ j, PowerSeries.C ((M j i : ℕ) : ℤ) * fz (P.ex j)

lemma form_bcomb (hs : Sizes P) (M : Fin 3 → Fin 3 → ℕ) (i : Fin 3) :
    IntForm ((P.p - 1 : ℕ) : ℤ) (bcomb P M i) := by
  simp only [bcomb, Fin.sum_univ_three]
  exact (((form_fz hs 0).C_mul _).add ((form_fz hs 1).C_mul _)).add ((form_fz hs 2).C_mul _)

lemma psi_bcomb (M : Fin 3 → Fin 3 → ℕ) (i : Fin 3) :
    Ψ P.p (bcomb P M i) = ∑ j, C ((M j i : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j)) := by
  rw [bcomb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, PowerSeries.map_C]
  congr 2
  simp

lemma coeff_bcomb {o : Out} (rF : ∀ i, Rep P.N 22 (o.F i) (rd P.p (fz (P.ex i))))
    (M : Fin 3 → Fin 3 → ℕ) (i : Fin 3) {n : ℕ} (hn : n < P.N) :
    coeff n (Ψ P.p (bcomb P M i)) = ((combLane M o.F i n : ℕ) : ZMod P.p) := by
  rw [psi_bcomb, map_sum, Fin.sum_univ_three]
  simp only [coeff_C_mul, coeff_psi (rF _) hn, combLane]
  push_cast; ring

lemma mod_eq_cast {a b : ℕ} (h : a % P.p = b % P.p) : (a : ZMod P.p) = (b : ZMod P.p) := by
  rw [← ZMod.natCast_mod a, h, ZMod.natCast_mod]

lemma alg3 {S : Type*} [CommRing S] (a b c : S) : a * (b * c) = c * (a * b) := by ring

lemma map_map_sq (g : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZModPow (p := P.p) 2) (PowerSeries.map (Int.castRingHom ℤ_[P.p]) g) =
      rd P.p g := by
  ext n
  simp [coeff_map]

lemma exists_of_toZModPow (x : ℤ_[P.p]) (z : ℕ)
    (h : PadicInt.toZModPow 2 x = ((P.p * z : ℕ) : ZMod (P.p ^ 2))) :
    ∃ t : ℤ_[P.p], x = (P.p : ℤ_[P.p]) * ((z : ℤ_[P.p]) + P.p * t) := by
  have hk : x - ((P.p * z : ℕ) : ℤ_[P.p]) ∈ RingHom.ker (PadicInt.toZModPow (p := P.p) 2) := by
    rw [RingHom.mem_ker, map_sub, h, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  refine ⟨t, ?_⟩
  push_cast at ht
  linear_combination -ht

/-- `obs(Y F) mod p²` from one packed product. -/
lemma obs_lane (hs : Sizes P) (F : PS P.p) {a : ℕ}
    (hrep : Rep P.N 22 a (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2) (Φl P.p * F))) :
    PadicInt.toZModPow 2 (Rank2.obs (fun k => ((T.w k : ℕ) : ℤ)) (Rank2.Yop F)) =
      ((obsLane P.p T.w a : ℕ) : ZMod (P.p ^ 2)) := by
  have hb : ∀ k : ℕ, k < 3 → P.p * (P.p * (k + 1)) < P.N := fun k hk => by
    have := hs.hN3
    calc P.p * (P.p * (k + 1)) = P.p ^ 2 * (k + 1) := by ring
      _ ≤ P.p ^ 2 * 3 := Nat.mul_le_mul_left _ (by omega)
      _ < P.N := by omega
  have hc : ∀ k : ℕ, k < 3 → PadicInt.toZModPow 2 (coeff (k + 1) (Rank2.Yop F)) =
      ((lane a (P.p ^ 2 * (k + 1)) : ℕ) : ZMod (P.p ^ 2)) := fun k hk => by
    change PadicInt.toZModPow 2 (coeff (k + 1) (BoylanWebb.U P.p (BoylanWebb.U P.p (Φl P.p * F)))) = _
    rw [coeff_U, coeff_U, ← coeff_map, ← hrep.coeff _ (hb k hk), show P.p * (P.p * (k + 1)) =
      P.p ^ 2 * (k + 1) by ring]
  rw [Rank2.obs_apply, Fin.sum_univ_three, map_add, map_add, map_mul, map_mul, map_mul]
  simp only [map_intCast, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), obsLane]
  push_cast; ring

/-- The polynomial `Pdisc^j X₀^a X₁^b` of a basis form. -/
noncomputable def Pm (hp5 : 5 ≤ P.p) (ex : ℕ × ℕ × ℕ) : Poly P.p :=
  DBound.Pdisc hp5 ^ ex.1 * MvPolynomial.X 0 ^ ex.2.1 * MvPolynomial.X 1 ^ ex.2.2

lemma iso_Pm (hs : Sizes P) (hp5 : 5 ≤ P.p) (i : Fin 3) : ModP.Iso (Pm hp5 (P.ex i)) (P.p - 1) := by
  have i0 : ModP.Iso (MvPolynomial.X 0 : Poly P.p) 4 := by
    simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[P.p] ModP.wt (0 : Fin 2)
  have i1 : ModP.Iso (MvPolynomial.X 1 : Poly P.p) 6 := by
    simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[P.p] ModP.wt (1 : Fin 2)
  refine ModP.iso_of_eq ((((DBound.iso_Pdisc hp5).pow (P.ex i).1).mul (i0.pow (P.ex i).2.1)).mul
    (i1.pow (P.ex i).2.2)) ?_
  rw [← hs.hw i]; ring

lemma ev_Pm (hp5 : 5 ≤ P.p) (i : Fin 3) :
    ModP.ev ℤ_[P.p] (Pm hp5 (P.ex i)) = PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) := by
  simp only [Pm, map_mul, map_pow, DBound.ev_Pdisc, ModP.ev_X0, ModP.ev_X1, fz]
  simp only [DBound.Dl, ModP.Dq, ModP.E4, ModP.E6, map_mul, map_pow]

/-- **`b_p(m) = 2m − 1` from one kernel evaluation and identities in `ZMod p`.** -/
theorem bEll_of_ok (hs : Sizes P) (hid : Identities P.p T X) (hok : ok P T = true) (m : ℕ)
    (hm : 1 ≤ m) : BLBound.bEll P.p m = 2 * m - 1 := by
  have hp5 : 5 ≤ P.p := by have := hs.h29; omega
  have h24 : 24 * BoylanWebb.δ P.p + 1 = P.p ^ 2 := hs.h24
  have hδ : BoylanWebb.δ P.p = (P.p ^ 2 - 1) / 24 := rfl
  have hδ1 : 1 ≤ BoylanWebb.δ P.p := by
    have h1 : 29 * 29 ≤ P.p ^ 2 := by nlinarith [hs.h29]
    omega
  unfold ok at hok
  cases hr : run P with
  | none => rw [hr] at hok; exact absurd hok (by simp)
  | some o =>
  rw [hr] at hok
  obtain ⟨rF, rPF, rEF, rphi⟩ := run_spec hs hr
  obtain ⟨cB, cU, cD, cZ, cS, cL⟩ := check_spec hok
  have hN3 := hs.hN3
  have hNd := hs.hNd
  have hst := hs.hsturm
  have hlt3 : ∀ n, n ≤ 3 → P.p * n < P.N := fun n hn => by
    have : P.p * n ≤ P.p * 3 := Nat.mul_le_mul_left _ hn
    have : P.p * 3 ≤ 3 * P.p ^ 2 := by nlinarith [hs.h29]
    omega
  -- `B`
  have hB : ∀ (k i : Fin 3), coeff (k.val + 1) (Ψ P.p (fz (P.ex i))) = castM P.p T.B k i := by
    intro k i
    rw [coeff_psi (rF i) (by have := k.isLt; omega), castM, ← ZMod.natCast_mod, cB i k]
  -- `U`
  have hU : ∀ i, U P.p (Ψ P.p (fz (P.ex i))) =
      ∑ j, C (castM P.p T.Um j i) * Ψ P.p (fz (P.ex j)) := by
    intro i
    rw [show (∑ j, C (castM P.p T.Um j i) * Ψ P.p (fz (P.ex j))) = Ψ P.p (bcomb P T.Um i) from
      (psi_bcomb T.Um i).symm]
    have he : P.p - 2 + 1 = P.p - 1 := by omega
    refine U_eq_of_coeffs P.p hp5 (P.p - 2) (by omega) ((P.p - 1 : ℕ) : ℤ) 0 (by rw [he]; simp) _ _
      ((form_fz hs i).cast (by rw [he])) (cusp_fz hs i) (form_bcomb hs _ i) fun n hn => ?_
    have hn3 : n ≤ 3 := by rw [he] at hn; omega
    rw [coeff_psi (rF i) (hlt3 n hn3), coeff_bcomb rF _ i (by have := hlt3 n hn3; nlinarith)]
    exact mod_eq_cast (cU i n (by omega))
  -- `D`
  have hD : ∀ i, U P.p (Ψ P.p (Dz ^ BoylanWebb.δ P.p) * Ψ P.p (fz (P.ex i))) =
      ∑ j, C (castM P.p T.Dm j i) * Ψ P.p (fz (P.ex j)) := by
    intro i
    rw [← map_mul, show (∑ j, C (castM P.p T.Dm j i) * Ψ P.p (fz (P.ex j))) =
      Ψ P.p (bcomb P T.Dm i) from (psi_bcomb T.Dm i).symm]
    set e := 12 * BoylanWebb.δ P.p + (P.p - 1) - 1
    have he : e + 1 = 12 * BoylanWebb.δ P.p + (P.p - 1) := by omega
    have hw : (((P.p - 1 : ℕ) : ℤ) + (((P.p + 1) / 2 : ℕ) : ℤ) * ((P.p - 1 : ℕ) : ℤ)) =
        ((e + 1 : ℕ) : ℤ) := by
      rw [he]; exact_mod_cast (by rw [hδ]; exact hs.hmD)
    refine U_eq_of_coeffs P.p hp5 e (by omega) ((P.p - 1 : ℕ) : ℤ) ((P.p + 1) / 2) hw _ _
      (((IntForm.disc.pow (BoylanWebb.δ P.p)).mul (form_fz hs i)).cast (by rw [he]; push_cast; ring))
      (coeff_zero_Dz_pow hδ1 _) (form_bcomb hs _ i) fun n hn => ?_
    have hn' : n ≤ BoylanWebb.δ P.p + 3 := by
      rw [he] at hn
      have : (12 * BoylanWebb.δ P.p + (P.p - 1)) / 12 = BoylanWebb.δ P.p + (P.p - 1) / 12 := by omega
      omega
    have hpn : P.p * n < P.N := by
      have : P.p * n ≤ P.p * (BoylanWebb.δ P.p + 3) := Nat.mul_le_mul_left _ hn'
      rw [hδ] at this; omega
    have hΦ : Ψ P.p (Dz ^ BoylanWebb.δ P.p * fz (P.ex i)) = Ψ P.p (BoylanWebb.Φ P.p * fz (P.ex i)) := by
      rw [map_mul, map_mul, Ψ_Φ P.p h24]
    have rq : Rep P.N 22 (o.PF i) (rd P.p (BoylanWebb.Φ P.p * fz (P.ex i))) := by
      rw [map_mul]; exact rPF i
    rw [hΦ, coeff_psi rq hpn, coeff_bcomb rF _ i (by nlinarith)]
    exact mod_eq_cast (cD i n (by rw [← hδ]; omega))
  -- the seed
  have hS : U P.p (Ψ P.p (Dz ^ BoylanWebb.δ P.p)) =
      ∑ j, C ((T.seed j : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j)) := by
    rw [show (∑ j, C ((T.seed j : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j))) =
      Ψ P.p (bcomb P (fun j _ => T.seed j) 0) from (psi_bcomb (fun j _ => T.seed j) 0).symm]
    set e := 12 * BoylanWebb.δ P.p - 1
    have he : e + 1 = 12 * BoylanWebb.δ P.p := by omega
    have hw : (((P.p - 1 : ℕ) : ℤ) + (((P.p - 1) / 2 : ℕ) : ℤ) * ((P.p - 1 : ℕ) : ℤ)) =
        ((e + 1 : ℕ) : ℤ) := by
      rw [he]; exact_mod_cast (by rw [hδ]; exact hs.hmS)
    refine U_eq_of_coeffs P.p hp5 e (by omega) ((P.p - 1 : ℕ) : ℤ) ((P.p - 1) / 2) hw _ _
      ((IntForm.disc.pow (BoylanWebb.δ P.p)).cast (by rw [he]; push_cast; ring))
      (by simpa using coeff_zero_Dz_pow hδ1 1) (form_bcomb hs _ 0) fun n hn => ?_
    have hn' : n ≤ BoylanWebb.δ P.p := by rw [he] at hn; omega
    have hpn : P.p * n < P.N := by
      have : P.p * n ≤ P.p * (BoylanWebb.δ P.p + 3) := Nat.mul_le_mul_left _ (by omega)
      rw [hδ] at this; omega
    rw [← Ψ_Φ P.p h24, coeff_psi rphi hpn, coeff_bcomb rF _ 0 (by nlinarith)]
    refine mod_eq_cast ((cS n (by rw [← hδ]; omega)).trans ?_)
    simp only [combLane]
  -- `z`
  have hz : ∀ i, ∃ t : ℤ_[P.p], Rank2.obs (fun k => ((T.w k : ℕ) : ℤ))
      (Rank2.Yop (PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) * Einv P.p hp5)) =
      (P.p : ℤ_[P.p]) * ((((T.z i : ℕ) : ℤ) : ℤ_[P.p]) + P.p * t) := by
    intro i
    have hrep : Rep P.N 22 (o.EF i) (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
        (Φl P.p * (PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) * Einv P.p hp5))) := by
      rw [map_mul, map_mul, Φl, map_map_sq, map_map_sq, alg3]
      exact rEF i
    have h1 := obs_lane (T := T) hs _ hrep
    rw [← ZMod.natCast_mod, cZ i, ZMod.natCast_mod] at h1
    obtain ⟨t, ht⟩ := exists_of_toZModPow _ _ h1
    exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hL2 : ∃ t : ℤ_[P.p], Rank2.obs (fun k => ((T.w k : ℕ) : ℤ)) (Ll P.p 2) =
      (P.p : ℤ_[P.p]) * ((((T.zL2 : ℕ) : ℤ) : ℤ_[P.p]) + P.p * t) := by
    have hY : Ll P.p 2 = Rank2.Yop 1 := by
      rw [show 2 = 2 * 0 + 2 from rfl, Rank2.even_U, Rank2.odd_D]
      change Ulin P.p (Dlin P.p (Ll P.p 0)) = Rank2.Yop 1
      simp [Ll, BoylanWebb.L, Rank2.Yop]
    have hrep : Rep P.N 22 o.pr.phi (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
        (Φl P.p * 1)) := by
      rw [mul_one, Φl, map_map_sq]; exact rphi
    have h1 := obs_lane (T := T) hs _ hrep
    rw [← ZMod.natCast_mod, cL, ZMod.natCast_mod] at h1
    obtain ⟨t, ht⟩ := exists_of_toZModPow _ _ h1
    exact ⟨t, by rw [hY, ht]; push_cast; ring⟩
  -- assemble
  let D0 : Rank2.Data P.p := ⟨fun i => fz (P.ex i), form_fz hs, cusp_fz hs, hs.hsturm, hp5,
    castM P.p T.B, hB, castM P.p X.Binv, hid.BBinv, castM P.p T.Um, hU, castM P.p T.Dm, hD,
    fun j => (T.seed j : ZMod P.p), hS⟩
  let D : Rank2.Data2 P.p := ⟨D0, fun i => Pm hp5 (P.ex i), iso_Pm hs hp5, ev_Pm hp5, hid.BinvB,
    fun k => ((T.w k : ℕ) : ℤ), X.lam, by simpa using hid.kill, fun i => ((T.z i : ℕ) : ℤ), hz,
    X.θ, fun j => (X.μ j : ZMod P.p), by simpa using hid.theta⟩
  have hodd : ∀ n, D.odd n = oddT P.p T n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change Rank2.mv _ (Rank2.mv _ (D.odd n)) = _; rw [ih]; rfl
  have hcay : D.odd 2 = (X.k₁ : ZMod P.p) • D.odd 1 + (X.k₀ : ZMod P.p) • D.odd 0 := by
    rw [hodd, hodd, hodd]; exact hid.cay
  have hdet : D.det 0 ≠ 0 := by
    have : D.det 0 = detT P.p T := by
      simp only [Rank2.Data.det, hodd]; rfl
    rw [this]; exact hid.det
  have hinit : D.init (X.k₀ : ZMod P.p) (X.k₁ : ZMod P.p) ((T.zL2 : ℕ) : ℤ) ≠ 0 := by
    have : D.init (X.k₀ : ZMod P.p) (X.k₁ : ZMod P.p) ((T.zL2 : ℕ) : ℤ) = initT P.p T X := by
      have hzc : ∀ x, ((D.z x : ℤ) : ZMod P.p) = (T.z x : ZMod P.p) := fun x => Int.cast_natCast _
      simp only [Rank2.Data2.init, initT, hodd, hzc, Int.cast_natCast]; rfl
    rw [this]; exact hid.init
  exact D.bEll_eq hs.h29 h24 hcay hid.k₀ hdet _ hL2 hid.θ₀ hinit m hm

end Final

end RamanujanTau.FiniteArithmetic.Rank2Packed
