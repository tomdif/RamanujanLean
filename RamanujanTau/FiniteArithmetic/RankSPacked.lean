import RamanujanTau.FiniteArithmetic.RankSMain
import RamanujanTau.FiniteArithmetic.Rank2Packed

/-!
# `b_p(m) = 2m − 1` from one packed kernel computation, with `s + 2` forms

The `Rank2Packed` pipeline for `RankS`. `RankSPacked.run` computes, modulo `p²` and over `2^lv`
lanes, packed prefixes of the basis forms `fᵢ = Δ^{jᵢ} E₄^{aᵢ} E₆^{bᵢ}` (`i < s + 2`), of
`Φ fᵢ`, of `E_{p-1}⁻¹ Φ fᵢ`, and of `Φ` (`PackedPrime.prelude`). `check` compares the needed lanes
with proposed matrices. `bEll_of_ok` turns a successful check, and finitely many identities in
`ZMod p`, into `b_p(m) = 2m − 1` for every `m ≥ 1` (`RankS.Data2.bEll_eq`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankSPacked

open PowerSeries Packed PackedPrime BoylanWebb AtkinOBrien AtkinOBrienFinal
open Rank2Packed (powP mono fz U_eq_of_coeffs powP_rep mono_rep coeff_psi alg3)
open MockTheta5.JTP (qfacInf partitionGF)

/-! ### Finite sums and options over `Fin n`, by structural recursion -/

/-- `Σ_{i<n} f i`, computed by recursion (kernel-friendly). -/
def fsum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + fsum n (fun i => f i.succ)

lemma fsum_eq : ∀ (n : ℕ) (f : Fin n → ℕ), fsum n f = ∑ i, f i
  | 0, _ => by simp [fsum]
  | n + 1, f => by rw [fsum, fsum_eq n, Fin.sum_univ_succ]

/-- All of `g 0, …, g (n-1)`, or `none`. -/
def optAll {α : Type} : (n : ℕ) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, g => do
    let a ← g 0
    let r ← optAll n (fun i => g i.succ)
    return Fin.cons a r

lemma optAll_spec {α : Type} : ∀ (n : ℕ) (g : Fin n → Option α) (r : Fin n → α),
    optAll n g = some r → ∀ i, g i = some (r i)
  | 0, _, _, _, i => i.elim0
  | n + 1, g, r, h, i => by
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨r', hr', h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using optAll_spec n _ r' hr' j

/-! ### The program -/

structure Params (s : ℕ) where
  p : ℕ
  N : ℕ
  lv : ℕ
  c : ℕ
  R : ℕ
  d : ℕ
  k : ℕ
  n : ℕ
  ku : ℕ
  kb : ℕ
  kc : ℕ
  ex : Fin (s + 2) → ℕ × ℕ × ℕ

structure Out (s : ℕ) where
  pr : Prelude
  F : Fin (s + 2) → ℕ
  PF : Fin (s + 2) → ℕ
  EF : Fin (s + 2) → ℕ

/-- `(f, Φ f, E⁻¹ Φ f)` for one basis form. -/
def formLanes {s : ℕ} (P : Params s) (pr : Prelude) (ex : ℕ × ℕ × ℕ) : Option (ℕ × ℕ × ℕ) := do
  let F ← mono P.p P.N pr ex
  let G ← mulP P.p P.N pr.phi F
  let H ← mulP P.p P.N pr.einv G
  return (F, G, H)

def run {s : ℕ} (P : Params s) : Option (Out s) := do
  let pr ← prelude P.lv P.p P.N P.c P.R P.d P.k P.n P.ku P.kb P.kc
  let L ← optAll (s + 2) (fun i => formLanes P pr (P.ex i))
  return ⟨pr, fun i => (L i).1, fun i => (L i).2.1, fun i => (L i).2.2⟩

/-- The proposed data. -/
structure Table (s : ℕ) where
  B : Fin (s + 2) → Fin (s + 2) → ℕ
  Um : Fin (s + 2) → Fin (s + 2) → ℕ
  Dm : Fin (s + 2) → Fin (s + 2) → ℕ
  seed : Fin (s + 2) → ℕ
  w : Fin s → Fin (s + 2) → ℕ
  z : Fin s → Fin (s + 2) → ℕ
  zL2 : Fin s → ℕ

/-- `Σⱼ Mⱼᵢ · lane(Fⱼ, n)`. -/
def combLane {s : ℕ} (M : Fin (s + 2) → Fin (s + 2) → ℕ) (F : Fin (s + 2) → ℕ) (i : Fin (s + 2))
    (n : ℕ) : ℕ :=
  fsum (s + 2) fun j => M j i * lane (F j) n

def obsLane {s : ℕ} (p : ℕ) (w : Fin (s + 2) → ℕ) (a : ℕ) : ℕ :=
  fsum (s + 2) fun k => w k * lane a (p ^ 2 * (k.val + 1))

/-- All lane comparisons. -/
def check {s : ℕ} (P : Params s) (T : Table s) (o : Out s) : Bool :=
  let p := P.p
  let δ := (p ^ 2 - 1) / 24
  let t := (p - 1) / 12
  ((List.finRange (s + 2)).all fun i => (List.finRange (s + 2)).all fun k =>
    lane (o.F i) (k.val + 1) % p == T.B k i) &&
  ((List.finRange (s + 2)).all fun i => (List.range (t + 1)).all fun n =>
    lane (o.F i) (p * n) % p == combLane T.Um o.F i n % p) &&
  ((List.finRange (s + 2)).all fun i => (List.range (δ + t + 1)).all fun n =>
    lane (o.PF i) (p * n) % p == combLane T.Dm o.F i n % p) &&
  ((List.finRange s).all fun a => (List.finRange (s + 2)).all fun i =>
    obsLane p (T.w a) (o.EF i) % p ^ 2 == p * T.z a i % p ^ 2) &&
  ((List.range (δ + 1)).all fun n =>
    lane o.pr.phi (p * n) % p == combLane (fun j _ => T.seed j) o.F 0 n % p) &&
  ((List.finRange s).all fun a => obsLane p (T.w a) o.pr.phi % p ^ 2 == p * T.zL2 a % p ^ 2)

/-- The kernel-evaluated statement. -/
def ok {s : ℕ} (P : Params s) (T : Table s) : Bool :=
  match run P with
  | some o => check P T o
  | none => false

/-! ### Unrolling the program -/

/-- The identities in `ZMod p`, proposed with the tables. -/
structure Extra (s : ℕ) where
  Binv : Fin (s + 2) → Fin (s + 2) → ℕ
  lam : Fin s → Fin s → ℕ
  θ : Fin s → Fin s → ℕ
  θi : Fin s → Fin s → ℕ
  μ : Fin s → Fin (s + 2) → ℕ
  k₀ : ℕ
  k₁ : ℕ

/-- The size and parameter conditions, all decidable. -/
structure Sizes {s : ℕ} (P : Params s) : Prop where
  h29 : 29 ≤ P.p
  hsturm : (P.p - 1) / 12 + 1 ≤ s + 3
  hlow : P.p * s < (P.p ^ 2 - 1) / 24
  h24 : 24 * ((P.p ^ 2 - 1) / 24) + 1 = P.p ^ 2
  hQ : P.p ^ 2 ≤ 2 ^ 21
  hN0 : 0 < P.N
  hlv : P.lv < 20
  hN : P.N ≤ 2 ^ P.lv
  hN5 : P.N ≤ 5 * P.p ^ 2
  hp3 : P.N < P.p ^ 3
  hN3 : (s + 2) * P.p ^ 2 < P.N
  hNd : P.p * ((P.p ^ 2 - 1) / 24 + (P.p - 1) / 12) < P.N
  hc : (24 * P.c + 1) % P.p = 0
  hk : P.ku + P.kb + P.lv < 64
  hno : 2 ^ 22 + P.p ^ 2 * 2 ^ P.kc ≤ x
  hn : P.k * 2 ^ P.d ≤ 2 ^ 20
  hJ : P.N ≤ PartitionPrefix.pentLow (P.k * 2 ^ P.d)
  hw : ∀ i, 12 * (P.ex i).1 + 4 * (P.ex i).2.1 + 6 * (P.ex i).2.2 = P.p - 1
  hj : ∀ i, 1 ≤ (P.ex i).1
  hmD : (P.p - 1) + (P.p + 1) / 2 * (P.p - 1) = 12 * ((P.p ^ 2 - 1) / 24) + (P.p - 1)
  hmS : (P.p - 1) + (P.p - 1) / 2 * (P.p - 1) = 12 * ((P.p ^ 2 - 1) / 24)

section Run
variable {s : ℕ} {P : Params s} [hp : Fact P.p.Prime]

lemma formLanes_spec (hs : Sizes P) {pr : Prelude}
    (sp : PreludeSpec P.p P.N (by have := hs.h29; omega) pr)
    (ex : ℕ × ℕ × ℕ) {t : ℕ × ℕ × ℕ} (h : formLanes P pr ex = some t) :
    Rep P.N 22 t.1 (rd P.p (fz ex)) ∧
    Rep P.N 22 t.2.1 (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz ex)) ∧
    Rep P.N 22 t.2.2 (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
      (Einv P.p (by have := hs.h29; omega)) * (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz ex))) := by
  unfold formLanes at h
  obtain ⟨F, hF, h⟩ := bind_some h
  obtain ⟨G, hG, h⟩ := bind_some h
  obtain ⟨H, hH, h⟩ := bind_some h
  obtain rfl := Option.some.inj h
  have r0 : Rep P.N 22 F (rd P.p (fz ex)) :=
    mono_rep hs.hQ hs.hlv hs.hN hs.hN0 sp.dq sp.e4 sp.e6 ex hF
  have r1 := rmul hs.hQ hs.hlv hs.hN sp.phi r0 hG
  exact ⟨r0, r1, rmul hs.hQ hs.hlv hs.hN sp.einv r1 hH⟩

theorem run_spec (hs : Sizes P) {o : Out s} (h : run P = some o) :
    (∀ i, Rep P.N 22 (o.F i) (rd P.p (fz (P.ex i)))) ∧
    (∀ i, Rep P.N 22 (o.PF i) (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz (P.ex i)))) ∧
    (∀ i, Rep P.N 22 (o.EF i) (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
      (Einv P.p (by have := hs.h29; omega)) * (rd P.p (BoylanWebb.Φ P.p) * rd P.p (fz (P.ex i))))) ∧
    Rep P.N 22 o.pr.phi (rd P.p (BoylanWebb.Φ P.p)) := by
  have hp5 : 5 ≤ P.p := by have := hs.h29; omega
  unfold run at h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨L, hL, h⟩ := bind_some h
  obtain rfl := Option.some.inj h
  have sp := prelude_spec hp5 hs.hQ hs.hN0 hs.hlv hs.hN (by have := hs.hN5; omega) hs.hp3 hs.hc hs.hk hs.hno hs.hn hs.hJ hpr
  have hl := optAll_spec _ _ _ hL
  exact ⟨fun i => (formLanes_spec hs sp _ (hl i)).1, fun i => (formLanes_spec hs sp _ (hl i)).2.1,
    fun i => (formLanes_spec hs sp _ (hl i)).2.2, sp.phi⟩

omit hp in
theorem check_spec {T : Table s} {o : Out s} (h : check P T o = true) :
    (∀ i k : Fin (s + 2), lane (o.F i) (k.val + 1) % P.p = T.B k i) ∧
    (∀ i : Fin (s + 2), ∀ n < (P.p - 1) / 12 + 1,
      lane (o.F i) (P.p * n) % P.p = combLane T.Um o.F i n % P.p) ∧
    (∀ i : Fin (s + 2), ∀ n < (P.p ^ 2 - 1) / 24 + (P.p - 1) / 12 + 1,
      lane (o.PF i) (P.p * n) % P.p = combLane T.Dm o.F i n % P.p) ∧
    (∀ a : Fin s, ∀ i : Fin (s + 2), obsLane P.p (T.w a) (o.EF i) % P.p ^ 2 = P.p * T.z a i % P.p ^ 2) ∧
    (∀ n < (P.p ^ 2 - 1) / 24 + 1, lane o.pr.phi (P.p * n) % P.p =
      combLane (fun j _ => T.seed j) o.F 0 n % P.p) ∧
    (∀ a : Fin s, obsLane P.p (T.w a) o.pr.phi % P.p ^ 2 = P.p * T.zL2 a % P.p ^ 2) := by
  simp only [check, List.all_eq_true, List.mem_finRange, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, forall_const, true_implies] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Run

/-! ### Forms, combinations and coefficient bridges -/

section Tables
variable {s : ℕ} (p : ℕ)

def castM {m n : ℕ} (M : Fin m → Fin n → ℕ) : Fin m → Fin n → ZMod p := fun j i => (M j i : ZMod p)

def oddT (T : Table s) : ℕ → Fin (s + 2) → ZMod p
  | 0 => fun j => (T.seed j : ZMod p)
  | n + 1 => RankS.mv (castM p T.Dm) (RankS.mv (castM p T.Um) (oddT T n))

def linT (T : Table s) (k : Fin (s + 2)) (v : Fin (s + 2) → ZMod p) : ZMod p :=
  ∑ i, castM p T.B k i * v i

def detT (T : Table s) : ZMod p :=
  linT p T (RankS.iS s) (oddT p T 0) * linT p T (RankS.iT s) (oddT p T 1) -
    linT p T (RankS.iS s) (oddT p T 1) * linT p T (RankS.iT s) (oddT p T 0)

def initT (T : Table s) (X : Extra s) : Fin s → ZMod p := fun a =>
  ∑ i, RankS.mv (castM p T.Um) (oddT p T 1) i * (T.z a i : ZMod p) -
    (X.k₁ : ZMod p) * ∑ i, RankS.mv (castM p T.Um) (oddT p T 0) i * (T.z a i : ZMod p) -
      (X.k₀ : ZMod p) * (T.zL2 a : ZMod p)

/-- Everything checked in `ZMod p`. -/
structure Identities (T : Table s) (X : Extra s) : Prop where
  BBinv : ∀ k j, ∑ i, castM p T.B k i * castM p X.Binv i j = if k = j then 1 else 0
  BinvB : ∀ i j, ∑ k, castM p X.Binv i k * castM p T.B k j = if i = j then 1 else 0
  kill : ∀ a i, ∑ j, (∑ k, ((T.w a k : ℕ) : ZMod p) * castM p T.B k j) * castM p T.Um j i =
    ∑ t, castM p X.lam a t * castM p T.B (Fin.castAdd 2 t) i
  theta : ∀ a i, ((T.z a i : ℕ) : ZMod p) =
    ∑ b, castM p X.θ a b * (∑ k, ((T.w b k : ℕ) : ZMod p) * castM p T.B k i) +
      ∑ j, castM p X.μ a j * castM p T.Dm j i
  thinv : ∀ a c, ∑ b, castM p X.θi a b * castM p X.θ b c = if a = c then 1 else 0
  cay : oddT p T 2 = (X.k₁ : ZMod p) • oddT p T 1 + (X.k₀ : ZMod p) • oddT p T 0
  k₀ : (X.k₀ : ZMod p) ≠ 0
  det : detT p T ≠ 0
  init : initT p T X ≠ 0

end Tables

section Generic
variable {p : ℕ} [Fact p.Prime]

lemma mod_eq_cast {a b : ℕ} (h : a % p = b % p) : (a : ZMod p) = (b : ZMod p) := by
  rw [← ZMod.natCast_mod a, h, ZMod.natCast_mod]

lemma map_map_sq (g : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZModPow (p := p) 2) (PowerSeries.map (Int.castRingHom ℤ_[p]) g) =
      rd p g := by
  ext n
  simp [coeff_map]

lemma exists_of_toZModPow (x : ℤ_[p]) (z : ℕ)
    (h : PadicInt.toZModPow 2 x = ((p * z : ℕ) : ZMod (p ^ 2))) :
    ∃ t : ℤ_[p], x = (p : ℤ_[p]) * ((z : ℤ_[p]) + p * t) := by
  have hk : x - ((p * z : ℕ) : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) 2) := by
    rw [RingHom.mem_ker, map_sub, h, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  refine ⟨t, ?_⟩
  push_cast at ht
  linear_combination -ht

/-- The polynomial `Pdisc^j X₀^a X₁^b` of a basis form. -/
noncomputable def Pm (hp5 : 5 ≤ p) (ex : ℕ × ℕ × ℕ) : Poly p :=
  DBound.Pdisc hp5 ^ ex.1 * MvPolynomial.X 0 ^ ex.2.1 * MvPolynomial.X 1 ^ ex.2.2

lemma ev_Pm (hp5 : 5 ≤ p) (ex : ℕ × ℕ × ℕ) :
    ModP.ev ℤ_[p] (Pm hp5 ex) = PowerSeries.map (Int.castRingHom ℤ_[p]) (fz ex) := by
  simp only [Pm, map_mul, map_pow, DBound.ev_Pdisc, ModP.ev_X0, ModP.ev_X1, fz]
  simp only [DBound.Dl, ModP.Dq, ModP.E4, ModP.E6, map_mul, map_pow]

end Generic

section Final
variable {s : ℕ} {P : Params s} {T : Table s} {X : Extra s} [hp : Fact P.p.Prime]

lemma form_fz (hs : Sizes P) (i : Fin (s + 2)) : IntForm ((P.p - 1 : ℕ) : ℤ) (fz (P.ex i)) := by
  have h := ((IntForm.disc.pow (P.ex i).1).mul (IntForm.E4.pow (P.ex i).2.1)).mul
    (IntForm.E6.pow (P.ex i).2.2)
  refine h.cast ?_
  rw [← hs.hw i]; push_cast; ring

lemma cusp_fz (hs : Sizes P) (i : Fin (s + 2)) : coeff 0 (fz (P.ex i)) = 0 := by
  rw [fz, mul_assoc]; exact coeff_zero_Dz_pow (hs.hj i) _

/-- `Σⱼ Mⱼᵢ fⱼ`. -/
noncomputable def bcomb (P : Params s) (M : Fin (s + 2) → Fin (s + 2) → ℕ) (i : Fin (s + 2)) :
    PowerSeries ℤ :=
  ∑ j, PowerSeries.C ((M j i : ℕ) : ℤ) * fz (P.ex j)

lemma form_bcomb (hs : Sizes P) (M : Fin (s + 2) → Fin (s + 2) → ℕ) (i : Fin (s + 2)) :
    IntForm ((P.p - 1 : ℕ) : ℤ) (bcomb P M i) :=
  RankS.intForm_sum _ _ fun j _ => (form_fz hs j).C_mul _

lemma psi_bcomb (M : Fin (s + 2) → Fin (s + 2) → ℕ) (i : Fin (s + 2)) :
    Ψ P.p (bcomb P M i) = ∑ j, C ((M j i : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j)) := by
  rw [bcomb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, PowerSeries.map_C]
  congr 2
  simp

lemma coeff_bcomb {o : Out s} (rF : ∀ i, Rep P.N 22 (o.F i) (rd P.p (fz (P.ex i))))
    (M : Fin (s + 2) → Fin (s + 2) → ℕ) (i : Fin (s + 2)) {n : ℕ} (hn : n < P.N) :
    coeff n (Ψ P.p (bcomb P M i)) = ((combLane M o.F i n : ℕ) : ZMod P.p) := by
  rw [psi_bcomb, map_sum, combLane, fsum_eq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_psi (rF _) hn]

/-- `obs(Y F) mod p²` from one packed product. -/
lemma obs_lane (hs : Sizes P) (w : Fin (s + 2) → ℕ) (F : PS P.p) {a : ℕ}
    (hrep : Rep P.N 22 a (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2) (Φl P.p * F))) :
    PadicInt.toZModPow 2 (RankS.obs (fun k => ((w k : ℕ) : ℤ)) (RankS.Yop F)) =
      ((obsLane P.p w a : ℕ) : ZMod (P.p ^ 2)) := by
  have hb : ∀ k : Fin (s + 2), P.p * (P.p * (k.val + 1)) < P.N := fun k => by
    have := hs.hN3
    have hk := k.isLt
    calc P.p * (P.p * (k.val + 1)) = P.p ^ 2 * (k.val + 1) := by ring
      _ ≤ P.p ^ 2 * (s + 2) := Nat.mul_le_mul_left _ (by omega)
      _ < P.N := by linarith
  have hc : ∀ k : Fin (s + 2), PadicInt.toZModPow 2 (coeff (k.val + 1) (RankS.Yop F)) =
      ((lane a (P.p ^ 2 * (k.val + 1)) : ℕ) : ZMod (P.p ^ 2)) := fun k => by
    change PadicInt.toZModPow 2 (coeff (k.val + 1) (BoylanWebb.U P.p (BoylanWebb.U P.p (Φl P.p * F)))) = _
    rw [coeff_U, coeff_U, ← coeff_map, ← hrep.coeff _ (hb k), show P.p * (P.p * (k.val + 1)) =
      P.p ^ 2 * (k.val + 1) by ring]
  rw [RankS.obs_apply, map_sum, obsLane, fsum_eq, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_intCast, hc k]
  push_cast; ring

lemma iso_Pm (hs : Sizes P) (hp5 : 5 ≤ P.p) (i : Fin (s + 2)) :
    ModP.Iso (Pm hp5 (P.ex i)) (P.p - 1) := by
  have i0 : ModP.Iso (MvPolynomial.X 0 : Poly P.p) 4 := by
    simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[P.p] ModP.wt (0 : Fin 2)
  have i1 : ModP.Iso (MvPolynomial.X 1 : Poly P.p) 6 := by
    simpa [ModP.wt] using MvPolynomial.isWeightedHomogeneous_X ℤ_[P.p] ModP.wt (1 : Fin 2)
  refine ModP.iso_of_eq ((((DBound.iso_Pdisc hp5).pow (P.ex i).1).mul (i0.pow (P.ex i).2.1)).mul
    (i1.pow (P.ex i).2.2)) ?_
  rw [← hs.hw i]; ring

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
  have hp2 : P.p ≤ P.p ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlt3 : ∀ n, n ≤ (P.p - 1) / 12 → P.p * n < P.N := fun n hn => by
    have : P.p * n ≤ P.p * ((P.p ^ 2 - 1) / 24 + (P.p - 1) / 12) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- `B`
  have hB : ∀ (k i : Fin (s + 2)), coeff (k.val + 1) (Ψ P.p (fz (P.ex i))) = castM P.p T.B k i := by
    intro k i
    have hk : k.val + 1 < P.N := by
      have := k.isLt
      have : (s + 2) * 1 ≤ (s + 2) * P.p ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      omega
    rw [coeff_psi (rF i) hk, castM, ← ZMod.natCast_mod, cB i k]
  -- `U`
  have hU : ∀ i, U P.p (Ψ P.p (fz (P.ex i))) =
      ∑ j, C (castM P.p T.Um j i) * Ψ P.p (fz (P.ex j)) := by
    intro i
    rw [show (∑ j, C (castM P.p T.Um j i) * Ψ P.p (fz (P.ex j))) = Ψ P.p (bcomb P T.Um i) from
      (psi_bcomb T.Um i).symm]
    have he : P.p - 2 + 1 = P.p - 1 := by omega
    refine U_eq_of_coeffs P.p hp5 (P.p - 2) (by omega) ((P.p - 1 : ℕ) : ℤ) 0 (by rw [he]; simp) _ _
      ((form_fz hs i).cast (by rw [he])) (cusp_fz hs i) (form_bcomb hs _ i) fun n hn => ?_
    have hn3 : n ≤ (P.p - 1) / 12 := by rw [he] at hn; exact hn
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
    have hn' : n ≤ BoylanWebb.δ P.p + (P.p - 1) / 12 := by
      rw [he] at hn
      have : (12 * BoylanWebb.δ P.p + (P.p - 1)) / 12 = BoylanWebb.δ P.p + (P.p - 1) / 12 := by omega
      omega
    have hpn : P.p * n < P.N := by
      have : P.p * n ≤ P.p * (BoylanWebb.δ P.p + (P.p - 1) / 12) := Nat.mul_le_mul_left _ hn'
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
      have : P.p * n ≤ P.p * (BoylanWebb.δ P.p + (P.p - 1) / 12) := Nat.mul_le_mul_left _ (by omega)
      rw [hδ] at this; omega
    rw [← Ψ_Φ P.p h24, coeff_psi rphi hpn, coeff_bcomb rF _ 0 (by nlinarith)]
    exact mod_eq_cast (cS n (by rw [← hδ]; omega))
  -- `z`
  have hz : ∀ a i, ∃ t : ℤ_[P.p], RankS.obs (fun k => ((T.w a k : ℕ) : ℤ))
      (RankS.Yop (PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) * Einv P.p hp5)) =
      (P.p : ℤ_[P.p]) * ((((T.z a i : ℕ) : ℤ) : ℤ_[P.p]) + P.p * t) := by
    intro a i
    have hrep : Rep P.N 22 (o.EF i) (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
        (Φl P.p * (PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) * Einv P.p hp5))) := by
      rw [map_mul, map_mul, Φl, map_map_sq, map_map_sq, alg3]
      exact rEF i
    have h1 := obs_lane hs (T.w a) _ hrep
    rw [← ZMod.natCast_mod, cZ a i, ZMod.natCast_mod] at h1
    obtain ⟨t, ht⟩ := exists_of_toZModPow _ _ h1
    exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hL2 : ∀ a, ∃ t : ℤ_[P.p], RankS.obs (fun k => ((T.w a k : ℕ) : ℤ)) (Ll P.p 2) =
      (P.p : ℤ_[P.p]) * ((((T.zL2 a : ℕ) : ℤ) : ℤ_[P.p]) + P.p * t) := by
    intro a
    have hY : Ll P.p 2 = RankS.Yop 1 := by
      rw [show 2 = 2 * 0 + 2 from rfl, RankS.even_U, RankS.odd_D]
      change Ulin P.p (Dlin P.p (Ll P.p 0)) = RankS.Yop 1
      simp [Ll, BoylanWebb.L, RankS.Yop]
    have hrep : Rep P.N 22 o.pr.phi (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
        (Φl P.p * 1)) := by
      rw [mul_one, Φl, map_map_sq]; exact rphi
    have h1 := obs_lane hs (T.w a) _ hrep
    rw [← ZMod.natCast_mod, cL a, ZMod.natCast_mod] at h1
    obtain ⟨t, ht⟩ := exists_of_toZModPow _ _ h1
    exact ⟨t, by rw [hY, ht]; push_cast; ring⟩
  -- assemble
  let D0 : RankS.Data P.p s := ⟨fun i => fz (P.ex i), form_fz hs, cusp_fz hs, hs.hsturm, hp5,
    castM P.p T.B, hB, castM P.p X.Binv, hid.BBinv, castM P.p T.Um, hU, castM P.p T.Dm, hD,
    fun j => (T.seed j : ZMod P.p), hS⟩
  let D : RankS.Data2 P.p s := ⟨D0, hs.hlow, fun i => Pm hp5 (P.ex i), iso_Pm hs hp5,
    (fun i => ev_Pm hp5 (P.ex i)), hid.BinvB, fun a k => ((T.w a k : ℕ) : ℤ), castM P.p X.lam, by simpa using hid.kill,
    fun a i => ((T.z a i : ℕ) : ℤ), hz, castM P.p X.θ, castM P.p X.μ, by simpa using hid.theta⟩
  have hodd : ∀ n, D.odd n = oddT P.p T n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change RankS.mv _ (RankS.mv _ (D.odd n)) = _; rw [ih]; rfl
  have hcay : D.odd 2 = (X.k₁ : ZMod P.p) • D.odd 1 + (X.k₀ : ZMod P.p) • D.odd 0 := by
    rw [hodd, hodd, hodd]; exact hid.cay
  have hdet : D.det 0 ≠ 0 := by
    have : D.det 0 = detT P.p T := by
      simp only [RankS.Data.det, hodd]; rfl
    rw [this]; exact hid.det
  have hinit : D.init (X.k₀ : ZMod P.p) (X.k₁ : ZMod P.p) (fun a => ((T.zL2 a : ℕ) : ℤ)) ≠ 0 := by
    have : D.init (X.k₀ : ZMod P.p) (X.k₁ : ZMod P.p) (fun a => ((T.zL2 a : ℕ) : ℤ)) =
        initT P.p T X := by
      have hzc : ∀ a x, ((D.z a x : ℤ) : ZMod P.p) = (T.z a x : ZMod P.p) :=
        fun a x => Int.cast_natCast _
      funext a
      simp only [RankS.Data2.init, initT, hodd, hzc, Int.cast_natCast]; rfl
    rw [this]; exact hid.init
  exact D.bEll_eq hs.h29 h24 hcay hid.k₀ hdet _ hL2 (castM P.p X.θi) hid.thinv hinit m hm

end Final

end RamanujanTau.FiniteArithmetic.RankSPacked
