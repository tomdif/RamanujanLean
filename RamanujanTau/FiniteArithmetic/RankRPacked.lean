import RamanujanTau.FiniteArithmetic.RankRMain
import RamanujanTau.FiniteArithmetic.RankSPacked

/-!
# `b_p(m) = 2m − 1` from one packed kernel computation, order-`r` recurrence

The `RankSPacked` pipeline for `RankR`: `s + r` basis forms, an odd recurrence of order `r`, and
`s` observations. `bEll_of_ok` turns one successful `decide +kernel` check and identities in
`ZMod p` into `b_p(m) = 2m − 1` for every `m ≥ 1` (`RankR.Data2.bEll_eq`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankRPacked

open PowerSeries Packed PackedPrime BoylanWebb AtkinOBrien AtkinOBrienFinal
open Rank2Packed (powP mono fz U_eq_of_coeffs powP_rep mono_rep coeff_psi alg3)
open MockTheta5.JTP (qfacInf partitionGF)
open RankSPacked (fsum fsum_eq optAll optAll_spec mod_eq_cast map_map_sq exists_of_toZModPow Pm ev_Pm)

/-! ### The program -/

structure Params (s r : ℕ) where
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
  ex : Fin (s + r) → ℕ × ℕ × ℕ

structure Out (s r : ℕ) where
  pr : Prelude
  F : Fin (s + r) → ℕ
  PF : Fin (s + r) → ℕ
  EF : Fin (s + r) → ℕ

/-- `(f, Φ f, E⁻¹ Φ f)` for one basis form. -/
def formLanes {s r : ℕ} (P : Params s r) (pr : Prelude) (ex : ℕ × ℕ × ℕ) : Option (ℕ × ℕ × ℕ) := do
  let F ← mono P.p P.N pr ex
  let G ← mulP P.p P.N pr.phi F
  let H ← mulP P.p P.N pr.einv G
  return (F, G, H)

def run {s r : ℕ} (P : Params s r) : Option (Out s r) := do
  let pr ← prelude P.lv P.p P.N P.c P.R P.d P.k P.n P.ku P.kb P.kc
  let L ← optAll (s + r) (fun i => formLanes P pr (P.ex i))
  return ⟨pr, fun i => (L i).1, fun i => (L i).2.1, fun i => (L i).2.2⟩

/-- The proposed data. -/
structure Table (s r : ℕ) where
  B : Fin (s + r) → Fin (s + r) → ℕ
  Um : Fin (s + r) → Fin (s + r) → ℕ
  Dm : Fin (s + r) → Fin (s + r) → ℕ
  seed : Fin (s + r) → ℕ
  w : Fin s → Fin (s + r) → ℕ
  z : Fin s → Fin (s + r) → ℕ
  zL2 : Fin s → ℕ

/-- `Σⱼ Mⱼᵢ · lane(Fⱼ, n)`. -/
def combLane {s r : ℕ} (M : Fin (s + r) → Fin (s + r) → ℕ) (F : Fin (s + r) → ℕ) (i : Fin (s + r))
    (n : ℕ) : ℕ :=
  fsum (s + r) fun j => M j i * lane (F j) n

def obsLane {s r : ℕ} (p : ℕ) (w : Fin (s + r) → ℕ) (a : ℕ) : ℕ :=
  fsum (s + r) fun k => w k * lane a (p ^ 2 * (k.val + 1))

/-- All lane comparisons. -/
def check {s r : ℕ} (P : Params s r) (T : Table s r) (o : Out s r) : Bool :=
  let p := P.p
  let δ := (p ^ 2 - 1) / 24
  let t := (p - 1) / 12
  ((List.finRange (s + r)).all fun i => (List.finRange (s + r)).all fun k =>
    lane (o.F i) (k.val + 1) % p == T.B k i) &&
  ((List.finRange (s + r)).all fun i => (List.range (t + 1)).all fun n =>
    lane (o.F i) (p * n) % p == combLane T.Um o.F i n % p) &&
  ((List.finRange (s + r)).all fun i => (List.range (δ + t + 1)).all fun n =>
    lane (o.PF i) (p * n) % p == combLane T.Dm o.F i n % p) &&
  ((List.finRange s).all fun a => (List.finRange (s + r)).all fun i =>
    obsLane p (T.w a) (o.EF i) % p ^ 2 == p * T.z a i % p ^ 2) &&
  ((List.range (δ + 1)).all fun n =>
    lane o.pr.phi (p * n) % p == fsum (s + r) (fun j => T.seed j * lane (o.F j) n) % p) &&
  ((List.finRange s).all fun a => obsLane p (T.w a) o.pr.phi % p ^ 2 == p * T.zL2 a % p ^ 2)

/-- The kernel-evaluated statement. -/
def ok {s r : ℕ} (P : Params s r) (T : Table s r) : Bool :=
  match run P with
  | some o => check P T o
  | none => false

/-! ### Unrolling the program -/

/-- The identities in `ZMod p`, proposed with the tables. -/
structure Extra (s r : ℕ) where
  Binv : Fin (s + r) → Fin (s + r) → ℕ
  lam : Fin s → Fin s → ℕ
  θ : Fin s → Fin s → ℕ
  θi : Fin s → Fin s → ℕ
  μ : Fin s → Fin (s + r) → ℕ
  k : Fin r → ℕ

/-- The size and parameter conditions, all decidable. -/
structure Sizes {s r : ℕ} (P : Params s r) : Prop where
  h29 : 29 ≤ P.p
  hr : 0 < r
  hsturm : (P.p - 1) / 12 + 1 ≤ s + r + 1
  hlow : P.p * s < (P.p ^ 2 - 1) / 24
  h24 : 24 * ((P.p ^ 2 - 1) / 24) + 1 = P.p ^ 2
  hQ : P.p ^ 2 ≤ 2 ^ 21
  hN0 : 0 < P.N
  hlv : P.lv < 20
  hN : P.N ≤ 2 ^ P.lv
  hN5 : P.N ≤ 12 * P.p ^ 2
  hp3 : P.N < P.p ^ 3
  hN3 : (s + r) * P.p ^ 2 < P.N
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
variable {s r : ℕ} {P : Params s r} [hp : Fact P.p.Prime]

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

theorem run_spec (hs : Sizes P) {o : Out s r} (h : run P = some o) :
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
theorem check_spec {T : Table s r} {o : Out s r} (h : check P T o = true) :
    (∀ i k : Fin (s + r), lane (o.F i) (k.val + 1) % P.p = T.B k i) ∧
    (∀ i : Fin (s + r), ∀ n < (P.p - 1) / 12 + 1,
      lane (o.F i) (P.p * n) % P.p = combLane T.Um o.F i n % P.p) ∧
    (∀ i : Fin (s + r), ∀ n < (P.p ^ 2 - 1) / 24 + (P.p - 1) / 12 + 1,
      lane (o.PF i) (P.p * n) % P.p = combLane T.Dm o.F i n % P.p) ∧
    (∀ a : Fin s, ∀ i : Fin (s + r), obsLane P.p (T.w a) (o.EF i) % P.p ^ 2 = P.p * T.z a i % P.p ^ 2) ∧
    (∀ n < (P.p ^ 2 - 1) / 24 + 1, lane o.pr.phi (P.p * n) % P.p =
      fsum (s + r) (fun j => T.seed j * lane (o.F j) n) % P.p) ∧
    (∀ a : Fin s, obsLane P.p (T.w a) o.pr.phi % P.p ^ 2 = P.p * T.zL2 a % P.p ^ 2) := by
  simp only [check, List.all_eq_true, List.mem_finRange, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, forall_const, true_implies] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Run

/-! ### Forms, combinations and coefficient bridges -/

section Tables
variable {s r : ℕ} (p : ℕ)

def castM {m n : ℕ} (M : Fin m → Fin n → ℕ) : Fin m → Fin n → ZMod p := fun j i => (M j i : ZMod p)

def oddT (T : Table s r) : ℕ → Fin (s + r) → ZMod p
  | 0 => fun j => (T.seed j : ZMod p)
  | n + 1 => RankR.mv (castM p T.Dm) (RankR.mv (castM p T.Um) (oddT T n))

def linT (T : Table s r) (k : Fin (s + r)) (v : Fin (s + r) → ZMod p) : ZMod p :=
  ∑ i, castM p T.B k i * v i

def detT (T : Table s r) : ZMod p :=
  Matrix.det (fun i j : Fin r => linT p T (RankR.high s i) (oddT p T j.val))

def kT (X : Extra s r) : Fin r → ZMod p := fun j => (X.k j : ZMod p)

def zevT (T : Table s r) : ℕ → Fin s → ZMod p
  | 0 => fun a => (T.zL2 a : ZMod p)
  | j + 1 => fun a => ∑ i, RankR.mv (castM p T.Um) (oddT p T j) i * (T.z a i : ZMod p)

def initT (T : Table s r) (X : Extra s r) : Fin s → ZMod p := fun a =>
  zevT p T r a - ∑ j : Fin r, kT p X j * zevT p T j.val a

/-- Everything checked in `ZMod p`. -/
structure Identities (T : Table s r) (X : Extra s r) : Prop where
  BBinv : ∀ k j, ∑ i, castM p T.B k i * castM p X.Binv i j = if k = j then 1 else 0
  BinvB : ∀ i j, ∑ k, castM p X.Binv i k * castM p T.B k j = if i = j then 1 else 0
  kill : ∀ a i, ∑ j, (∑ k, ((T.w a k : ℕ) : ZMod p) * castM p T.B k j) * castM p T.Um j i =
    ∑ t, castM p X.lam a t * castM p T.B (Fin.castAdd r t) i
  theta : ∀ a i, ((T.z a i : ℕ) : ZMod p) =
    ∑ b, castM p X.θ a b * (∑ k, ((T.w b k : ℕ) : ZMod p) * castM p T.B k i) +
      ∑ j, castM p X.μ a j * castM p T.Dm j i
  thinv : ∀ a c, ∑ b, castM p X.θi a b * castM p X.θ b c = if a = c then 1 else 0
  cay : oddT p T r = ∑ j : Fin r, kT p X j • oddT p T j.val
  comp : (RankR.comp (kT p X)).det ≠ 0
  det : detT p T ≠ 0
  init : initT p T X ≠ 0

end Tables


section Final
variable {s r : ℕ} {P : Params s r} {T : Table s r} {X : Extra s r} [hp : Fact P.p.Prime]

lemma form_fz (hs : Sizes P) (i : Fin (s + r)) : IntForm ((P.p - 1 : ℕ) : ℤ) (fz (P.ex i)) := by
  have h := ((IntForm.disc.pow (P.ex i).1).mul (IntForm.E4.pow (P.ex i).2.1)).mul
    (IntForm.E6.pow (P.ex i).2.2)
  refine h.cast ?_
  rw [← hs.hw i]; push_cast; ring

lemma cusp_fz (hs : Sizes P) (i : Fin (s + r)) : coeff 0 (fz (P.ex i)) = 0 := by
  rw [fz, mul_assoc]; exact coeff_zero_Dz_pow (hs.hj i) _

/-- `Σⱼ Mⱼᵢ fⱼ`. -/
noncomputable def bcomb (P : Params s r) (M : Fin (s + r) → Fin (s + r) → ℕ) (i : Fin (s + r)) :
    PowerSeries ℤ :=
  ∑ j, PowerSeries.C ((M j i : ℕ) : ℤ) * fz (P.ex j)

lemma form_bcomb (hs : Sizes P) (M : Fin (s + r) → Fin (s + r) → ℕ) (i : Fin (s + r)) :
    IntForm ((P.p - 1 : ℕ) : ℤ) (bcomb P M i) :=
  RankR.intForm_sum _ _ fun j _ => (form_fz hs j).C_mul _

lemma psi_bcomb (M : Fin (s + r) → Fin (s + r) → ℕ) (i : Fin (s + r)) :
    Ψ P.p (bcomb P M i) = ∑ j, C ((M j i : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j)) := by
  rw [bcomb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, PowerSeries.map_C]
  congr 2
  simp

lemma coeff_bcomb {o : Out s r} (rF : ∀ i, Rep P.N 22 (o.F i) (rd P.p (fz (P.ex i))))
    (M : Fin (s + r) → Fin (s + r) → ℕ) (i : Fin (s + r)) {n : ℕ} (hn : n < P.N) :
    coeff n (Ψ P.p (bcomb P M i)) = ((combLane M o.F i n : ℕ) : ZMod P.p) := by
  rw [psi_bcomb, map_sum, combLane, fsum_eq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_psi (rF _) hn]

/-- `obs(Y F) mod p²` from one packed product. -/
lemma obs_lane (hs : Sizes P) (w : Fin (s + r) → ℕ) (F : PS P.p) {a : ℕ}
    (hrep : Rep P.N 22 a (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2) (Φl P.p * F))) :
    PadicInt.toZModPow 2 (RankR.obs (fun k => ((w k : ℕ) : ℤ)) (RankR.Yop F)) =
      ((obsLane P.p w a : ℕ) : ZMod (P.p ^ 2)) := by
  have hb : ∀ k : Fin (s + r), P.p * (P.p * (k.val + 1)) < P.N := fun k => by
    have := hs.hN3
    have hk := k.isLt
    calc P.p * (P.p * (k.val + 1)) = P.p ^ 2 * (k.val + 1) := by ring
      _ ≤ P.p ^ 2 * (s + r) := Nat.mul_le_mul_left _ (by omega)
      _ < P.N := by linarith
  have hc : ∀ k : Fin (s + r), PadicInt.toZModPow 2 (coeff (k.val + 1) (RankR.Yop F)) =
      ((lane a (P.p ^ 2 * (k.val + 1)) : ℕ) : ZMod (P.p ^ 2)) := fun k => by
    change PadicInt.toZModPow 2 (coeff (k.val + 1) (BoylanWebb.U P.p (BoylanWebb.U P.p (Φl P.p * F)))) = _
    rw [coeff_U, coeff_U, ← coeff_map, ← hrep.coeff _ (hb k), show P.p * (P.p * (k.val + 1)) =
      P.p ^ 2 * (k.val + 1) by ring]
  rw [RankR.obs_apply, map_sum, obsLane, fsum_eq, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_intCast, hc k]
  push_cast; ring

lemma iso_Pm (hs : Sizes P) (hp5 : 5 ≤ P.p) (i : Fin (s + r)) :
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
  have hB : ∀ (k i : Fin (s + r)), coeff (k.val + 1) (Ψ P.p (fz (P.ex i))) = castM P.p T.B k i := by
    intro k i
    have hk : k.val + 1 < P.N := by
      have := k.isLt
      have : (s + r) * 1 ≤ (s + r) * P.p ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
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
  have i0 : Fin (s + r) := ⟨0, by have := hs.hr; omega⟩
  have hS : U P.p (Ψ P.p (Dz ^ BoylanWebb.δ P.p)) =
      ∑ j, C ((T.seed j : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j)) := by
    rw [show (∑ j, C ((T.seed j : ℕ) : ZMod P.p) * Ψ P.p (fz (P.ex j))) =
      Ψ P.p (bcomb P (fun j _ => T.seed j) i0) from (psi_bcomb (fun j _ => T.seed j) i0).symm]
    set e := 12 * BoylanWebb.δ P.p - 1
    have he : e + 1 = 12 * BoylanWebb.δ P.p := by omega
    have hw : (((P.p - 1 : ℕ) : ℤ) + (((P.p - 1) / 2 : ℕ) : ℤ) * ((P.p - 1 : ℕ) : ℤ)) =
        ((e + 1 : ℕ) : ℤ) := by
      rw [he]; exact_mod_cast (by rw [hδ]; exact hs.hmS)
    refine U_eq_of_coeffs P.p hp5 e (by omega) ((P.p - 1 : ℕ) : ℤ) ((P.p - 1) / 2) hw _ _
      ((IntForm.disc.pow (BoylanWebb.δ P.p)).cast (by rw [he]; push_cast; ring))
      (by simpa using coeff_zero_Dz_pow hδ1 1) (form_bcomb hs _ i0) fun n hn => ?_
    have hn' : n ≤ BoylanWebb.δ P.p := by rw [he] at hn; omega
    have hpn : P.p * n < P.N := by
      have : P.p * n ≤ P.p * (BoylanWebb.δ P.p + (P.p - 1) / 12) := Nat.mul_le_mul_left _ (by omega)
      rw [hδ] at this; omega
    rw [← Ψ_Φ P.p h24, coeff_psi rphi hpn, coeff_bcomb rF _ i0 (by nlinarith)]
    exact mod_eq_cast (cS n (by rw [← hδ]; omega))
  -- `z`
  have hz : ∀ a i, ∃ t : ℤ_[P.p], RankR.obs (fun k => ((T.w a k : ℕ) : ℤ))
      (RankR.Yop (PowerSeries.map (Int.castRingHom ℤ_[P.p]) (fz (P.ex i)) * Einv P.p hp5)) =
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
  have hL2 : ∀ a, ∃ t : ℤ_[P.p], RankR.obs (fun k => ((T.w a k : ℕ) : ℤ)) (Ll P.p 2) =
      (P.p : ℤ_[P.p]) * ((((T.zL2 a : ℕ) : ℤ) : ℤ_[P.p]) + P.p * t) := by
    intro a
    have hY : Ll P.p 2 = RankR.Yop 1 := by
      rw [show 2 = 2 * 0 + 2 from rfl, RankS.even_U, RankS.odd_D]
      change Ulin P.p (Dlin P.p (Ll P.p 0)) = RankR.Yop 1
      simp [Ll, BoylanWebb.L, RankR.Yop]
    have hrep : Rep P.N 22 o.pr.phi (PowerSeries.map (PadicInt.toZModPow (p := P.p) 2)
        (Φl P.p * 1)) := by
      rw [mul_one, Φl, map_map_sq]; exact rphi
    have h1 := obs_lane hs (T.w a) _ hrep
    rw [← ZMod.natCast_mod, cL a, ZMod.natCast_mod] at h1
    obtain ⟨t, ht⟩ := exists_of_toZModPow _ _ h1
    exact ⟨t, by rw [hY, ht]; push_cast; ring⟩
  -- assemble
  let D0 : RankR.Data P.p s r := ⟨fun i => fz (P.ex i), form_fz hs, cusp_fz hs, hs.hsturm, hp5,
    castM P.p T.B, hB, castM P.p X.Binv, hid.BBinv, castM P.p T.Um, hU, castM P.p T.Dm, hD,
    fun j => (T.seed j : ZMod P.p), hS⟩
  let D : RankR.Data2 P.p s r := ⟨D0, hs.hlow, fun i => Pm hp5 (P.ex i), iso_Pm hs hp5,
    (fun i => ev_Pm hp5 (P.ex i)), hid.BinvB, fun a k => ((T.w a k : ℕ) : ℤ), castM P.p X.lam,
    by simpa using hid.kill, fun a i => ((T.z a i : ℕ) : ℤ), hz, castM P.p X.θ, castM P.p X.μ,
    by simpa using hid.theta⟩
  have hodd : ∀ n, D.odd n = oddT P.p T n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change RankR.mv _ (RankR.mv _ (D.odd n)) = _; rw [ih]; rfl
  have hcay : D.odd r = ∑ j : Fin r, kT P.p X j • D.odd j.val := by
    simp only [hodd]; exact hid.cay
  have hdet : D.det 0 ≠ 0 := by
    have : D.det 0 = detT P.p T := by
      unfold RankR.Data.det detT
      congr 1
      ext i j
      simp only [RankR.Data.oddM, zero_add]
      rw [hodd]
      rfl
    rw [this]; exact hid.det
  have hzc : ∀ a x, ((D.z a x : ℤ) : ZMod P.p) = (T.z a x : ZMod P.p) :=
    fun a x => Int.cast_natCast _
  have hzev : ∀ j, D.zev (fun a => ((T.zL2 a : ℕ) : ℤ)) j = zevT P.p T j := by
    intro j
    cases j with
    | zero => funext a; simp [RankR.Data2.zev, zevT]
    | succ j => funext a; simp only [RankR.Data2.zev, zevT, hodd, hzc]; rfl
  have hinit : D.init (kT P.p X) (fun a => ((T.zL2 a : ℕ) : ℤ)) ≠ 0 := by
    have : D.init (kT P.p X) (fun a => ((T.zL2 a : ℕ) : ℤ)) = initT P.p T X := by
      funext a
      simp only [RankR.Data2.init, initT, hzev]
    rw [this]; exact hid.init
  exact D.bEll_eq hs.h29 h24 hs.hr hcay hid.comp hdet _ hL2 (castM P.p X.θi) hid.thinv hinit m hm

end Final

end RamanujanTau.FiniteArithmetic.RankRPacked
