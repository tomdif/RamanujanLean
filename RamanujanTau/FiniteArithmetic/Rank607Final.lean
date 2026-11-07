import RamanujanTau.FiniteArithmetic.Rank607Series
import RamanujanTau.FiniteArithmetic.Rank607Check
import RamanujanTau.FiniteArithmetic.Rank607Witness
import RamanujanTau.FiniteArithmetic.EnvelopePrecision

/-! # The generator rank at 607

The saved 25-by-25 minor consists of actual partition data, so
`rEll 607 m = 25` for every `m ≥ 2`.

The induction identifies each `L(b)`, `1 ≤ b ≤ 53`, modulo `607²` with an explicit
combination of the basis `E₄^(3(101-t)) Δ^t E⁻²`, using the exact reconstruction
theorem `partition_two_eq_of_coeff_prefix`. All coefficient data comes from one
kernel evaluation of `finalCheck`. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace RamanujanTau.FiniteArithmetic.Rank607Final

open PowerSeries Packed Rank607Program Rank607Series Rank607Identities
open BoylanWebb (L T U coeff_U map_U)

/-- The whole finite computation, evaluated once. -/
theorem final_ok : finalCheck = true := by decide +kernel

lemma pure_some {α : Type} {a b : α} (h : (pure a : Option α) = some b) : a = b :=
  Option.some.inj h

/-- Unrolling `rows` without evaluating it. -/
lemma rows_unroll {rs : Rows} {phiRow : ℕ} (h : rows = some (rs, phiRow)) :
    ∃ pr, prelude = some pr ∧ basisRows pr.g (shiftR N delta pr.pgf) 102 pr.b0 = some rs ∧
      rowOf (shiftR N delta pr.pgf) = phiRow := by
  unfold rows at h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨rs', hrs, h⟩ := bind_some h
  have hinj : (rs', rowOf (shiftR N delta pr.pgf)) = (rs, phiRow) := pure_some h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj
  exact ⟨pr, hpr, hrs, rfl⟩

lemma baseOk_unroll {rs : Rows} {phiRow : ℕ} (h : baseOk rs phiRow = true) :
    ∃ B, comboL (coordAt 1) rs.ls = some B ∧ canon phiRow = canon B := by
  unfold baseOk at h
  cases hB : comboL (coordAt 1) rs.ls with
  | none => rw [hB] at h; exact absurd h (by simp)
  | some B =>
    rw [hB] at h
    exact ⟨B, rfl, by simpa using h⟩

lemma stepOk_unroll {rs : Rows} {b : ℕ} (h : stepOk rs b = true) :
    ∃ A B, comboL (coordAt b) (if b % 2 = 1 then rs.us else rs.ds) = some A ∧
      comboL (coordAt (b + 1)) rs.ls = some B ∧ canon A = canon B := by
  unfold stepOk at h
  cases hA : comboL (coordAt b) (if b % 2 = 1 then rs.us else rs.ds) with
  | none => rw [hA] at h; exact absurd h (by simp)
  | some A =>
    cases hB : comboL (coordAt (b + 1)) rs.ls with
    | none => rw [hA, hB] at h; exact absurd h (by simp)
    | some B =>
      rw [hA, hB] at h
      exact ⟨A, B, rfl, rfl, by simpa using h⟩

lemma columnOk_unroll {rs : Rows} {j : ℕ} (h : columnOk rs j = true) :
    ∃ B, comboL (coordAt (2 * j + 3)) rs.ls = some B ∧
      ∀ i < 25, lane (canon B) (i + 26) = entryAt i j := by
  unfold columnOk at h
  cases hB : comboL (coordAt (2 * j + 3)) rs.ls with
  | none => rw [hB] at h; exact absurd h (by simp)
  | some B =>
    rw [hB] at h
    refine ⟨B, rfl, fun i hi => ?_⟩
    have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
    simpa using this

/-- The pieces of the final check, without evaluating anything. -/
lemma final_unroll : ∃ rs phiRow, rows = some (rs, phiRow) ∧
    (∀ b < 54, (coordAt b).length ≤ 102) ∧ baseOk rs phiRow = true ∧
    (∀ b < 52, stepOk rs (b + 1) = true) ∧ (∀ j < 25, columnOk rs j = true) := by
  have h := final_ok
  unfold finalCheck at h
  cases hr : rows with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some rp =>
    obtain ⟨rs, phiRow⟩ := rp
    rw [hr] at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨rs, phiRow, rfl, h1, h2, h3, h4⟩

attribute [local irreducible] rows prelude coordTable matrixTable coordAt entryAt comboL
  finalCheck stepOk baseOk columnOk

/-! ### Reading rows -/

variable {f : PowerSeries R}

lemma rep_zero : Rep 102 22 0 (0 : PowerSeries R) := by
  refine ⟨⟨by norm_num, fun i => ?_⟩, fun i _ => ?_⟩
  · simp [lane]
  · simp [lane]

lemma Rep_lane_bound {M k a i : ℕ} (hlt : a < x ^ M) (hi : ¬ i < M) : lane a i < 2 ^ k := by
  have hle : a < x ^ i := lt_of_lt_of_le hlt (Nat.pow_le_pow_right x_pos (by omega))
  rw [lane, Nat.div_eq_of_lt hle, Nat.zero_mod]
  positivity

/-- A long prefix restricts to a short one. -/
lemma rep_low {k a : ℕ} (ha : Rep N k a f) : Rep 102 k (a % x ^ 102) f := by
  have hlt : a % x ^ 102 < x ^ 102 := Nat.mod_lt _ (pow_pos x_pos _)
  refine ⟨⟨hlt, fun i => ?_⟩, fun i hi => ?_⟩
  · by_cases hi : i < 102
    · rw [lane_mod _ _ _ hi]
      exact ha.lane_lt i
    · exact Rep_lane_bound hlt hi
  · rw [lane_mod _ _ _ hi]
    exact ha.coeff i (lt_trans hi (by norm_num))

/-- The specification of `sparse`. -/
theorem sparse_eq (s : ℕ) (hs : 0 < s) (l a : ℕ) :
    sparse s l a = pack (fun j => lane a (s * j)) (2 ^ l) := by
  induction l generalizing a with
  | zero => simp [sparse, pack, lane]
  | succ l ih =>
    have hsh : ∀ b : ℕ, b <<< (64 * 2 ^ l) = b * x ^ 2 ^ l := fun b => by
      rw [Nat.shiftLeft_eq, x, ← pow_mul]
    have e1 : pack (fun j => lane (a % x ^ (s * 2 ^ l)) (s * j)) (2 ^ l) =
        pack (fun j => lane a (s * j)) (2 ^ l) :=
      pack_congr fun j hj => lane_mod _ _ _ (Nat.mul_lt_mul_of_pos_left hj hs)
    have e2 : pack (fun j => lane (a >>> (64 * (s * 2 ^ l))) (s * j)) (2 ^ l) =
        pack (fun j => lane a (s * (2 ^ l + j))) (2 ^ l) :=
      pack_congr fun j _ => by rw [lane_shift, Nat.mul_add]
    rw [sparse, ih, ih, pow_succ, mul_two, pack_split, hsh, e1, e2]

lemma lane_rowOf (a j : ℕ) (hj : j < 102) : lane (rowOf a) j = lane a (607 * j) := by
  rw [rowOf, lane_mod _ _ _ hj, sparse_eq _ (by norm_num)]
  exact lane_pack (fun j => lane a (p * j)) (fun _ => lane_lt _ _) _ j
    (lt_trans hj (by norm_num))

/-- The row of a represented series is a prefix of its image under `U`. -/
lemma rep_rowOf {k a : ℕ} (ha : Rep N k a f) : Rep 102 k (rowOf a) (U 607 f) := by
  have hlt : rowOf a < x ^ 102 := Nat.mod_lt _ (pow_pos x_pos _)
  refine ⟨⟨hlt, fun i => ?_⟩, fun i hi => ?_⟩
  · by_cases hi : i < 102
    · rw [lane_rowOf _ _ hi]
      exact ha.lane_lt _
    · exact Rep_lane_bound hlt hi
  · rw [lane_rowOf _ _ hi, coeff_U]
    exact ha.coeff _ (by change 607 * i < 61308; omega)

lemma lane_canon (a i : ℕ) (hi : i < 102) : lane (canon a) i = lane a i % Q := by
  rw [canon, lane_mod _ _ _ hi, laneMap_eq]
  have hv : ∀ j, lane a j % Q < x := fun j =>
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  exact lane_pack (fun j => lane a j % Q) hv _ i (lt_trans hi (by norm_num))

lemma cast_lane_of_canon {a b : ℕ} (h : canon a = canon b) (i : ℕ) (hi : i < 102) :
    (lane a i : R) = (lane b i : R) := by
  have := congrArg (fun z => lane z i) h
  simp only [lane_canon _ _ hi] at this
  rw [← ZMod.natCast_mod (lane a i), ← ZMod.natCast_mod (lane b i), this]

/-! ### Combinations -/

/-- A list of rows representing consecutive series. -/
def RepList : List ℕ → (ℕ → PowerSeries R) → ℕ → Prop
  | [], _, _ => True
  | r :: rs, F, t => Rep 102 22 r (F t) ∧ RepList rs F (t + 1)

/-- The series represented by a combination. -/
noncomputable def comboS : List ℕ → (ℕ → PowerSeries R) → ℕ → PowerSeries R
  | [], _, _ => 0
  | d :: ds, F, t => PowerSeries.C (d : R) * F t + comboS ds F (t + 1)

theorem comboL_rep {ds rs : List ℕ} {F : ℕ → PowerSeries R} {t r : ℕ} (hr : RepList rs F t)
    (h : comboL ds rs = some r) : Rep 102 22 r (comboS ds F t) := by
  induction ds generalizing rs t r with
  | nil =>
    obtain rfl : 0 = r := by simpa [comboL] using h
    exact rep_zero
  | cons d ds ih =>
    cases rs with
    | nil => simp [comboL] at h
    | cons a as =>
      simp only [comboL] at h
      split_ifs at h with hd
      obtain ⟨u, hu, h⟩ := bind_some h
      obtain ⟨s, hs, h⟩ := bind_some h
      have hC : Rep 102 22 d (PowerSeries.C (d : R)) := rep_C (by norm_num) hd (by norm_num)
      have r1 : Rep 102 22 u (PowerSeries.C (d : R) * F t) :=
        Rep.mulR hQ hC hr.1 (by norm_num : 102 ≤ 2 ^ 7) (by norm_num) hu
      exact Rep.addR hQ r1 (ih hr.2 hs) h

lemma alg_phi_cons {S : Type*} [CommRing S] (ph c a b : S) :
    ph * (c * a + b) = c * (a * ph) + ph * b := by ring

lemma U_add_C {c : R} {a b : PowerSeries R} :
    U 607 (PowerSeries.C c * a + b) = PowerSeries.C c * U 607 a + U 607 b := by
  ext n
  simp [coeff_U, PowerSeries.coeff_C_mul]

lemma comboS_U (ds : List ℕ) (F : ℕ → PowerSeries R) (t : ℕ) :
    U 607 (comboS ds F t) = comboS ds (fun s => U 607 (F s)) t := by
  induction ds generalizing t with
  | nil =>
    ext n
    simp [comboS, coeff_U]
  | cons d ds ih => rw [comboS, comboS, U_add_C, ih]

lemma comboS_Uphi (ph : PowerSeries R) (ds : List ℕ) (F : ℕ → PowerSeries R) (t : ℕ) :
    U 607 (ph * comboS ds F t) = comboS ds (fun s => U 607 (F s * ph)) t := by
  induction ds generalizing t with
  | nil =>
    ext n
    simp [comboS, coeff_U]
  | cons d ds ih => rw [comboS, comboS, alg_phi_cons, U_add_C, ih]

/-! ### The basis rows -/

structure RowSpec (rs : Rows) (F : ℕ → PowerSeries R) (ph : PowerSeries R) (t : ℕ) : Prop where
  ls : RepList rs.ls F t
  us : RepList rs.us (fun s => U 607 (F s)) t
  ds : RepList rs.ds (fun s => U 607 (F s * ph)) t

theorem basisRows_spec {g phi : ℕ} {gs ph : PowerSeries R} (hg : Rep N 22 g gs)
    (hphi : Rep N 22 phi ph) {F : ℕ → PowerSeries R} (hF : ∀ t, F (t + 1) = F t * gs)
    (c : ℕ) {b t : ℕ} {rs : Rows} (hb : Rep N 22 b (F t)) (h : basisRows g phi c b = some rs) :
    RowSpec rs F ph t := by
  induction c generalizing b t rs with
  | zero =>
    obtain rfl : (⟨[], [], []⟩ : Rows) = rs := Option.some.inj h
    exact ⟨trivial, trivial, trivial⟩
  | succ c ih =>
    obtain ⟨next, h1, h⟩ := bind_some h
    obtain ⟨d, h2, h⟩ := bind_some h
    obtain ⟨rest, h3, h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    have hnext : Rep N 22 next (F (t + 1)) := by
      rw [hF]
      exact rmul hb hg h1
    have hR := ih hnext h3
    have hprod : Rep N 61 ((b * phi) % x ^ N) (F t * ph) := hb.mul hphi hN (by norm_num)
    have hd : Rep 102 22 d (U 607 (F t * ph)) := Rep.reduceR hQ (rep_rowOf hprod) h2
    exact ⟨⟨rep_low hb, hR.ls⟩, ⟨rep_rowOf hb, hR.us⟩, ⟨hd, hR.ds⟩⟩

/-! ### Numerators -/

lemma alg_basis {S : Type*} [CommRing S] (e d v s : S) (hv : e ^ 3 * v = 1) {t : ℕ}
    (ht : t ≤ 101) :
    (e ^ 3) ^ 101 * s * (d * v) ^ t = e ^ (3 * (101 - t)) * d ^ t * s := by
  have h1 : (e ^ 3) ^ 101 = e ^ (3 * (101 - t)) * (e ^ 3) ^ t := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have h2 : (e ^ 3) ^ t * v ^ t = 1 := by rw [← mul_pow, hv, one_pow]
  rw [h1, mul_pow]
  linear_combination (e ^ (3 * (101 - t)) * s * d ^ t) * h2

lemma alg_num {S : Type*} [CommRing S] (E c a b s rest : S) (hs : E * s = 1) :
    c * (a * b) + E * rest = E * (c * (a * b * s) + rest) := by
  linear_combination (-(c * (a * b))) * hs

lemma h1728 : IsUnit (1728 : R) := by
  have : ((1728 : ℕ) : R) = 1728 := by norm_num
  rw [← this, ZMod.isUnit_iff_coprime]
  norm_num

/-- The discriminant with its denominator removed. -/
noncomputable def DpPoly : MvPolynomial (Fin 2) R :=
  MvPolynomial.C ((1728 : R)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

lemma iso_Dp : ModP.Iso DpPoly 12 := by
  have h3 : ModP.Iso (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) R) 12 :=
    ModP.iso_of_eq (by simpa using ModP.iso_mono (R := R) 3 0) (by norm_num)
  have h2 : ModP.Iso (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) 12 :=
    ModP.iso_of_eq (by simpa using ModP.iso_mono (R := R) 0 2) (by norm_num)
  exact (ModP.iso_sub h3 h2).C_mul _

lemma ev_Dp : ModP.ev R DpPoly = ModP.Dq R := by
  have hu : ((1728 : R)⁻¹) * 1728 = 1 := by
    have := ZMod.inv_mul_of_unit (1728 : R) h1728
    exact this
  rw [DpPoly, map_mul, ModP.ev_C, ModP.ev_disc, ← mul_assoc]
  have hC : PowerSeries.C ((1728 : R)⁻¹) * (1728 : PowerSeries R) = 1 := by
    rw [← map_ofNat PowerSeries.C 1728, ← map_mul, hu, map_one]
  rw [hC, one_mul]

variable {v : PowerSeries R}

/-- The basis series, in the form computed by the loop. -/
noncomputable def Bs (v : PowerSeries R) (t : ℕ) : PowerSeries R :=
  (ModP.E4 R ^ 3) ^ 101 * (1 + sigmaPart) * (ModP.Dq R * v) ^ t

/-- Every combination of the first 102 basis series has a homogeneous numerator. -/
theorem exists_numerator (hv : ModP.E4 R ^ 3 * v = 1) {E : PowerSeries R}
    (hE : E * (1 + sigmaPart) = 1) (ds : List ℕ) (t : ℕ) (hlen : t + ds.length ≤ 102) :
    ∃ P : MvPolynomial (Fin 2) R, ModP.Iso P 1212 ∧ ModP.ev R P = E * comboS ds (Bs v) t := by
  induction ds generalizing t with
  | nil =>
    exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, by simp [comboS]⟩
  | cons d ds ih =>
    have hlen' : t + 1 + ds.length ≤ 102 := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨P, hP, hPe⟩ := ih (t + 1) hlen'
    have ht : t ≤ 101 := by omega
    have hX : ModP.Iso (MvPolynomial.X 0 ^ (3 * (101 - t)) : MvPolynomial (Fin 2) R)
        (4 * (3 * (101 - t))) :=
      ModP.iso_of_eq (by simpa using ModP.iso_mono (R := R) (3 * (101 - t)) 0) (by norm_num)
    have hD : ModP.Iso (DpPoly ^ t) (t * 12) :=
      ModP.iso_of_eq (iso_Dp.pow t) (by simp)
    have hprod : ModP.Iso (MvPolynomial.C (d : R) *
        (MvPolynomial.X 0 ^ (3 * (101 - t)) * DpPoly ^ t)) 1212 :=
      ModP.iso_of_eq ((hX.mul hD).C_mul _) (by omega)
    refine ⟨_, hprod.add hP, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ModP.ev_C, ModP.ev_X0, ev_Dp, hPe, comboS,
      Bs, alg_basis _ _ _ _ hv ht]
    exact alg_num E _ _ _ _ _ hE

/-! ### The induction -/

lemma reducePow_Ll (b : ℕ) :
    reducePow (p := 607) 2 (AtkinOBrienFinal.Ll 607 b) = rd (L 607 b) := by
  have hcomp : (PadicInt.toZModPow (p := 607) 2).comp (Int.castRingHom ℤ_[607]) =
      Int.castRingHom (ZMod (607 ^ 2)) := RingHom.ext_int _ _
  rw [AtkinOBrienFinal.Ll, reducePow, ModP.psmap_map, hcomp]

lemma h5 : 5 ≤ 607 := by norm_num

lemma sigmaPart_eq :
    (PowerSeries.map (PadicInt.toZModPow (p := 607) 2)
        (AtkinOBrienFinal.Einv 607 h5)) ^ 2 = 1 + sigmaPart := by
  rw [map_Einv_square_squared_general (p := 607) h5, sigmaPart]
  push_cast
  rfl

lemma E_sq_mul_sigma :
    (reducePow (p := 607) 2 (AtkinOBrienFinal.E 607 h5)) ^ 2 * (1 + sigmaPart) = 1 := by
  rw [← sigmaPart_eq, reducePow, ← mul_pow, ← map_mul, AtkinOBrienFinal.E_mul_Einv, map_one,
    one_pow]

/-- Reconstruction specialized to `607`. -/
theorem L_eq_of_prefix (b : ℕ) (hb : 1 ≤ b) (hv : ModP.E4 R ^ 3 * v = 1) (ds : List ℕ)
    (hlen : ds.length ≤ 102)
    (hc : ∀ n < 102, PowerSeries.coeff n (rd (L 607 b)) =
      PowerSeries.coeff n (comboS ds (Bs v) 0)) :
    rd (L 607 b) = comboS ds (Bs v) 0 := by
  obtain ⟨P, hP, hPe⟩ := exists_numerator hv E_sq_mul_sigma ds 0 (by omega)
  have h := partition_two_eq_of_coeff_prefix (p := 607) (by norm_num) h5 h1728 b hb
    (comboS ds (Bs v) 0) P hP hPe (fun n hn => by
      rw [reducePow_Ll]
      exact hc n (by norm_num at hn; omega))
  rwa [reducePow_Ll] at h

/-- The operator step on reduced iterates. -/
lemma rd_L_succ_even {b : ℕ} (hb : Even b) :
    rd (L 607 (b + 1)) = U 607 (rd (BoylanWebb.Φ 607) * rd (L 607 b)) := by
  rw [BoylanWebb.L_succ, T, if_pos hb, map_U, map_mul]

lemma rd_L_succ_odd {b : ℕ} (hb : ¬ Even b) :
    rd (L 607 (b + 1)) = U 607 (rd (L 607 b)) := by
  rw [BoylanWebb.L_succ, T, if_neg hb, map_U]

/-- Coefficient comparison from a canonical equality of represented prefixes. -/
lemma coeff_eq_of_canon {A B : ℕ} {f g : PowerSeries R} (hA : Rep 102 22 A f)
    (hB : Rep 102 22 B g) (h : canon A = canon B) (n : ℕ) (hn : n < 102) :
    PowerSeries.coeff n f = PowerSeries.coeff n g := by
  rw [← hA.coeff n hn, ← hB.coeff n hn]
  exact cast_lane_of_canon h n hn

/-- `L(b)` for `1 ≤ b ≤ 53` in the basis, and the entries of the minor. -/
theorem iterates (rs : Rows) (phiRow : ℕ) (hrows : rows = some (rs, phiRow))
    (hlen : ∀ b < 54, (coordAt b).length ≤ 102)
    (hbase : baseOk rs phiRow = true)
    (hstep : ∀ b < 52, stepOk rs (b + 1) = true)
    (hcol : ∀ j < 25, columnOk rs j = true) :
    (∃ v : PowerSeries R, ModP.E4 R ^ 3 * v = 1 ∧
      ∀ b, 1 ≤ b → b ≤ 53 → rd (L 607 b) = comboS (coordAt b) (Bs v) 0) ∧
    ∀ (i j : ℕ), i < 25 → j < 25 →
      PowerSeries.coeff (i + 26) (rd (L 607 (2 * j + 3))) = (entryAt i j : R) := by
  obtain ⟨pr, hpr, hrs, rfl⟩ := rows_unroll hrows
  have hspec := prelude_spec hpr
  obtain ⟨v, hv, hg⟩ := hspec.g
  have hphi := phi_rep hspec.pgf
  let ph := rd (BoylanWebb.Φ 607)
  have hF : ∀ t, Bs v (t + 1) = Bs v t * (ModP.Dq R * v) := fun t => by
    simp only [Bs, pow_succ, mul_assoc]
  have hb0 : Rep N 22 pr.b0 (Bs v 0) := by
    have : Bs v 0 = (ModP.E4 R ^ 3) ^ 101 * (1 + sigmaPart) := by simp [Bs]
    rw [this]
    exact hspec.b0
  have hR : RowSpec rs (Bs v) ph 0 := basisRows_spec hg hphi hF 102 hb0 hrs
  -- Every coordinate list is represented through the low rows.
  let G : ℕ → PowerSeries R := fun b => comboS (coordAt b) (Bs v) 0
  have hG : ∀ b, 1 ≤ b → b ≤ 53 → rd (L 607 b) = G b := by
    intro b hb1
    induction b, hb1 using Nat.le_induction with
    | base =>
      intro _
      apply L_eq_of_prefix 1 le_rfl hv _ (hlen 1 (by norm_num))
      intro n hn
      obtain ⟨B, hB, hcan⟩ := baseOk_unroll hbase
      have hBr := comboL_rep hR.ls hB
      have hrow := rep_rowOf hphi
      have hL1 : rd (L 607 1) = U 607 (rd (BoylanWebb.Φ 607)) := by
        have h := rd_L_succ_even (b := 0) (by simp)
        simpa [BoylanWebb.L] using h
      rw [hL1]
      exact coeff_eq_of_canon hrow hBr hcan n hn
    | succ b hb1 ih =>
      intro hb53
      have hIH := ih (by omega)
      apply L_eq_of_prefix (b + 1) (by omega) hv _ (hlen (b + 1) (by omega))
      intro n hn
      have hst := hstep (b - 1) (by omega)
      rw [show b - 1 + 1 = b by omega] at hst
      obtain ⟨A, B, hA, hB, hcan⟩ := stepOk_unroll hst
      have hBr := comboL_rep hR.ls hB
      by_cases hodd : b % 2 = 1
      · rw [if_pos hodd] at hA
        have hAr := comboL_rep hR.us hA
        rw [← comboS_U] at hAr
        have hne : ¬ Even b := by
          rw [Nat.even_iff]
          omega
        rw [rd_L_succ_odd hne, hIH]
        exact coeff_eq_of_canon hAr hBr hcan n hn
      · rw [if_neg hodd] at hA
        have hAr := comboL_rep hR.ds hA
        rw [← comboS_Uphi] at hAr
        have he : Even b := by
          rw [Nat.even_iff]
          omega
        rw [rd_L_succ_even he, hIH]
        exact coeff_eq_of_canon hAr hBr hcan n hn
  refine ⟨⟨v, hv, hG⟩, ?_⟩
  intro i j hi hj
  obtain ⟨B, hB, hl⟩ := columnOk_unroll (hcol j hj)
  have hBr := comboL_rep hR.ls hB
  rw [hG (2 * j + 3) (by omega) (by omega), ← hBr.coeff (i + 26) (by omega), ← hl i hi,
    lane_canon _ _ (by omega), ZMod.natCast_mod]

/-- The entries of the actual minor are the saved numbers. -/
theorem entries_eq :
    ∀ (i j : ℕ), i < 25 → j < 25 →
      PowerSeries.coeff (i + 26) (rd (L 607 (2 * j + 3))) = (entryAt i j : R) := by
  obtain ⟨rs, phiRow, hrows, h1, h2, h3, h4⟩ := final_unroll
  exact (iterates rs phiRow hrows h1 h2 h3 h4).2

/-- `L(1), …, L(53)` modulo `607²` in the reconstruction basis. -/
theorem series_eq : ∃ v : PowerSeries R, ModP.E4 R ^ 3 * v = 1 ∧
    ∀ b, 1 ≤ b → b ≤ 53 → rd (L 607 b) = comboS (coordAt b) (Bs v) 0 := by
  obtain ⟨rs, phiRow, hrows, h1, h2, h3, h4⟩ := final_unroll
  exact (iterates rs phiRow hrows h1 h2 h3 h4).1

/-- The saved literal matrix is the table used by the check. -/
theorem matrix_eq_table :
    ∀ i j : Fin 25, Rank607Witness.matrix i j = (entryAt i.val j.val : R) := by
  decide +kernel

/-- The saved minor is the actual minor. -/
theorem rank607Matrix_eq (i j : Fin 25) : rank607Matrix i j = Rank607Witness.matrix i j := by
  rw [matrix_eq_table]
  exact entries_eq i.val j.val i.isLt j.isLt

/-- **At `ℓ = 607`, the stable module has exactly 25 generators at every precision `m ≥ 2`.** -/
theorem rEll_607 (m : ℕ) (hm : 2 ≤ m) : BLBound.rEll 607 m = 25 :=
  Rank607Witness.actual_rank_of_entries rank607Matrix_eq m hm

end RamanujanTau.FiniteArithmetic.Rank607Final
