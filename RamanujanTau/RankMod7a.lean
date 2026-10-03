/-
# Dyson's rank mod 7, part A: the 7-dissection of `F(ζ₇) = (q)(ζq)(q/ζ)` and identity `T`

`F(w) = J_{7,3}(q⁷) + q(w²+w³+w⁴+w⁵) J_{7,2}(q⁷) − q³(w³+w⁴) J_{7,1}(q⁷)` (`w⁷ = 1`, `w ≠ 1`), from the
triangular Jacobi product. Then `F(ζ)F(ζ²)F(ζ³) = E(q)²E(q⁷)` identifies Ramanujan's `x, y, z` (the 7-dissection
of `E`, `Ramanujan7Identity`) as `J₇,₂/J₇,₁, J₇,₃/J₇,₂, J₇,₁/J₇,₃`, and `rel4` becomes
`T : J₇,₂³J₇,₃ = J₇,₁J₇,₃³ + q·J₇,₁³J₇,₂`.
-/
import RamanujanTau.RankR03
import RamanujanTau.Ramanujan7Identity

set_option autoImplicit false

namespace CrankProof
open PowerSeries Finset MockTheta5.Bailey
open MockTheta5.JTP (qfacInf isUnit_qfacInf triE)
open scoped PowerSeries.WithPiTopology
local notation "ψ" => MockTheta5.JTP.ψC

section Dissect7

noncomputable def E7C : PowerSeries ℂ →+* PowerSeries ℂ := (PowerSeries.expand 7 (by norm_num)).toRingHom

lemma coeff_E7C (n : ℕ) (f : PowerSeries ℂ) : coeff n (E7C f) = if 7 ∣ n then coeff (n / 7) f else 0 := by
  have h : E7C f = PowerSeries.expand 7 (by norm_num) f := rfl
  rw [h, PowerSeries.coeff_expand]

lemma ψ_E7 (f : PowerSeries ℤ) : ψ (MockTheta5.JTP.E7 f) = E7C (ψ f) := by
  ext n
  have h : MockTheta5.JTP.E7 f = PowerSeries.expand 7 (by norm_num) f := rfl
  rw [coeff_E7C, PowerSeries.coeff_map, h, PowerSeries.coeff_expand]
  split_ifs <;> simp [PowerSeries.coeff_map]

lemma proper_seven {ι : Type*} {e : ι → ℕ} (he : Proper e) : Proper fun i => 7 * e i := fun k =>
  (he k).subset fun i hi => by simp only [Set.mem_setOf_eq] at hi ⊢; omega

lemma lat_seven {ι : Type*} (w : ι → ℂ) {e : ι → ℕ} (he : Proper e) :
    lat w (fun i => 7 * e i) = E7C (lat w e) := by
  ext k
  rw [coeff_lat _ (proper_seven he), coeff_E7C]
  split_ifs with hk
  · rw [coeff_lat _ he]
    refine tsum_congr fun i => ?_
    obtain ⟨j, rfl⟩ := hk
    by_cases h : e i = j
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
  · simp only [show ∀ i, ¬ (7 * e i = k) from fun i h => hk ⟨e i, h.symm⟩, if_false, tsum_zero]

def σ7 : Fin 7 × ℤ ≃ ℤ where
  toFun p := 7 * p.2 + (p.1 : ℤ) - 3
  invFun m := (⟨((m + 3) % 7).toNat, by omega⟩, (m + 3) / 7)
  left_inv p := by
    obtain ⟨⟨i, hi⟩, k⟩ := p
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    constructor <;> omega
  right_inv m := by simp only; omega

lemma expo_split7 {a b : ℕ} (hba : b ≤ a) (i : ℕ) (hi : i < 7) (k : ℤ) :
    expo a b (7 * k + i - 3) = expo a b ((i : ℤ) - 3) + 7 * expo (7 * a) (a * i + b) k := by
  have h1 := two_expo hba (7 * k + i - 3)
  have h2 := two_expo hba ((i : ℤ) - 3)
  have h3 := two_expo (show a * i + b ≤ 7 * a by nlinarith) k
  have : 2 * (expo a b (7 * k + i - 3) : ℤ) = 2 * ((expo a b ((i : ℤ) - 3) : ℤ) + 7 * expo (7 * a) (a * i + b) k) := by
    push_cast at h3
    linear_combination h1 - h2 - 7 * h3
  omega

/-- **the 7-dissection of a theta series** (`u⁷ = 1`). -/
theorem thL_dissect7 {a b : ℕ} (ha : 1 ≤ a) (hba : b ≤ a) {u : ℂ} (hu : u ^ 7 = 1) :
    thL a b u = ∑ i : Fin 7, C ((-u) ^ ((i : ℤ) - 3)) * X ^ expo a b ((i : ℤ) - 3)
      * E7C (thL (7 * a) (a * i + b) 1) := by
  have hu0 : -u ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; rw [h] at hu; norm_num at hu
  rw [thL, ← lat_equiv σ7, lat_fubini _ (proper_equiv (proper_expo ha hba) σ7), tsum_fintype]
  refine sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hp : Proper (expo (7 * a) (a * i + b)) := proper_expo (by omega) (by nlinarith)
  have hw : (fun k : ℤ => (((fun m : ℤ => (-u) ^ m) ∘ σ7) (i, k)))
      = fun k => (-u) ^ ((i : ℤ) - 3) * (-1 : ℂ) ^ k := by
    funext k
    simp only [Function.comp_apply, σ7, Equiv.coe_fn_mk]
    rw [show 7 * k + (i : ℤ) - 3 = 7 * k + ((i : ℤ) - 3) by ring, zpow_add₀ hu0, zpow_mul,
      show (-u) ^ (7 : ℤ) = -1 by rw [zpow_ofNat, neg_pow, hu]; norm_num]
    ring
  have he : (fun k : ℤ => ((expo a b ∘ σ7) (i, k))) = fun k => expo a b ((i : ℤ) - 3) + 7 * expo (7 * a) (a * i + b) k := by
    funext k
    simp only [Function.comp_apply, σ7, Equiv.coe_fn_mk]
    exact expo_split7 hba i hi k
  rw [hw, he, lat_shift _ _ _ (proper_seven hp), lat_seven _ hp]
  rfl

end Dissect7

section F7

/-- `s₁(w) = w²+w³+w⁴+w⁵`, `s₂(w) = w³+w⁴`. -/
noncomputable def s1w (w : ℂ) : ℂ := w ^ 2 + w ^ 3 + w ^ 4 + w ^ 5
noncomputable def s2w (w : ℂ) : ℂ := w ^ 3 + w ^ 4

/-- **7-dissection of `(q)_∞(wq)_∞(q/w)_∞`** for `w⁷ = 1`, `w ≠ 1` (Garvan (5.1)). -/
theorem F7_dissect {w : ℂ} (hw : w ^ 7 = 1) (hw1 : w ≠ 1) :
    pochInf 1 1 * pochInf w 1 * pochInf w⁻¹ 1
      = E7C (ψ (Jab 7 3)) + X * C (s1w w) * E7C (ψ (Jab 7 2)) - X ^ 3 * C (s2w w) * E7C (ψ (Jab 7 1)) := by
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw0
  set u : ℂˣ := Units.mk0 (-w) hnw
  have hJ := jtp_eval u
  rw [theta_lat u] at hJ
  have hu : (u : ℂ) = -w := rfl
  have hui : -((u⁻¹ : ℂˣ) : ℂ) = w⁻¹ := by rw [Units.val_inv_eq_inv_val, hu, inv_neg, neg_neg]
  rw [hui, hu, neg_neg, ← expo_one_zero, show lat (fun m : ℤ => (-w) ^ m) (expo 1 0) = thL 1 0 w from rfl,
    thL_dissect7 le_rfl (by norm_num) hw, Fin.sum_univ_seven] at hJ
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, one_mul, add_zero] at hJ
  rw [thL_zero, map_zero, mul_zero, zero_add] at hJ
  have h3 : ((3 : Fin 7) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 7) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 7) : ℕ) = 5 := rfl
  have h6 : ((6 : Fin 7) : ℕ) = 6 := rfl
  rw [h3, h4, h5, h6, thL_eq_Jab (by norm_num) (by norm_num), thL_eq_Jab (by norm_num) (by norm_num),
    thL_eq_Jab (by norm_num) (by norm_num), thL_eq_Jab (by norm_num) (by norm_num),
    thL_eq_Jab (by norm_num) (by norm_num), thL_eq_Jab (by norm_num) (by norm_num),
    show Jab 7 4 = Jab 7 3 from Jab_symm 7 3 (by norm_num), show Jab 7 5 = Jab 7 2 from Jab_symm 7 2 (by norm_num),
    show Jab 7 6 = Jab 7 1 from Jab_symm 7 1 (by norm_num)] at hJ
  have e1 : expo 1 0 ((1 : ℕ) - 3 : ℤ) = 3 := by decide
  have e2 : expo 1 0 ((2 : ℕ) - 3 : ℤ) = 1 := by decide
  have e3 : expo 1 0 ((3 : ℕ) - 3 : ℤ) = 0 := by decide
  have e4 : expo 1 0 ((4 : ℕ) - 3 : ℤ) = 0 := by decide
  have e5 : expo 1 0 ((5 : ℕ) - 3 : ℤ) = 1 := by decide
  have e6 : expo 1 0 ((6 : ℕ) - 3 : ℤ) = 3 := by decide
  push_cast at hJ e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6] at hJ
  have hwinv : w⁻¹ = w ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hw])
  have hc : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have key : C (1 - w) * (pochInf 1 1 * pochInf w 1 * pochInf w⁻¹ 1)
      = C (1 - w) * (E7C (ψ (Jab 7 3)) + X * C (s1w w) * E7C (ψ (Jab 7 2))
        - X ^ 3 * C (s2w w) * E7C (ψ (Jab 7 1))) := by
    rw [show C (1 - w) * (pochInf 1 1 * pochInf w 1 * pochInf w⁻¹ 1)
        = (1 + C (-w)) * pochInf 1 1 * pochInf w 1 * pochInf w⁻¹ 1 by rw [map_neg, map_sub, map_one]; ring, hJ]
    simp only [show (1 : ℤ) - 3 = -2 by norm_num, show (2 : ℤ) - 3 = -1 by norm_num,
      show (3 : ℤ) - 3 = 0 by norm_num, show (4 : ℤ) - 3 = 1 by norm_num, show (5 : ℤ) - 3 = 2 by norm_num,
      show (6 : ℤ) - 3 = 3 by norm_num, zpow_neg, zpow_zero, zpow_one, pow_zero, pow_one, map_one, one_mul, mul_one]
    have i1 : (-w)⁻¹ = -w ^ 6 := by rw [inv_neg, hwinv]
    have i2 : ((-w) ^ 2)⁻¹ = w ^ 5 := by
      rw [← inv_pow, i1]; linear_combination (w ^ 5) * hw
    simp only [zpow_ofNat] 
    rw [i1, i2]
    simp only [s1w, s2w, map_neg, map_pow, map_sub, map_one, map_add, map_mul]
    ring
  have hu' : IsUnit (C (1 - w) : PowerSeries ℂ) := (isUnit_iff_ne_zero.mpr hc).map C
  exact hu'.mul_left_cancel key

end F7

section Split7
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext)

lemma Pfin_split7 : ∀ N, Pfin 1 1 (7 * N) = ∏ r ∈ range 7, Pfin (r + 1) 7 N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show 7 * (N + 1) = 7 * N + 7 by ring, Pfin, prod_range_add, ← Pfin, Pfin_split7 N]
    simp only [Pfin_succ, prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun r _ => ?_
    congr 2; ring

lemma dvd_sub_prod {d : PowerSeries ℤ} {s : Finset ℕ} (f g : ℕ → PowerSeries ℤ) (h : ∀ j ∈ s, d ∣ f j - g j) :
    d ∣ ∏ j ∈ s, f j - ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      show f a * ∏ j ∈ s, f j - g a * ∏ j ∈ s, g j
        = (f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j) by ring]
    exact dvd_add (dvd_mul_of_dvd_left (h a (mem_insert_self a s)) _)
      (dvd_mul_of_dvd_right (ih fun j hj => h j (mem_insert_of_mem hj)) _)

/-- `(q;q)_∞ = ∏_{r=1}^{7} (q^r;q⁷)_∞`. -/
theorem Pinf_split7 : Pinf 1 1 = ∏ r ∈ range 7, Pinf (r + 1) 7 := by
  symm
  refine Pinf_ext le_rfl le_rfl fun N => ?_
  have h1 : (X : PowerSeries ℤ) ^ (N + 1) ∣ ∏ r ∈ range 7, Pinf (r + 1) 7 - ∏ r ∈ range 7, Pfin (r + 1) 7 N :=
    dvd_sub_prod _ _ fun r _ => X_pow_dvd_Pinf_sub (r + 1) 7 (by omega) (by norm_num) N
  have h2 := X_pow_dvd_Pfin_sub 1 1 N le_rfl le_rfl (7 * N) (by omega)
  rw [Pfin_split7] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- `(q;q)_∞ (q⁷;q⁷)_∞² = J_{7,1} J_{7,2} J_{7,3}`. -/
theorem qfac_J7 : qfacInf * MockTheta5.JTP.eQ7 ^ 2 = Jab 7 1 * Jab 7 2 * Jab 7 3 := by
  have h7 : MockTheta5.JTP.eQ7 = Pinf 7 7 := by
    rw [show MockTheta5.JTP.eQ7 = MockTheta5.JTP.E7 qfacInf from rfl, ← RankProof.Pinf_one_one,
      show MockTheta5.JTP.E7 (Pinf 1 1) = RankProof.Ea 7 (by norm_num) (Pinf 1 1) from rfl,
      RankProof.Ea_Pinf 7 1 1 _ le_rfl le_rfl]
  rw [h7, ← RankProof.Pinf_one_one, Pinf_split7, Jab, Jab, Jab]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  norm_num
  ring

end Split7

section DisC7

noncomputable def dis7C (r : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ := mk fun n => coeff (7 * n + r) f

@[simp] lemma coeff_dis7C (r n : ℕ) (f : PowerSeries ℂ) : coeff n (dis7C r f) = coeff (7 * n + r) f := by
  rw [dis7C, coeff_mk]

lemma dis7C_ψ (r : ℕ) (f : PowerSeries ℤ) : dis7C r (ψ f) = ψ (MockTheta5.JTP.dis7 r f) := by
  ext n; simp [PowerSeries.coeff_map]

lemma coeff_E7C_mul_X (n r d : ℕ) (hr : r < 7) (hd : d < 7) (P : PowerSeries ℂ) :
    coeff (7 * n + r) (X ^ d * E7C P) = if d = r then coeff n P else 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · subst h2; rw [show 7 * n + d - d = 7 * n by omega, coeff_E7C, if_pos (dvd_mul_right 7 n),
      Nat.mul_div_cancel_left _ (by norm_num)]
  · rw [coeff_E7C, if_neg (by omega)]
  · omega
  · rfl

/-- reading off the components of a normal form `Σ_{d<7} q^d P_d(q⁷)`. -/
lemma dis7C_normal (r : ℕ) (hr : r < 7) (P : ℕ → PowerSeries ℂ) :
    dis7C r (∑ d ∈ range 7, X ^ d * E7C (P d)) = P r := by
  ext n
  rw [coeff_dis7C, map_sum]
  rw [sum_eq_single r (fun d hd hdr => by rw [coeff_E7C_mul_X n r d hr (mem_range.mp hd), if_neg hdr])
    (fun h => absurd (mem_range.mpr hr) h), coeff_E7C_mul_X n r r hr hr, if_pos rfl]

end DisC7

section Ident
open MockTheta5.JTP (xQ yQ zQ eQ7 L7 E7 dis7 dis7_normal dis7_E7_mul qfacInf_dissection7)

lemma ω7_phi : ω7 ^ 6 + ω7 ^ 5 + ω7 ^ 4 + ω7 ^ 3 + ω7 ^ 2 + ω7 + 1 = 0 := by
  have h := ω7_prim.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h
  linear_combination h

/-- `F(w) = (q)_∞(wq)_∞(q/w)_∞`. -/
noncomputable def F7 (w : ℂ) : PowerSeries ℂ := pochInf 1 1 * pochInf w 1 * pochInf w⁻¹ 1

lemma F7_prod : F7 ω7 * F7 (ω7 ^ 2) * F7 (ω7 ^ 3) = ψ (qfacInf ^ 2 * E7 qfacInf) := by
  have h := prod_pochInf_roots_gen ω7_prim (by norm_num : (7 : ℕ) ≠ 0)
  have hE : MockTheta5.JTP.ψC (Ep 7 (by norm_num) qfacInf) = ψ (E7 qfacInf) := rfl
  rw [hE] at h
  simp only [prod_range_succ, prod_range_zero, one_mul, pow_zero, pow_one] at h
  have i1 : ω7⁻¹ = ω7 ^ 6 := ω7_inv
  have i2 : (ω7 ^ 2)⁻¹ = ω7 ^ 5 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, ω7_pow7])
  have i3 : (ω7 ^ 3)⁻¹ = ω7 ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, ω7_pow7])
  rw [F7, F7, F7, i1, i2, i3, map_mul, map_pow, ← h, ← pochInf_one_eq]
  ring

lemma E7C_C (c : ℂ) : E7C (C c) = C c := by
  ext n; rw [coeff_E7C, coeff_C, coeff_C]; split_ifs <;> first | rfl | omega

lemma E7C_X : E7C X = X ^ 7 := PowerSeries.expand_X 7 (by norm_num)

/-- the components of `∏_{i=1}^{3}(A + q aᵢ B − q³ bᵢ C)` (`A, B, C` series in `q⁷`). -/
noncomputable def P3 (A B Cc : PowerSeries ℂ) (a1 a2 a3 b1 b2 b3 : ℂ) (d : ℕ) : PowerSeries ℂ :=
  if d = 0 then A ^ 3 + C (b1 * b2 * a3 + b1 * b3 * a2 + b2 * b3 * a1) * X * Cc ^ 2 * B
  else if d = 1 then C (a1 + a2 + a3) * A ^ 2 * B
  else if d = 2 then C (a1 * a2 + a1 * a3 + a2 * a3) * A * B ^ 2 - C (b1 * b2 * b3) * X * Cc ^ 3
  else if d = 3 then C (a1 * a2 * a3) * B ^ 3 - C (b1 + b2 + b3) * A ^ 2 * Cc
  else if d = 4 then -C (b1 * a2 + b1 * a3 + b2 * a1 + b2 * a3 + b3 * a1 + b3 * a2) * A * B * Cc
  else if d = 5 then -C (b1 * a2 * a3 + b2 * a1 * a3 + b3 * a1 * a2) * B ^ 2 * Cc
  else C (b1 * b2 + b1 * b3 + b2 * b3) * A * Cc ^ 2

lemma prod3_normal (A B Cc : PowerSeries ℂ) (a1 a2 a3 b1 b2 b3 : ℂ) :
    (E7C A + X * C a1 * E7C B - X ^ 3 * C b1 * E7C Cc) * (E7C A + X * C a2 * E7C B - X ^ 3 * C b2 * E7C Cc)
      * (E7C A + X * C a3 * E7C B - X ^ 3 * C b3 * E7C Cc)
      = ∑ d ∈ range 7, X ^ d * E7C (P3 A B Cc a1 a2 a3 b1 b2 b3 d) := by
  simp only [sum_range_succ, sum_range_zero, zero_add, P3]
  simp only [show (1 : ℕ) ≠ 0 from by norm_num, show (2 : ℕ) ≠ 0 from by norm_num, show (2 : ℕ) ≠ 1 from by norm_num,
    show (3 : ℕ) ≠ 0 from by norm_num, show (3 : ℕ) ≠ 1 from by norm_num, show (3 : ℕ) ≠ 2 from by norm_num,
    show (4 : ℕ) ≠ 0 from by norm_num, show (4 : ℕ) ≠ 1 from by norm_num, show (4 : ℕ) ≠ 2 from by norm_num,
    show (4 : ℕ) ≠ 3 from by norm_num, show (5 : ℕ) ≠ 0 from by norm_num, show (5 : ℕ) ≠ 1 from by norm_num,
    show (5 : ℕ) ≠ 2 from by norm_num, show (5 : ℕ) ≠ 3 from by norm_num, show (5 : ℕ) ≠ 4 from by norm_num,
    show (6 : ℕ) ≠ 0 from by norm_num, show (6 : ℕ) ≠ 1 from by norm_num, show (6 : ℕ) ≠ 2 from by norm_num,
    show (6 : ℕ) ≠ 3 from by norm_num, show (6 : ℕ) ≠ 4 from by norm_num, show (6 : ℕ) ≠ 5 from by norm_num,
    if_true, if_false]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, E7C_C, E7C_X]
  ring

lemma qsq_classes : dis7 1 (qfacInf ^ 2) = -2 * eQ7 ^ 2 * xQ * yQ ∧ dis7 5 (qfacInf ^ 2) = 2 * eQ7 ^ 2 * xQ * zQ
    ∧ dis7 6 (qfacInf ^ 2) = -2 * eQ7 ^ 2 * yQ * zQ := by
  have hn : qfacInf ^ 2 = X ^ 0 * E7 (eQ7 ^ 2 * (xQ ^ 2 - 2 * X * zQ)) + X ^ 1 * E7 (eQ7 ^ 2 * (-2 * xQ * yQ))
      + X ^ 2 * E7 (eQ7 ^ 2 * (yQ ^ 2 - 2 * xQ)) + X ^ 3 * E7 (eQ7 ^ 2 * (2 * yQ + X * zQ ^ 2))
      + X ^ 4 * E7 (eQ7 ^ 2) + X ^ 5 * E7 (eQ7 ^ 2 * (2 * xQ * zQ)) + X ^ 6 * E7 (eQ7 ^ 2 * (-2 * yQ * zQ)) := by
    rw [qfacInf_dissection7, L7]
    have h7 : E7 (X : PowerSeries ℤ) = X ^ 7 := PowerSeries.expand_X 7 (by norm_num)
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, h7]
    ring
  refine ⟨?_, ?_, ?_⟩ <;> rw [hn, dis7_normal _ (by norm_num)] <;> simp <;> ring

lemma ω7_pow_ne (a : ℕ) (h0 : 0 < a) (h7 : a < 7) : ω7 ^ a ≠ 1 := ω7_prim.pow_ne_one_of_pos_of_lt (by omega) h7

lemma F7_pow (a : ℕ) (h0 : 0 < a) (h7 : a < 7) :
    F7 (ω7 ^ a) = E7C (ψ (Jab 7 3)) + X * C (s1w (ω7 ^ a)) * E7C (ψ (Jab 7 2))
      - X ^ 3 * C (s2w (ω7 ^ a)) * E7C (ψ (Jab 7 1)) :=
  F7_dissect (by rw [← pow_mul, mul_comm, pow_mul, ω7_pow7, one_pow]) (ω7_pow_ne a h0 h7)

/-- the classes of `F(ζ)F(ζ²)F(ζ³) = E²E(q⁷)`. -/
lemma prod_class (r : ℕ) (hr : r < 7) :
    P3 (ψ (Jab 7 3)) (ψ (Jab 7 2)) (ψ (Jab 7 1)) (s1w ω7) (s1w (ω7 ^ 2)) (s1w (ω7 ^ 3))
      (s2w ω7) (s2w (ω7 ^ 2)) (s2w (ω7 ^ 3)) r = ψ (qfacInf * dis7 r (qfacInf ^ 2)) := by
  have h := congrArg (dis7C r) F7_prod
  rw [show F7 ω7 = F7 (ω7 ^ 1) by rw [pow_one], F7_pow 1 (by norm_num) (by norm_num), F7_pow 2 (by norm_num) (by norm_num),
    F7_pow 3 (by norm_num) (by norm_num), prod3_normal, dis7C_normal r hr, dis7C_ψ, mul_comm, dis7_E7_mul r hr] at h
  simpa [pow_one] using h

lemma e1_val : s1w ω7 + s1w (ω7 ^ 2) + s1w (ω7 ^ 3) = -2 := by
  unfold s1w
  linear_combination (ω7 ^ 9 - ω7 ^ 8 + ω7 ^ 6 - ω7 ^ 5 + ω7 ^ 4 + ω7 ^ 2 - 2 * ω7 + 2) * ω7_phi

lemma e5_val : s2w ω7 * s1w (ω7 ^ 2) * s1w (ω7 ^ 3) + s2w (ω7 ^ 2) * s1w ω7 * s1w (ω7 ^ 3)
    + s2w (ω7 ^ 3) * s1w ω7 * s1w (ω7 ^ 2) = -2 := by
  unfold s1w s2w
  linear_combination (ω7 ^ 23 + ω7 ^ 22 + ω7 ^ 21 + 2 * ω7 ^ 20 + 2 * ω7 ^ 19 + 2 * ω7 ^ 17 + 2 * ω7 ^ 16 - ω7 ^ 15
    + 3 * ω7 ^ 14 + ω7 ^ 13 - 2 * ω7 ^ 8 + 2 * ω7 ^ 7 - 2 * ω7 + 2) * ω7_phi

lemma e6_val : s2w ω7 * s2w (ω7 ^ 2) + s2w ω7 * s2w (ω7 ^ 3) + s2w (ω7 ^ 2) * s2w (ω7 ^ 3) = -2 := by
  unfold s2w
  linear_combination (ω7 ^ 14 - ω7 ^ 13 + ω7 ^ 12 + ω7 ^ 9 - 2 * ω7 ^ 8 + 2 * ω7 ^ 7 - 2 * ω7 + 2) * ω7_phi

lemma two_ne_PSC : (2 : PowerSeries ℂ) ≠ 0 := by
  intro h; have := congrArg constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this

/-- **Ramanujan's `x, y, z` are theta quotients**: `x = J₇,₂/J₇,₁`, `y = J₇,₃/J₇,₂`, `z = J₇,₁/J₇,₃`. -/
theorem xyz_J : xQ * Jab 7 1 = Jab 7 2 ∧ yQ * Jab 7 2 = Jab 7 3 ∧ zQ * Jab 7 3 = Jab 7 1 := by
  obtain ⟨c1, c5, c6⟩ := qsq_classes
  have h1 := prod_class 1 (by norm_num)
  have h5 := prod_class 5 (by norm_num)
  have h6 := prod_class 6 (by norm_num)
  simp only [P3, show (1 : ℕ) ≠ 0 from by norm_num, show (5 : ℕ) ≠ 0 from by norm_num, show (5 : ℕ) ≠ 1 from by norm_num,
    show (5 : ℕ) ≠ 2 from by norm_num, show (5 : ℕ) ≠ 3 from by norm_num, show (5 : ℕ) ≠ 4 from by norm_num,
    show (6 : ℕ) ≠ 0 from by norm_num, show (6 : ℕ) ≠ 1 from by norm_num, show (6 : ℕ) ≠ 2 from by norm_num,
    show (6 : ℕ) ≠ 3 from by norm_num, show (6 : ℕ) ≠ 4 from by norm_num, show (6 : ℕ) ≠ 5 from by norm_num,
    if_true, if_false] at h1 h5 h6
  rw [e1_val] at h1
  rw [show s2w ω7 * s1w (ω7 ^ 2) * s1w (ω7 ^ 3) + s2w (ω7 ^ 2) * s1w ω7 * s1w (ω7 ^ 3)
      + s2w (ω7 ^ 3) * s1w ω7 * s1w (ω7 ^ 2) = -2 from e5_val] at h5
  rw [e6_val] at h6
  rw [c1] at h1; rw [c5] at h5; rw [c6] at h6
  have hC2 : (C (-2 : ℂ) : PowerSeries ℂ) = -2 := by rw [map_neg, map_ofNat]
  simp only [map_mul, map_pow, map_neg, map_ofNat, hC2] at h1 h5 h6
  have g1 : Jab 7 3 ^ 2 * Jab 7 2 = qfacInf * (eQ7 ^ 2 * xQ * yQ) := by
    apply MockTheta5.JTP.ψC_injective
    apply mul_left_cancel₀ (neg_ne_zero.mpr two_ne_PSC)
    simp only [map_mul, map_pow]
    linear_combination h1
  have g5 : Jab 7 2 ^ 2 * Jab 7 1 = qfacInf * (eQ7 ^ 2 * xQ * zQ) := by
    apply MockTheta5.JTP.ψC_injective
    apply mul_left_cancel₀ two_ne_PSC
    simp only [map_mul, map_pow]
    linear_combination h5
  have g6 : Jab 7 1 ^ 2 * Jab 7 3 = qfacInf * (eQ7 ^ 2 * yQ * zQ) := by
    apply MockTheta5.JTP.ψC_injective
    apply mul_left_cancel₀ (neg_ne_zero.mpr two_ne_PSC)
    simp only [map_mul, map_pow]
    linear_combination h6
  have hq := qfac_J7
  have hxyz := MockTheta5.JTP.xyz_eq_one
  have u1 := (isUnit_Jab 7 1 (by norm_num) (by norm_num)).ne_zero
  have u2 := (isUnit_Jab 7 2 (by norm_num) (by norm_num)).ne_zero
  have u3 := (isUnit_Jab 7 3 (by norm_num) (by norm_num)).ne_zero
  have k1 : Jab 7 3 = Jab 7 1 * xQ * yQ :=
    mul_left_cancel₀ (mul_ne_zero u2 u3) (by linear_combination g1 + xQ * yQ * hq)
  have k5 : Jab 7 2 = Jab 7 3 * xQ * zQ :=
    mul_left_cancel₀ (mul_ne_zero u1 u2) (by linear_combination g5 + xQ * zQ * hq)
  have k6 : Jab 7 1 = Jab 7 2 * yQ * zQ :=
    mul_left_cancel₀ (mul_ne_zero u1 u3) (by linear_combination g6 + yQ * zQ * hq)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination xQ * k6 + Jab 7 2 * hxyz
  · linear_combination yQ * k5 + Jab 7 3 * hxyz
  · linear_combination zQ * k1 + Jab 7 1 * hxyz

/-- **the theta identity `T`**: `J₇,₂³J₇,₃ = J₇,₁J₇,₃³ + q·J₇,₁³J₇,₂`. -/
theorem identity_T : Jab 7 2 ^ 3 * Jab 7 3 = Jab 7 1 * Jab 7 3 ^ 3 + X * Jab 7 1 ^ 3 * Jab 7 2 := by
  obtain ⟨hx, hy, -⟩ := xyz_J
  have r4 := MockTheta5.JTP.rel4
  have hxyz := MockTheta5.JTP.xyz_eq_one
  have hb : Jab 7 2 = xQ * Jab 7 1 := hx.symm
  have hc : Jab 7 3 = yQ * xQ * Jab 7 1 := by rw [← hy, hb]; ring
  rw [hc, hb]
  linear_combination (Jab 7 1 ^ 4 * xQ ^ 3 * yQ) * r4 + (X * Jab 7 1 ^ 4 * xQ * (xQ * yQ * zQ + 1)) * hxyz

end Ident

end CrankProof
