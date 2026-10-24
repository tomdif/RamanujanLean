/-
# HM Theorem 0.3 for `f_{3,7,3}`: the auxiliary entire function `F = P · J̄ · D`

`P(x) = Π_r j(A_r(x); q^{160}) Π_s j(B_s(x); q^{160})` clears every pole of `g_{3,7,3}` and `θ_{3,4}`.
This file builds the entire series whose values are `P(x)·J̄ f(x)`, `P(x)·θ-terms`, and `P(x)·g-terms`.
-/
import RamanujanTau.MTC.G373
import RamanujanTau.MTC.T373
import RamanujanTau.MTC.UDecL

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Theta series in a power of `x` -/

/-- the series of `x ↦ j(cb t^{eb} x^d; t^N)`. -/
noncomputable def thX (N : ℕ) (d eb : ℤ) (cb : ℂ) : ℤ → L := subst (thSer N 0 1) d eb cb

lemma thX_ent {N : ℕ} (hN : 1 ≤ N) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) : Ent (thX N d eb cb) :=
  (thSer_ent hN 0 one_ne_zero).subst hd eb cb

lemma thX_ev {N : ℕ} (hN : 1 ≤ N) {d : ℤ} (hd : d ≠ 0) (eb : ℤ) (cb : ℂ) (ex : ℤ) (cx : ℂ) :
    ev (thX N d eb cb) ex cx = θ hN (eb + d * ex) (cb * cx ^ d) := by
  rw [thX, ev_subst (thSer_ent hN 0 one_ne_zero) hd, thSer_ev hN 0 one_ne_zero, zero_add, one_mul]

section Core
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the index list `[0, 1, 2, 3]`. -/
def idx4 : List ℤ := [0, 1, 2, 3]

/-- the series of `j(A_r(x); q^{160})`, `A_r = q^{40r+14} y⁷ x^{−3}`. -/
noncomputable def AS (r : ℤ) : ℤ → L := thX (160 * qe) (-3) (qe * (40 * r + 14) + 7 * ey) (cy ^ (7 : ℤ))
/-- the series of `j(B_s(x); q^{160})`, `B_s = q^{40s+14} x⁷ y^{−3}`. -/
noncomputable def BS (s : ℤ) : ℤ → L := thX (160 * qe) 7 (qe * (40 * s + 14) - 3 * ey) (cy ^ (-3 : ℤ))

include hqe in
lemma AS_ent (r : ℤ) : Ent (AS (qe := qe) ey cy r) := thX_ent (h160 hqe) (by norm_num) _ _
include hqe in
lemma BS_ent (s : ℤ) : Ent (BS (qe := qe) ey cy s) := thX_ent (h160 hqe) (by norm_num) _ _

lemma AS_ev (r ex : ℤ) (cx : ℂ) :
    ev (AS (qe := qe) ey cy r) ex cx = θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) := by
  rw [AS, thX_ev (h160 hqe) (by norm_num)]
  congr 1
  unfold eAT; ring

lemma BS_ev (s ex : ℤ) (cx : ℂ) :
    ev (BS (qe := qe) ey cy s) ex cx = θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx) := by
  rw [BS, thX_ev (h160 hqe) (by norm_num)]
  congr 1
  · unfold eBT; ring
  · unfold cBT; ring

/-- `P(x)`. -/
noncomputable def Pv (ex : ℤ) (cx : ℂ) : L :=
  (idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
    (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod

/-- the series of `P(x)`. -/
noncomputable def PS : ℤ → L := cprodL (idx4.map (AS (qe := qe) ey cy) ++ idx4.map (BS (qe := qe) ey cy))

include hqe in
lemma PS_ent : Ent (PS (qe := qe) ey cy) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_append, List.mem_map] at hF
  rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
  · exact AS_ent hqe ey cy r
  · exact BS_ent hqe ey cy s

lemma PS_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) : ev (PS (qe := qe) ey cy) ex cx = Pv hqe ey cy ex cx := by
  rw [PS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_append, List.mem_map] at hF
    rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s) ex hcx]
  simp only [List.map_append, List.map_map, List.prod_append, Pv]
  congr 1
  · congr 1; refine List.map_congr_left fun r _ => ?_; simp [Function.comp, AS_ev hqe]
  · congr 1; refine List.map_congr_left fun s _ => ?_; simp [Function.comp, BS_ev hqe]

/-! ## The `θ_{3,4}` part -/

/-- the series of `Tn r s` (the numerator of the `(r,s)` summand). -/
noncomputable def TnS (r s : ℤ) : ℤ → L :=
  cprodL [monoS (r - 1) (mono (eTn (qe := qe) ey r s 0) ((-1) ^ (r - 1) * (-cy) ^ (s + 2))),
    thX (48 * qe) 3 (qe * (12 * (s - r)) - 3 * ey) (-(cy ^ (-3 : ℤ))),
    thX (160 * qe) 4 (qe * (40 * (r + s) + 28) + 4 * ey) (cy ^ (4 : ℤ))]

include hqe in
lemma TnS_ent (r s : ℤ) : Ent (TnS (qe := qe) ey cy r s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · exact ent_monoS _ _
  · exact thX_ent (h48 hqe) (by norm_num) _ _
  · exact thX_ent (h160 hqe) (by norm_num) _ _

lemma TnS_ev (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (TnS (qe := qe) ey cy r s) ex cx = Tn hqe ey cy r s ex cx := by
  rw [TnS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact ent_monoS _ _
    · exact thX_ent (h48 hqe) (by norm_num) _ _
    · exact thX_ent (h160 hqe) (by norm_num) _ _) ex hcx]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ev_monoS,
    thX_ev (h48 hqe) (by norm_num : (3 : ℤ) ≠ 0), thX_ev (h160 hqe) (by norm_num : (4 : ℤ) ≠ 0), Tn]
  have hm : mono (eTn (qe := qe) ey r s 0) ((-1) ^ (r - 1) * (-cy) ^ (s + 2)) * mono (ex * (r - 1)) (cx ^ (r - 1)) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) := by
    rw [mono_mul]
    apply mono_ext
    · unfold eTn; ring
    · unfold cTn; rw [neg_eq_neg_one_mul cx, mul_zpow]; ring
  have h1 : θ (h48 hqe) (qe * (12 * (s - r)) - 3 * ey + 3 * ex) (-(cy ^ (-3 : ℤ)) * cx ^ (3 : ℤ)) =
      θ (h48 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) := by
    unfold e1T c1T; congr 1 <;> ring
  have h2 : θ (h160 hqe) (qe * (40 * (r + s) + 28) + 4 * ey + 4 * ex) (cy ^ (4 : ℤ) * cx ^ (4 : ℤ)) =
      θ (h160 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) := by
    unfold e2T c2T; congr 1 <;> ring
  rw [← hm, h1, h2]
  ring

/-- the series of `P(x) · Tn/Td` for the `(r,s)` summand. -/
noncomputable def TS (r s : ℤ) : ℤ → L :=
  cprodL (TnS (qe := qe) ey cy r s :: ((idx4.erase r).map (AS (qe := qe) ey cy) ++
    (idx4.erase s).map (BS (qe := qe) ey cy)))

include hqe in
lemma TS_ent (r s : ℤ) : Ent (TS (qe := qe) ey cy r s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
  · exact TnS_ent hqe ey cy r s
  · exact AS_ent hqe ey cy r'
  · exact BS_ent hqe ey cy s'

lemma TS_ev {r s : ℤ} (hr : r ∈ idx4) (hs : s ∈ idx4) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hd : Td hqe ey cy r s ex cx ≠ 0) :
    ev (TS (qe := qe) ey cy r s) ex cx = Pv hqe ey cy ex cx * (Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx) := by
  rw [TS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, TnS_ev hqe ey cy r s ex hcx]
  have hA := List.prod_map_erase (fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)) hr
  have hB := List.prod_map_erase (fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) hs
  have hA' : ((idx4.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx4.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  unfold Td at hd ⊢
  have hA0 := left_ne_zero_of_mul hd
  have hB0 := right_ne_zero_of_mul hd
  unfold Pv
  rw [← hA, ← hB, hA', hB']
  field_simp

end Core

/-! ## The `g_{3,7,3}` part -/

section GPart
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the residue class `s(k) = (t + 1 − 3k) mod 4`. -/
def sK (t k : ℤ) : ℤ := (t + 1 - 3 * k) % 4
/-- `ℓ(k)` with `4ℓ = 3k + s(k) − t − 1`. -/
def lK (t k : ℤ) : ℤ := (3 * k - t - 1 + sK t k) / 4

lemma sK_mem (t k : ℤ) : sK t k ∈ idx4 := by
  unfold sK idx4
  have h0 : 0 ≤ (t + 1 - 3 * k) % 4 := Int.emod_nonneg _ (by norm_num)
  have h1 : (t + 1 - 3 * k) % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma lK_spec (t k : ℤ) : 4 * lK t k = 3 * k + sK t k - t - 1 := by
  unfold lK sK; omega

lemma lK_bound {t : ℤ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (k : ℤ) : |lK t k| ≤ |k| + 2 := by
  have h := lK_spec t k
  have hs := sK_mem t k
  unfold idx4 at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [abs_le]
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> constructor <;> omega

/-- the fixed factor of the first family: `j(q^{7t}x; q³) Π_r j(A_r) Π_{s' ≠ s} j(B_{s'})`. -/
noncomputable def Fix1 (t s : ℤ) : ℤ → L :=
  cprodL (thX (3 * qe) 1 (7 * qe * t) 1 :: (idx4.map (AS (qe := qe) ey cy) ++ (idx4.erase s).map (BS (qe := qe) ey cy)))

/-- `Λ_{ℓ(k)}(B_{s(k)}(x))`. -/
noncomputable def lam1 (t k : ℤ) : ℤ → L :=
  lamX (h160 hqe) (lK t k) 7 (qe * (40 * sK t k + 14) - 3 * ey) (cy ^ (-3 : ℤ))

/-- the scalar `q^{120 C(k,2)} (−y)^t q^{3C(t,2)}`. -/
noncomputable def sig1 (t k : ℤ) : L := mono (120 * qe * c2 k + (3 * qe * c2 t + ey * t)) ((-cy) ^ t)

/-- the `k`-th term of `P · G1_t`. -/
noncomputable def term1 (t k : ℤ) : ℤ → L :=
  MTC.conv (Fix1 (qe := qe) ey cy t (sK t k)) (fun n => sig1 (qe := qe) ey cy t k * lam1 hqe ey cy t k n)

/-- the series of `P(x) · G1_t(x)`. -/
noncomputable def PG1 (t : ℤ) : ℤ → L := sumS (term1 hqe ey cy t)

include hqe in
lemma Fix1_ent (t s : ℤ) : Ent (Fix1 (qe := qe) ey cy t s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
  · exact thX_ent (h3qe hqe) one_ne_zero _ _
  · exact AS_ent hqe ey cy r
  · exact BS_ent hqe ey cy s'

lemma term1_udec {t : ℤ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : UDec (term1 hqe ey cy t) := by
  have hF : UEnt (fun k => Fix1 (qe := qe) ey cy t (sK t k)) :=
    uent_of_fin (Fix1 (qe := qe) ey cy t) (sK t) idx4.toFinset (fun k => List.mem_toFinset.mpr (sK_mem t k))
      fun s _ => Fix1_ent hqe ey cy t s
  have hM : (1 : ℤ) ≤ 120 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam (h160 hqe) (by norm_num : (7 : ℤ) ≠ 0) (fun k => qe * (40 * sK t k + 14) - 3 * ey)
    (qe * 174 + 3 * |ey|) (fun k => by
      dsimp only
      have hs := sK_mem t k
      unfold idx4 at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      rcases hs with h | h | h | h <;> rw [h] <;> exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (cy ^ (-3 : ℤ)) (lK t) 2 (lK_bound ht0 ht2) (sig1 (qe := qe) ey cy t) hM (-(3 * qe * c2 t + ey * t)) fun k => by
      unfold sig1; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

end GPart

section GPartVal
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the Lambert denominator `q^{120(k−1)} X_t z` equals `Q^ℓ / B_s(x)`. -/
lemma lam1_denom (t k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (120 * qe) (eX (qe := qe) ey t ex) 0 k) (cX cy cx * (-1)) =
      mono (((160 * qe : ℕ) : ℤ) * lK t k - ((qe * (40 * sK t k + 14) - 3 * ey) + 7 * ex))
        (cy ^ (-3 : ℤ) * cx ^ (7 : ℤ))⁻¹ := by
  apply mono_ext
  · have h := lK_spec t k
    unfold wE eX
    push_cast
    linear_combination (-(40 * (qe : ℤ))) * h
  · unfold cX
    simp only [zpow_neg]
    field_simp

lemma Fix1_ev_mul (t s : ℤ) (hs : s ∈ idx4) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix1 (qe := qe) ey cy t s) ex cx * θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx) =
      θ (h3qe hqe) (7 * qe * t + ex) cx * Pv hqe ey cy ex cx := by
  rw [Fix1, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent (h3qe hqe) one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    thX_ev (h3qe hqe) one_ne_zero, one_mul, zpow_one]
  have hB := List.prod_map_erase (fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) hs
  have hA' : (idx4.map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      (idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx4.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB', Pv, ← hB]
  beta_reduce
  ring

end GPartVal

end MTC
