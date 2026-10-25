/-
# HM Theorem 0.3 for `f_{1,4,1}`: the entire series of `P · θ`-terms and `P · g`-terms

`P(x) = Π_r j(A_r(x); q^{45}) Π_s j(B_s(x); q^{45})` (`A_r = −q^{15r+6} y⁴ x^{−1}`, `B_s = −q^{15s+6} x⁴ y^{−1}`)
clears every pole of `g_{1,4,1}` and `θ_{1,3}`. The `n = 1` analogue of `Core373` and `PG373`.

* `PS_ev`, `TS_ev` — the series of `P` and of `P · Tn/Td`;
* `PG1_ev`, `PG2_ev` — the series of `P · G1` and `P · G2`; both pole maps are `k ↦ (s(k), ℓ(k))`
  with `3ℓ = k + s`.
-/
import RamanujanTau.MTC.G141
import RamanujanTau.MTC.T141
import RamanujanTau.MTC.PG373

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

section Core
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the index list `[0, 1, 2]`. -/
def idx3 : List ℤ := [0, 1, 2]

/-- the series of `j(A_r(x); q^{45})`. -/
noncomputable def AS (r : ℤ) : ℤ → L := thX (45 * qe) (-1) (qe * (15 * r + 6) + 4 * ey) (-(cy ^ (4 : ℤ)))
/-- the series of `j(B_s(x); q^{45})`. -/
noncomputable def BS (s : ℤ) : ℤ → L := thX (45 * qe) 4 (qe * (15 * s + 6) - ey) (-(cy ^ (-1 : ℤ)))

include hqe in
lemma AS_ent (r : ℤ) : Ent (AS (qe := qe) ey cy r) := thX_ent (h45 hqe) (by norm_num) _ _
include hqe in
lemma BS_ent (s : ℤ) : Ent (BS (qe := qe) ey cy s) := thX_ent (h45 hqe) (by norm_num) _ _

lemma AS_ev (r ex : ℤ) (cx : ℂ) :
    ev (AS (qe := qe) ey cy r) ex cx = θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) := by
  rw [AS, thX_ev (h45 hqe) (by norm_num)]
  congr 1
  · unfold eAT; ring
  · unfold cAT; ring

lemma BS_ev (s ex : ℤ) (cx : ℂ) :
    ev (BS (qe := qe) ey cy s) ex cx = θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx) := by
  rw [BS, thX_ev (h45 hqe) (by norm_num)]
  congr 1
  · unfold eBT; ring
  · unfold cBT; ring

/-- `P(x)`. -/
noncomputable def Pv (ex : ℤ) (cx : ℂ) : L :=
  (idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
    (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod

/-- the series of `P(x)`. -/
noncomputable def PS : ℤ → L := cprodL (idx3.map (AS (qe := qe) ey cy) ++ idx3.map (BS (qe := qe) ey cy))

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

/-! ## The `θ_{1,3}` part -/

/-- the series of `Tn r s`. -/
noncomputable def TnS (r s : ℤ) : ℤ → L :=
  cprodL [monoS r (mono (eTn (qe := qe) ey r s 0) ((-1) ^ r * (-cy) ^ (s + 1))),
    thX (9 * qe) 1 (qe * (3 * (s - r)) - ey) (-(cy ^ (-1 : ℤ))),
    thX (45 * qe) 3 (qe * (15 * (r + s) + 12) + 3 * ey) (cy ^ (3 : ℤ))]

include hqe in
lemma TnS_ent (r s : ℤ) : Ent (TnS (qe := qe) ey cy r s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · exact ent_monoS _ _
  · exact thX_ent (h9 hqe) (by norm_num) _ _
  · exact thX_ent (h45 hqe) (by norm_num) _ _

lemma TnS_ev (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (TnS (qe := qe) ey cy r s) ex cx = Tn hqe ey cy r s ex cx := by
  rw [TnS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact ent_monoS _ _
    · exact thX_ent (h9 hqe) (by norm_num) _ _
    · exact thX_ent (h45 hqe) (by norm_num) _ _) ex hcx]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ev_monoS,
    thX_ev (h9 hqe) (by norm_num : (1 : ℤ) ≠ 0), thX_ev (h45 hqe) (by norm_num : (3 : ℤ) ≠ 0), Tn]
  have hm : mono (eTn (qe := qe) ey r s 0) ((-1) ^ r * (-cy) ^ (s + 1)) * mono (ex * r) (cx ^ r) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) := by
    rw [mono_mul]
    apply mono_ext
    · unfold eTn; ring
    · unfold cTn; rw [neg_eq_neg_one_mul cx, mul_zpow]; ring
  have h1 : θ (h9 hqe) (qe * (3 * (s - r)) - ey + 1 * ex) (-(cy ^ (-1 : ℤ)) * cx ^ (1 : ℤ)) =
      θ (h9 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) := by
    unfold e1T c1T; rw [zpow_one]; congr 1 <;> ring
  have h2 : θ (h45 hqe) (qe * (15 * (r + s) + 12) + 3 * ey + 3 * ex) (cy ^ (3 : ℤ) * cx ^ (3 : ℤ)) =
      θ (h45 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) := by
    unfold e2T c2T; congr 1 <;> ring
  rw [← hm, h1, h2]
  ring

/-- the series of `P(x) · Tn/Td` for the `(r,s)` summand. -/
noncomputable def TS (r s : ℤ) : ℤ → L :=
  cprodL (TnS (qe := qe) ey cy r s :: ((idx3.erase r).map (AS (qe := qe) ey cy) ++
    (idx3.erase s).map (BS (qe := qe) ey cy)))

include hqe in
lemma TS_ent (r s : ℤ) : Ent (TS (qe := qe) ey cy r s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
  · exact TnS_ent hqe ey cy r s
  · exact AS_ent hqe ey cy r'
  · exact BS_ent hqe ey cy s'

lemma TS_ev {r s : ℤ} (hr : r ∈ idx3) (hs : s ∈ idx3) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hd : Td hqe ey cy r s ex cx ≠ 0) :
    ev (TS (qe := qe) ey cy r s) ex cx = Pv hqe ey cy ex cx * (Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx) := by
  rw [TS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, TnS_ev hqe ey cy r s ex hcx]
  have hA := List.prod_map_erase (fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)) hr
  have hB := List.prod_map_erase (fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) hs
  have hA' : ((idx3.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx3.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  unfold Td at hd ⊢
  have hA0 := left_ne_zero_of_mul hd
  have hB0 := right_ne_zero_of_mul hd
  unfold Pv
  rw [← hA, ← hB, hA', hB']
  field_simp

end Core

/-! ## The `g_{1,4,1}` part -/

section GPart
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the residue class `s(k) = (−k) mod 3`. -/
def sK (k : ℤ) : ℤ := (-k) % 3
/-- `ℓ(k)` with `3ℓ = k + s(k)`. -/
def lK (k : ℤ) : ℤ := (k + sK k) / 3

lemma sK_mem (k : ℤ) : sK k ∈ idx3 := by
  unfold sK idx3
  have h0 : 0 ≤ (-k) % 3 := Int.emod_nonneg _ (by norm_num)
  have h1 : (-k) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma lK_spec (k : ℤ) : 3 * lK k = k + sK k := by
  unfold lK sK; omega

lemma lK_bound (k : ℤ) : |lK k| ≤ |k| + 1 := by
  have h := lK_spec k
  have hs := sK_mem k
  unfold idx3 at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rw [abs_le]
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> constructor <;> omega

/-- the fixed factor of the first family: `j(x; q) Π_r j(A_r) Π_{s' ≠ s} j(B_{s'})`. -/
noncomputable def Fix1 (s : ℤ) : ℤ → L :=
  cprodL (thX qe 1 0 1 :: (idx3.map (AS (qe := qe) ey cy) ++ (idx3.erase s).map (BS (qe := qe) ey cy)))

/-- `Λ_{ℓ(k)}(B_{s(k)}(x))`. -/
noncomputable def lam1 (k : ℤ) : ℤ → L :=
  lamX (h45 hqe) (lK k) 4 (qe * (15 * sK k + 6) - ey) (-(cy ^ (-1 : ℤ)))

/-- the scalar `q^{15 C(k,2)}`. -/
noncomputable def sig1 (k : ℤ) : L := mono (15 * qe * c2 k) 1

/-- the `k`-th term of `P · G1`. -/
noncomputable def term1 (k : ℤ) : ℤ → L :=
  MTC.conv (Fix1 (qe := qe) ey cy (sK k)) (fun n => sig1 (qe := qe) k * lam1 hqe ey cy k n)

/-- the series of `P(x) · G1(x)`. -/
noncomputable def PG1 : ℤ → L := sumS (term1 hqe ey cy)

include hqe in
lemma Fix1_ent (s : ℤ) : Ent (Fix1 (qe := qe) ey cy s) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
  · exact thX_ent hqe one_ne_zero _ _
  · exact AS_ent hqe ey cy r
  · exact BS_ent hqe ey cy s'

lemma term1_udec : UDec (term1 hqe ey cy) := by
  have hF : UEnt (fun k => Fix1 (qe := qe) ey cy (sK k)) :=
    uent_of_fin (Fix1 (qe := qe) ey cy) sK idx3.toFinset (fun k => List.mem_toFinset.mpr (sK_mem k))
      fun s _ => Fix1_ent hqe ey cy s
  have hM : (1 : ℤ) ≤ 15 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam (h45 hqe) (by norm_num : (4 : ℤ) ≠ 0) (fun k => qe * (15 * sK k + 6) - ey)
    (qe * 36 + |ey|) (fun k => by
      dsimp only
      have hs := sK_mem k
      unfold idx3 at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      rcases hs with h | h | h <;> rw [h] <;> exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (-(cy ^ (-1 : ℤ))) lK 1 lK_bound (sig1 (qe := qe)) hM 0 fun k => by
      unfold sig1; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

/-- the Lambert denominator `q^{15(k−1)} X z` equals `Q^ℓ / B_s(x)`. -/
lemma lam1_denom (k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (15 * qe) (eX (qe := qe) ey ex) 0 k) (cX cy cx * (-1)) =
      mono (((45 * qe : ℕ) : ℤ) * lK k - ((qe * (15 * sK k + 6) - ey) + 4 * ex))
        (-(cy ^ (-1 : ℤ)) * cx ^ (4 : ℤ))⁻¹ := by
  apply mono_ext
  · have h := lK_spec k
    unfold wE eX
    push_cast
    linear_combination (-(15 * (qe : ℤ))) * h
  · unfold cX
    simp only [zpow_neg]
    field_simp

lemma Fix1_ev_mul (s : ℤ) (hs : s ∈ idx3) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix1 (qe := qe) ey cy s) ex cx * θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx) =
      θ hqe ex cx * Pv hqe ey cy ex cx := by
  rw [Fix1, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent hqe one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    thX_ev hqe one_ne_zero, one_mul, zpow_one, zero_add]
  have hB := List.prod_map_erase (fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) hs
  have hA' : (idx3.map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      (idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx3.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB', Pv, ← hB]
  beta_reduce
  ring

/-- value of the `k`-th term of `P · G1`. -/
lemma term1_ev (k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKX (qe := qe) ey cy ex cx) :
    ev (term1 hqe ey cy k) ex cx = Pv hqe ey cy ex cx * (θ hqe ex cx *
      lamT (15 * qe) (eX (qe := qe) ey ex) (cX cy cx) 0 (-1) k) := by
  have hL : Ent (lam1 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy _) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h45 hqe) (lK k) (by norm_num : (4 : ℤ) ≠ 0) (qe * (15 * sK k + 6) - ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-1) hcy)) ex hcx
  rw [← lam1_denom ey cy k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam1 hqe ey cy k) ex cx =
      (1 - mono (wE (15 * qe) (eX (qe := qe) ey ex) 0 k) (cX cy cx * (-1)))⁻¹ *
        θ (h45 hqe) (qe * (15 * sK k + 6) - ey + 4 * ex) (-(cy ^ (-1 : ℤ)) * cx ^ (4 : ℤ)) := by
    unfold lam1; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix1_ev_mul hqe ey cy (sK k) (sK_mem k) ex hcx
  rw [show eBT (qe := qe) ey (sK k) ex = qe * (15 * sK k + 6) - ey + 4 * ex by unfold eBT; ring,
    show cBT cy cx = -(cy ^ (-1 : ℤ)) * cx ^ (4 : ℤ) by unfold cBT; ring] at hF
  have hsig : sig1 (qe := qe) k = mono (((15 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) := by
    rw [sig1, neg_one_sq_zpow]
    exact mono_ext (by push_cast; ring) rfl
  rw [hΛ, hsig]
  unfold lamT
  have key : ∀ a b c d e f : L, a * d = e * f → a * (b * (c * d)) = f * (e * (b * c)) := by
    intro a b c d e f h; linear_combination (b * c) * h
  exact key _ _ _ _ _ _ hF

/-- **`P · G1`**. -/
theorem PG1_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKX (qe := qe) ey cy ex cx) :
    ev (PG1 hqe ey cy) ex cx = Pv hqe ey cy ex cx * g1 hqe ey cy ex cx := by
  unfold PG1 g1 Av
  rw [ev_sumS (term1_udec hqe ey cy), dif_pos ⟨cX_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h15 hqe) (cX_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * θ hqe ex cx)
      (fun k => by rw [evColFam_apply, term1_ev hqe ey cy k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

/-! ## Second family -/

/-- the fixed factor `j(y; q) Π_{r' ≠ r} j(A_{r'}) Π_s j(B_s)`. -/
noncomputable def Fix2 (r : ℤ) : ℤ → L :=
  cprodL (monoS 0 (θ hqe ey cy) ::
    ((idx3.erase r).map (AS (qe := qe) ey cy) ++ idx3.map (BS (qe := qe) ey cy)))

/-- `Λ_{ℓ(k)}(A_{s(k)}(x))`. -/
noncomputable def lam2 (k : ℤ) : ℤ → L :=
  lamX (h45 hqe) (lK k) (-1) (qe * (15 * sK k + 6) + 4 * ey) (-(cy ^ (4 : ℤ)))

noncomputable def term2 (k : ℤ) : ℤ → L :=
  MTC.conv (Fix2 hqe ey cy (sK k)) (fun n => sig1 (qe := qe) k * lam2 hqe ey cy k n)

/-- the series of `P(x) · G2(x)`. -/
noncomputable def PG2 : ℤ → L := sumS (term2 hqe ey cy)

lemma Fix2_ent (r : ℤ) : Ent (Fix2 hqe ey cy r) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
  · exact ent_monoS _ _
  · exact AS_ent hqe ey cy r'
  · exact BS_ent hqe ey cy s'

lemma term2_udec : UDec (term2 hqe ey cy) := by
  have hF : UEnt (fun k => Fix2 hqe ey cy (sK k)) :=
    uent_of_fin (Fix2 hqe ey cy) sK idx3.toFinset (fun k => List.mem_toFinset.mpr (sK_mem k))
      fun s _ => Fix2_ent hqe ey cy s
  have hM : (1 : ℤ) ≤ 15 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam (h45 hqe) (by norm_num : (-1 : ℤ) ≠ 0) (fun k => qe * (15 * sK k + 6) + 4 * ey)
    (qe * 36 + 4 * |ey|) (fun k => by
      dsimp only
      have hs := sK_mem k
      unfold idx3 at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      rcases hs with h | h | h <;> rw [h] <;> exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (-(cy ^ (4 : ℤ))) lK 1 lK_bound (sig1 (qe := qe)) hM 0 fun k => by
      unfold sig1; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

/-- the Lambert denominator `q^{15(k−1)} Y z` equals `Q^ℓ / A_s(x)`. -/
lemma lam2_denom (k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (15 * qe) (eY (qe := qe) ey ex) 0 k) (cY cy cx * (-1)) =
      mono (((45 * qe : ℕ) : ℤ) * lK k - ((qe * (15 * sK k + 6) + 4 * ey) + -1 * ex))
        (-(cy ^ (4 : ℤ)) * cx ^ (-1 : ℤ))⁻¹ := by
  apply mono_ext
  · have h := lK_spec k
    unfold wE eY
    push_cast
    linear_combination (-(15 * (qe : ℤ))) * h
  · unfold cY
    simp only [zpow_neg]
    field_simp

lemma Fix2_ev_mul (r : ℤ) (hr : r ∈ idx3) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix2 hqe ey cy r) ex cx * θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) =
      θ hqe ey cy * Pv hqe ey cy ex cx := by
  rw [Fix2, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, ev_monoS]
  have hA := List.prod_map_erase (fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)) hr
  have hA' : ((idx3.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : (idx3.map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB', Pv, ← hA]
  simp only [mul_zero, zpow_zero]
  rw [show (mono 0 (1 : ℂ) : L) = 1 from rfl]
  ring

/-- value of the `k`-th term of `P · G2`. -/
lemma term2_ev (k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKY (qe := qe) ey cy ex cx) :
    ev (term2 hqe ey cy k) ex cx = Pv hqe ey cy ex cx * (θ hqe ey cy *
      lamT (15 * qe) (eY (qe := qe) ey ex) (cY cy cx) 0 (-1) k) := by
  have hL : Ent (lam2 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy _) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h45 hqe) (lK k) (by norm_num : (-1 : ℤ) ≠ 0) (qe * (15 * sK k + 6) + 4 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 4 hcy)) ex hcx
  rw [← lam2_denom ey cy k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam2 hqe ey cy k) ex cx =
      (1 - mono (wE (15 * qe) (eY (qe := qe) ey ex) 0 k) (cY cy cx * (-1)))⁻¹ *
        θ (h45 hqe) (qe * (15 * sK k + 6) + 4 * ey + -1 * ex) (-(cy ^ (4 : ℤ)) * cx ^ (-1 : ℤ)) := by
    unfold lam2; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix2_ev_mul hqe ey cy (sK k) (sK_mem k) ex hcx
  rw [show eAT (qe := qe) ey (sK k) ex = qe * (15 * sK k + 6) + 4 * ey + -1 * ex by unfold eAT; ring,
    show cAT cy cx = -(cy ^ (4 : ℤ)) * cx ^ (-1 : ℤ) by unfold cAT; ring] at hF
  have hsig : sig1 (qe := qe) k = mono (((15 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) := by
    rw [sig1, neg_one_sq_zpow]
    exact mono_ext (by push_cast; ring) rfl
  rw [hΛ, hsig]
  unfold lamT
  have key : ∀ a b c d e f : L, a * d = e * f → a * (b * (c * d)) = f * (e * (b * c)) := by
    intro a b c d e f h; linear_combination (b * c) * h
  exact key _ _ _ _ _ _ hF

/-- **`P · G2`**. -/
theorem PG2_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKY (qe := qe) ey cy ex cx) :
    ev (PG2 hqe ey cy) ex cx = Pv hqe ey cy ex cx * g2 hqe ey cy ex cx := by
  unfold PG2 g2 Av
  rw [ev_sumS (term2_udec hqe ey cy), dif_pos ⟨cY_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h15 hqe) (cY_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * θ hqe ey cy)
      (fun k => by rw [evColFam_apply, term2_ev hqe ey cy k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

end GPart

end MTC.H141
