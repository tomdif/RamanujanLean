/-
# HM Theorem 0.3 for `f_{2,3,2}`: the entire series of `P · θ` and `P · g`

`P(x) = j(A(x); q⁵) j(B(x); q⁵)`, `A = −q⁴ y³ x^{−2}`, `B = −q⁴ x³ y^{−2}`; for `p = 1` the θ-quotient has the single
denominator `Td = P`, so `P · θ_{2,1}/J_5³ = Tn`. The pole maps of both Appell–Lerch families are `k ↦ ℓ = 2k − t`.
-/
import RamanujanTau.MTC.G232
import RamanujanTau.MTC.T232
import RamanujanTau.MTC.PG373
import RamanujanTau.MTC.UDecL2

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section Core
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

noncomputable def AS : ℤ → L := thX (5 * qe) (-2) (qe * 4 + 3 * ey) (-(cy ^ (3 : ℤ)))
noncomputable def BS : ℤ → L := thX (5 * qe) 3 (qe * 4 - 2 * ey) (-(cy ^ (-2 : ℤ)))

include hqe in
lemma AS_ent : Ent (AS (qe := qe) ey cy) := thX_ent (h5 hqe) (by norm_num) _ _
include hqe in
lemma BS_ent : Ent (BS (qe := qe) ey cy) := thX_ent (h5 hqe) (by norm_num) _ _

lemma AS_ev (ex : ℤ) (cx : ℂ) : ev (AS (qe := qe) ey cy) ex cx = θ (h5 hqe) (eAT (qe := qe) ey ex) (cAT cy cx) := by
  rw [AS, thX_ev (h5 hqe) (by norm_num)]
  congr 1
  · unfold eAT; ring
  · unfold cAT; ring

lemma BS_ev (ex : ℤ) (cx : ℂ) : ev (BS (qe := qe) ey cy) ex cx = θ (h5 hqe) (eBT (qe := qe) ey ex) (cBT cy cx) := by
  rw [BS, thX_ev (h5 hqe) (by norm_num)]
  congr 1
  · unfold eBT; ring
  · unfold cBT; ring

/-- `P(x) = Td(x)`. -/
noncomputable def Pv (ex : ℤ) (cx : ℂ) : L := Td hqe ey cy ex cx

noncomputable def PS : ℤ → L := MTC.conv (AS (qe := qe) ey cy) (BS (qe := qe) ey cy)

include hqe in
lemma PS_ent : Ent (PS (qe := qe) ey cy) := (AS_ent hqe ey cy).conv (BS_ent hqe ey cy)

lemma PS_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) : ev (PS (qe := qe) ey cy) ex cx = Pv hqe ey cy ex cx := by
  rw [PS, ev_conv (AS_ent hqe ey cy) (BS_ent hqe ey cy) ex hcx, AS_ev hqe, BS_ev hqe, Pv, Td]

/-- the series of `Tn = P · θ_{2,1}/J_5³`. -/
noncomputable def TS : ℤ → L :=
  cprodL [monoS 0 (mono (eTn (qe := qe) ey) (cTn cy)),
    thX (2 * qe) 2 (-(2 * ey)) (-(cy ^ (-2 : ℤ))),
    thX (5 * qe) 1 (qe * 8 + ey) cy]

include hqe in
lemma TS_ent : Ent (TS (qe := qe) ey cy) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · exact ent_monoS _ _
  · exact thX_ent (h2qe hqe) (by norm_num) _ _
  · exact thX_ent (h5 hqe) (by norm_num) _ _

lemma TS_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) : ev (TS (qe := qe) ey cy) ex cx = Tn hqe ey cy ex cx := by
  rw [TS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact ent_monoS _ _
    · exact thX_ent (h2qe hqe) (by norm_num) _ _
    · exact thX_ent (h5 hqe) (by norm_num) _ _) ex hcx]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ev_monoS,
    thX_ev (h2qe hqe) (by norm_num : (2 : ℤ) ≠ 0), thX_ev (h5 hqe) (by norm_num : (1 : ℤ) ≠ 0), Tn]
  have h1 : θ (h2qe hqe) (-(2 * ey) + 2 * ex) (-(cy ^ (-2 : ℤ)) * cx ^ (2 : ℤ)) = θ (h2qe hqe) (e1T ey ex) (c1T cy cx) := by
    unfold e1T c1T; congr 1 <;> ring
  have h2 : θ (h5 hqe) (qe * 8 + ey + 1 * ex) (cy * cx ^ (1 : ℤ)) = θ (h5 hqe) (e2T (qe := qe) ey ex) (c2T cy cx) := by
    unfold e2T c2T; rw [zpow_one]; congr 1 <;> ring
  rw [h1, h2, show ex * 0 = 0 by ring, zpow_zero]
  rw [show (mono 0 (1 : ℂ) : L) = 1 from rfl]
  ring

end Core

/-! ## The `g_{2,3,2}` part -/

section GPart
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- `ℓ(k) = 2k − t`. -/
def lK (t k : ℤ) : ℤ := 2 * k - t

lemma lK_bound {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℤ) : |lK t k| ≤ 2 * |k| + 1 := by
  unfold lK
  rw [abs_le]
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> constructor <;> omega

/-- the fixed factor of the first family: `j(q^{3t}x; q²) j(A)`. -/
noncomputable def Fix1 (t : ℤ) : ℤ → L := MTC.conv (thX (2 * qe) 1 (3 * qe * t) 1) (AS (qe := qe) ey cy)

noncomputable def lam1 (t k : ℤ) : ℤ → L := lamX (h5 hqe) (lK t k) 3 (qe * 4 - 2 * ey) (-(cy ^ (-2 : ℤ)))

noncomputable def sig1 (t k : ℤ) : L := mono (10 * qe * c2 k + (2 * qe * c2 t + ey * t)) ((-cy) ^ t)

noncomputable def term1 (t k : ℤ) : ℤ → L :=
  MTC.conv (Fix1 (qe := qe) ey cy t) (fun n => sig1 (qe := qe) ey cy t k * lam1 hqe ey cy t k n)

noncomputable def PG1 (t : ℤ) : ℤ → L := sumS (term1 hqe ey cy t)

include hqe in
lemma Fix1_ent (t : ℤ) : Ent (Fix1 (qe := qe) ey cy t) := (thX_ent (h2qe hqe) one_ne_zero _ _).conv (AS_ent hqe ey cy)

lemma term1_udec {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UDec (term1 hqe ey cy t) := by
  have hF : UEnt (fun _ : ℤ => Fix1 (qe := qe) ey cy t) :=
    uent_of_fin (fun _ : ℤ => Fix1 (qe := qe) ey cy t) (fun _ => 0) {0} (fun _ => Finset.mem_singleton_self 0)
      fun _ _ => Fix1_ent hqe ey cy t
  have hM : (1 : ℤ) ≤ 10 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam2 (h5 hqe) (by norm_num : (3 : ℤ) ≠ 0) (fun _ => qe * 4 - 2 * ey) (qe * 4 + 2 * |ey|)
    (fun _ => by
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (-(cy ^ (-2 : ℤ))) (lK t) 1 (lK_bound ht0 ht1) (sig1 (qe := qe) ey cy t) hM (-(2 * qe * c2 t + ey * t)) fun k => by
      unfold sig1; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

/-- the Lambert denominator `q^{10(k−1)} X_t z` equals `Q^ℓ / B(x)`. -/
lemma lam1_denom (t k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (10 * qe) (eX (qe := qe) ey t ex) 0 k) (cX cy cx * (-1)) =
      mono (((5 * qe : ℕ) : ℤ) * lK t k - ((qe * 4 - 2 * ey) + 3 * ex)) (-(cy ^ (-2 : ℤ)) * cx ^ (3 : ℤ))⁻¹ := by
  apply mono_ext
  · unfold wE eX lK; push_cast; ring
  · unfold cX; simp only [zpow_neg]; field_simp

lemma Fix1_ev_mul (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix1 (qe := qe) ey cy t) ex cx * θ (h5 hqe) (eBT (qe := qe) ey ex) (cBT cy cx) =
      θ (h2qe hqe) (3 * qe * t + ex) cx * Pv hqe ey cy ex cx := by
  rw [Fix1, ev_conv (thX_ent (h2qe hqe) one_ne_zero _ _) (AS_ent hqe ey cy) ex hcx,
    thX_ev (h2qe hqe) one_ne_zero, AS_ev hqe, Pv, Td]
  simp only [one_mul, zpow_one]
  ring

lemma term1_ev (t k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKX (qe := qe) ey cy t ex cx) :
    ev (term1 hqe ey cy t k) ex cx = Pv hqe ey cy ex cx * (mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) *
      θ (h2qe hqe) (3 * qe * t + ex) cx * lamT (10 * qe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1) k) := by
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h5 hqe) (lK t k) (by norm_num : (3 : ℤ) ≠ 0) (qe * 4 - 2 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-2) hcy)) ex hcx
  rw [← lam1_denom ey cy t k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam1 hqe ey cy t k) ex cx =
      (1 - mono (wE (10 * qe) (eX (qe := qe) ey t ex) 0 k) (cX cy cx * (-1)))⁻¹ *
        θ (h5 hqe) (qe * 4 - 2 * ey + 3 * ex) (-(cy ^ (-2 : ℤ)) * cx ^ (3 : ℤ)) := by
    unfold lam1; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix1_ev_mul hqe ey cy t ex hcx
  rw [show eBT (qe := qe) ey ex = qe * 4 - 2 * ey + 3 * ex by unfold eBT; ring,
    show cBT cy cx = -(cy ^ (-2 : ℤ)) * cx ^ (3 : ℤ) by unfold cBT; ring] at hF
  have hsig : sig1 (qe := qe) ey cy t k = mono (((10 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) *
      mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) := by
    rw [sig1, mono_mul, neg_one_sq_zpow, one_mul]
    exact mono_ext (by push_cast; ring) rfl
  rw [hΛ, hsig]
  unfold lamT
  have key : ∀ a b c d e f g : L, a * d = e * f → a * (b * c * (g * d)) = f * (c * e * (b * g)) := by
    intro a b c d e f g h; linear_combination (b * c * g) * h
  exact key _ _ _ _ _ _ _ hF

theorem PG1_ev {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hok : OKX (qe := qe) ey cy t ex cx) :
    ev (PG1 hqe ey cy t) ex cx = Pv hqe ey cy ex cx * g1 hqe ey cy t ex cx := by
  unfold PG1 g1 Av
  rw [ev_sumS (term1_udec hqe ey cy ht0 ht1), dif_pos ⟨cX_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h10 hqe) (cX_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * (mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) * θ (h2qe hqe) (3 * qe * t + ex) cx))
      (fun k => by rw [evColFam_apply, term1_ev hqe ey cy t k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

/-! ## Second family -/

noncomputable def Fix2 (t : ℤ) : ℤ → L :=
  MTC.conv (monoS t (mono (2 * qe * c2 t) ((-1) ^ t) * θ (h2qe hqe) (3 * qe * t + ey) cy)) (BS (qe := qe) ey cy)

noncomputable def lam2 (t k : ℤ) : ℤ → L := lamX (h5 hqe) (lK t k) (-2) (qe * 4 + 3 * ey) (-(cy ^ (3 : ℤ)))

noncomputable def sig2 (k : ℤ) : L := mono (10 * qe * c2 k) 1

noncomputable def term2 (t k : ℤ) : ℤ → L :=
  MTC.conv (Fix2 hqe ey cy t) (fun n => sig2 (qe := qe) k * lam2 hqe ey cy t k n)

noncomputable def PG2 (t : ℤ) : ℤ → L := sumS (term2 hqe ey cy t)

lemma Fix2_ent (t : ℤ) : Ent (Fix2 hqe ey cy t) := (ent_monoS _ _).conv (BS_ent hqe ey cy)

lemma term2_udec {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UDec (term2 hqe ey cy t) := by
  have hF : UEnt (fun _ : ℤ => Fix2 hqe ey cy t) :=
    uent_of_fin (fun _ : ℤ => Fix2 hqe ey cy t) (fun _ => 0) {0} (fun _ => Finset.mem_singleton_self 0)
      fun _ _ => Fix2_ent hqe ey cy t
  have hM : (1 : ℤ) ≤ 10 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam2 (h5 hqe) (by norm_num : (-2 : ℤ) ≠ 0) (fun _ => qe * 4 + 3 * ey) (qe * 4 + 3 * |ey|)
    (fun _ => by
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (-(cy ^ (3 : ℤ))) (lK t) 1 (lK_bound ht0 ht1) (fun k => sig2 (qe := qe) k) hM 0 fun k => by
      unfold sig2; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

lemma lam2_denom (t k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (10 * qe) (eY (qe := qe) ey t ex) 0 k) (cY cy cx * (-1)) =
      mono (((5 * qe : ℕ) : ℤ) * lK t k - ((qe * 4 + 3 * ey) + -2 * ex)) (-(cy ^ (3 : ℤ)) * cx ^ (-2 : ℤ))⁻¹ := by
  apply mono_ext
  · unfold wE eY lK; push_cast; ring
  · unfold cY; simp only [zpow_neg]; field_simp; try ring

lemma Fix2_ev_mul (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix2 hqe ey cy t) ex cx * θ (h5 hqe) (eAT (qe := qe) ey ex) (cAT cy cx) =
      mono (2 * qe * c2 t) ((-1) ^ t) * θ (h2qe hqe) (3 * qe * t + ey) cy * mono (ex * t) (cx ^ t) *
        Pv hqe ey cy ex cx := by
  rw [Fix2, ev_conv (ent_monoS _ _) (BS_ent hqe ey cy) ex hcx, ev_monoS, BS_ev hqe, Pv, Td]
  ring

lemma term2_ev (t k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKY (qe := qe) ey cy t ex cx) :
    ev (term2 hqe ey cy t k) ex cx = Pv hqe ey cy ex cx * (mono (2 * qe * c2 t + ex * t) ((-cx) ^ t) *
      θ (h2qe hqe) (3 * qe * t + ey) cy * lamT (10 * qe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1) k) := by
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h5 hqe) (lK t k) (by norm_num : (-2 : ℤ) ≠ 0) (qe * 4 + 3 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 3 hcy)) ex hcx
  rw [← lam2_denom ey cy t k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam2 hqe ey cy t k) ex cx =
      (1 - mono (wE (10 * qe) (eY (qe := qe) ey t ex) 0 k) (cY cy cx * (-1)))⁻¹ *
        θ (h5 hqe) (qe * 4 + 3 * ey + -2 * ex) (-(cy ^ (3 : ℤ)) * cx ^ (-2 : ℤ)) := by
    unfold lam2; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix2_ev_mul hqe ey cy t ex hcx
  rw [show eAT (qe := qe) ey ex = qe * 4 + 3 * ey + -2 * ex by unfold eAT; ring,
    show cAT cy cx = -(cy ^ (3 : ℤ)) * cx ^ (-2 : ℤ) by unfold cAT; ring] at hF
  have hsig : sig2 (qe := qe) k = mono (((10 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) := by
    rw [sig2, neg_one_sq_zpow]
    exact mono_ext (by push_cast; ring) rfl
  have hg : mono (2 * qe * c2 t + ex * t) ((-cx) ^ t) = mono (2 * qe * c2 t) ((-1) ^ t) * mono (ex * t) (cx ^ t) := by
    rw [mono_mul]; exact mono_ext rfl (by rw [neg_eq_neg_one_mul, mul_zpow])
  rw [hΛ, hsig, hg]
  unfold lamT
  have key : ∀ a b d m th mx f g : L, a * d = m * th * mx * f →
      a * (b * (g * d)) = f * (m * mx * th * (b * g)) := by
    intro a b d m th mx f g h; linear_combination (b * g) * h
  exact key _ _ _ _ _ _ _ _ hF

theorem PG2_ev {t : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hok : OKY (qe := qe) ey cy t ex cx) :
    ev (PG2 hqe ey cy t) ex cx = Pv hqe ey cy ex cx * g2 hqe ey cy t ex cx := by
  unfold PG2 g2 Av
  rw [ev_sumS (term2_udec hqe ey cy ht0 ht1), dif_pos ⟨cY_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h10 hqe) (cY_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * (mono (2 * qe * c2 t + ex * t) ((-cx) ^ t) * θ (h2qe hqe) (3 * qe * t + ey) cy))
      (fun k => by rw [evColFam_apply, term2_ev hqe ey cy t k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

end GPart

end MTC.H232
