/-
# `P · g_{3,7,3}` as an entire series

* first family (`X_t`-Lambert sums): `PG1_ev` — `ev (PG1 t) = P(x) · g1_t(x)`;
* second family (`Y_t`-Lambert sums, poles at the zeros of `j(A_r)`): `PG2_ev` — `ev (PG2 t) = P(x) · g2_t(x)`.

Both pole maps are `k ↦ (s(k), ℓ(k))` with `4ℓ = 3k + s − t − 1`.
-/
import RamanujanTau.MTC.Core373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma neg_one_sq_zpow (k : ℤ) : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by
  rw [← mul_zpow]; norm_num

/-- a family that is termwise a multiple of another has proportional sum. -/
lemma hs_eq_mul {s u : SummableFamily ℤ ℂ ℤ} (a : L) (h : ∀ k, u k = a * s k) : hs u = a * hs s := by
  rw [hs, hs, ← SummableFamily.hsum_smul]
  congr 1; ext k : 1
  simp [HahnSeries.of_symm_smul_of_eq_mul, h k]

section PG
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma cX_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cX cy cx ≠ 0 := by
  unfold cX; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx))

lemma cY_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cY cy cx ≠ 0 := by
  unfold cY; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))

/-! ## First family -/

/-- value of the `k`-th term of `P · G1_t`. -/
lemma term1_ev (t k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKX (qe := qe) ey cy t ex cx) :
    ev (term1 hqe ey cy t k) ex cx = Pv hqe ey cy ex cx * (mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) *
      θ (h3qe hqe) (7 * qe * t + ex) cx * lamT (120 * qe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1) k) := by
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t _) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h160 hqe) (lK t k) (by norm_num : (7 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) - 3 * ey)
    (zpow_ne_zero (-3) hcy) ex hcx
  rw [← lam1_denom ey cy t k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam1 hqe ey cy t k) ex cx =
      (1 - mono (wE (120 * qe) (eX (qe := qe) ey t ex) 0 k) (cX cy cx * (-1)))⁻¹ *
        θ (h160 hqe) (qe * (40 * sK t k + 14) - 3 * ey + 7 * ex) (cy ^ (-3 : ℤ) * cx ^ (7 : ℤ)) := by
    unfold lam1; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix1_ev_mul hqe ey cy t (sK t k) (sK_mem t k) ex hcx
  rw [show eBT (qe := qe) ey (sK t k) ex = qe * (40 * sK t k + 14) - 3 * ey + 7 * ex by unfold eBT; ring,
    show cBT cy cx = cy ^ (-3 : ℤ) * cx ^ (7 : ℤ) by unfold cBT; ring] at hF
  have hsig : sig1 (qe := qe) ey cy t k = mono (((120 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) *
      mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) := by
    rw [sig1, mono_mul, neg_one_sq_zpow, one_mul]
    exact mono_ext (by push_cast; ring) rfl
  rw [hΛ, hsig]
  unfold lamT
  have key : ∀ a b c d e f g : L, a * d = e * f → a * (b * c * (g * d)) = f * (c * e * (b * g)) := by
    intro a b c d e f g h; linear_combination (b * c * g) * h
  exact key _ _ _ _ _ _ _ hF

/-- **`P · G1_t`**. -/
theorem PG1_ev {t : ℤ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hok : OKX (qe := qe) ey cy t ex cx) :
    ev (PG1 hqe ey cy t) ex cx = Pv hqe ey cy ex cx * g1 hqe ey cy t ex cx := by
  unfold PG1 g1 Av
  rw [ev_sumS (term1_udec hqe ey cy ht0 ht2), dif_pos ⟨cX_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h120 hqe) (cX_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * (mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) * θ (h3qe hqe) (7 * qe * t + ex) cx))
      (fun k => by rw [evColFam_apply, term1_ev hqe ey cy t k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

/-! ## Second family -/

/-- the fixed factor `(−1)^t q^{3C(t,2)} j(q^{7t} y; q³) x^t Π_{r' ≠ r} j(A_{r'}) Π_s j(B_s)`. -/
noncomputable def Fix2 (t r : ℤ) : ℤ → L :=
  cprodL (monoS t (mono (3 * qe * c2 t) ((-1) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy) ::
    ((idx4.erase r).map (AS (qe := qe) ey cy) ++ idx4.map (BS (qe := qe) ey cy)))

/-- `Λ_{ℓ(k)}(A_{s(k)}(x))`. -/
noncomputable def lam2 (t k : ℤ) : ℤ → L :=
  lamX (h160 hqe) (lK t k) (-3) (qe * (40 * sK t k + 14) + 7 * ey) (cy ^ (7 : ℤ))

/-- the scalar `q^{120 C(k,2)}`. -/
noncomputable def sig2 (k : ℤ) : L := mono (120 * qe * c2 k) 1

noncomputable def term2 (t k : ℤ) : ℤ → L :=
  MTC.conv (Fix2 hqe ey cy t (sK t k)) (fun n => sig2 (qe := qe) k * lam2 hqe ey cy t k n)

/-- the series of `P(x) · G2_t(x)`. -/
noncomputable def PG2 (t : ℤ) : ℤ → L := sumS (term2 hqe ey cy t)

lemma Fix2_ent (t r : ℤ) : Ent (Fix2 hqe ey cy t r) := by
  refine Ent.cprodL _ fun F hF => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
  rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
  · exact ent_monoS _ _
  · exact AS_ent hqe ey cy r'
  · exact BS_ent hqe ey cy s'

lemma term2_udec {t : ℤ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : UDec (term2 hqe ey cy t) := by
  have hF : UEnt (fun k => Fix2 hqe ey cy t (sK t k)) :=
    uent_of_fin (Fix2 hqe ey cy t) (sK t) idx4.toFinset (fun k => List.mem_toFinset.mpr (sK_mem t k))
      fun s _ => Fix2_ent hqe ey cy t s
  have hM : (1 : ℤ) ≤ 120 * qe := by
    have : (1 : ℤ) ≤ qe := (by exact_mod_cast hqe)
    linarith
  have hL := udec_lam (h160 hqe) (by norm_num : (-3 : ℤ) ≠ 0) (fun k => qe * (40 * sK t k + 14) + 7 * ey)
    (qe * 174 + 7 * |ey|) (fun k => by
      dsimp only
      have hs := sK_mem t k
      unfold idx4 at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hq : (0 : ℤ) ≤ qe := by positivity
      have h1 := le_abs_self ey; have h2 := neg_abs_le ey
      rcases hs with h | h | h | h <;> rw [h] <;> exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (cy ^ (7 : ℤ)) (lK t) 2 (lK_bound ht0 ht2) (fun k => sig2 (qe := qe) k) hM 0 fun k => by
      unfold sig2; exact vge_mono (vge_single _ _) (by linarith)
  exact UDec.conv hF hL

end PG

section PGVal
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-- the Lambert denominator `q^{120(k−1)} Y_t z` equals `Q^ℓ / A_s(x)`. -/
lemma lam2_denom (t k ex : ℤ) (cx : ℂ) (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (wE (120 * qe) (eY (qe := qe) ey t ex) 0 k) (cY cy cx * (-1)) =
      mono (((160 * qe : ℕ) : ℤ) * lK t k - ((qe * (40 * sK t k + 14) + 7 * ey) + -3 * ex))
        (cy ^ (7 : ℤ) * cx ^ (-3 : ℤ))⁻¹ := by
  apply mono_ext
  · have h := lK_spec t k
    unfold wE eY
    push_cast
    linear_combination (-(40 * (qe : ℤ))) * h
  · unfold cY
    simp only [zpow_neg]
    field_simp
    try ring

lemma Fix2_ev_mul (t r : ℤ) (hr : r ∈ idx4) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix2 hqe ey cy t r) ex cx * θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) =
      mono (3 * qe * c2 t) ((-1) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy * mono (ex * t) (cx ^ t) *
        Pv hqe ey cy ex cx := by
  rw [Fix2, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, ev_monoS]
  have hA := List.prod_map_erase (fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)) hr
  have hA' : ((idx4.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : (idx4.map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB', Pv, ← hA]
  ring

/-- value of the `k`-th term of `P · G2_t`. -/
lemma term2_ev (t k ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hok : OKY (qe := qe) ey cy t ex cx) :
    ev (term2 hqe ey cy t k) ex cx = Pv hqe ey cy ex cx * (mono (3 * qe * c2 t + ex * t) ((-cx) ^ t) *
      θ (h3qe hqe) (7 * qe * t + ey) cy * lamT (120 * qe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1) k) := by
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t _) (hL.smul _) ex hcx, ev_smul hL]
  have hrel := lamX_rel (h160 hqe) (lK t k) (by norm_num : (-3 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) + 7 * ey)
    (zpow_ne_zero 7 hcy) ex hcx
  rw [← lam2_denom ey cy t k ex cx hcx hcy] at hrel
  have hne := one_sub_mono_ne_zero (hok k)
  have hΛ : ev (lam2 hqe ey cy t k) ex cx =
      (1 - mono (wE (120 * qe) (eY (qe := qe) ey t ex) 0 k) (cY cy cx * (-1)))⁻¹ *
        θ (h160 hqe) (qe * (40 * sK t k + 14) + 7 * ey + -3 * ex) (cy ^ (7 : ℤ) * cx ^ (-3 : ℤ)) := by
    unfold lam2; rw [← hrel, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hF := Fix2_ev_mul hqe ey cy t (sK t k) (sK_mem t k) ex hcx
  rw [show eAT (qe := qe) ey (sK t k) ex = qe * (40 * sK t k + 14) + 7 * ey + -3 * ex by unfold eAT; ring,
    show cAT cy cx = cy ^ (7 : ℤ) * cx ^ (-3 : ℤ) by unfold cAT; ring] at hF
  have hsig : sig2 (qe := qe) k = mono (((120 * qe : ℕ) : ℤ) * c2 k + 0 * k) ((-1) ^ k * (-1) ^ k) := by
    rw [sig2, neg_one_sq_zpow]
    exact mono_ext (by push_cast; ring) rfl
  have hg : mono (3 * qe * c2 t + ex * t) ((-cx) ^ t) = mono (3 * qe * c2 t) ((-1) ^ t) * mono (ex * t) (cx ^ t) := by
    rw [mono_mul]; exact mono_ext rfl (by rw [neg_eq_neg_one_mul, mul_zpow])
  rw [hΛ, hsig, hg]
  unfold lamT
  have key : ∀ a b d m th mx f g : L, a * d = m * th * mx * f →
      a * (b * (g * d)) = f * (m * mx * th * (b * g)) := by
    intro a b d m th mx f g h; linear_combination (b * g) * h
  exact key _ _ _ _ _ _ _ _ hF

/-- **`P · G2_t`**. -/
theorem PG2_ev {t : ℤ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hok : OKY (qe := qe) ey cy t ex cx) :
    ev (PG2 hqe ey cy t) ex cx = Pv hqe ey cy ex cx * g2 hqe ey cy t ex cx := by
  unfold PG2 g2 Av
  rw [ev_sumS (term2_udec hqe ey cy ht0 ht2), dif_pos ⟨cY_ne cy hcx hcy, by norm_num, hok⟩, Alam,
    hs_eq_mul (s := lamF (h120 hqe) (cY_ne cy hcx hcy) (by norm_num) hok)
      (Pv hqe ey cy ex cx * (mono (3 * qe * c2 t + ex * t) ((-cx) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy))
      (fun k => by rw [evColFam_apply, term2_ev hqe ey cy t k ex hcx hcy hok, lamF, ofSupp_apply]; ring)]
  ring

end PGVal

end MTC
