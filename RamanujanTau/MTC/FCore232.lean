/-
# `F = P · (J̄ f − J̄ g − κ θ)` lies in `Th(11)` (`f_{2,3,2}`)

* `Pv_FE` — `P(q⁵x) = q^{−34} y^{12} x^{−13} P(x)`;
* `Dv_FE` — `D(q⁵x) = μ_D x² D(x)`;
* `FS_ev` — the series `FS` has values `P · D` at good points;
* `FS_mem_Th` — `FS ∈ Th (5 qe) 11 (−q^{−28} y⁹)` when `|y| = 1`.
-/
import RamanujanTau.MTC.Core232
import RamanujanTau.MTC.FCore373

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section FCore
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

theorem Pv_FE (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    Pv hqe ey cy (ex + 5 * qe) cx =
      mono (-(34 * qe) + 12 * ey - 13 * ex) (cy ^ (12 : ℤ) * cx ^ (-13 : ℤ)) * Pv hqe ey cy ex cx := by
  have hA := cAT_ne cy hcx hcy
  have hB := cBT_ne cy hcx hcy
  simp only [Pv, Td]
  rw [θ_sh (h5 hqe) hA (-2) (e := eAT (qe := qe) ey (ex + 5 * qe)) (e' := eAT (qe := qe) ey ex)
      (by unfold eAT; push_cast; ring),
    θ_sh (h5 hqe) hB 3 (e := eBT (qe := qe) ey (ex + 5 * qe)) (e' := eBT (qe := qe) ey ex)
      (by unfold eBT; push_cast; ring)]
  have hM : Msh (5 * qe) (eAT (qe := qe) ey ex) (-2) (cAT cy cx) * Msh (5 * qe) (eBT (qe := qe) ey ex) 3 (cBT cy cx) =
      mono (-(34 * qe) + 12 * ey - 13 * ex) (cy ^ (12 : ℤ) * cx ^ (-13 : ℤ)) := by
    simp only [Msh, mono_mul]
    apply mono_ext
    · push_cast
      simp only [show (-2 : ℤ) + 1 = -1 by norm_num, show (3 : ℤ) + 1 = 4 by norm_num,
        show c2 (-1) = 1 by decide, show c2 4 = 6 by decide]
      unfold eAT eBT; ring
    · unfold cAT cBT
      simp only [neg_neg, zpow_neg, zpow_one, mul_inv, inv_inv, zpow_ofNat]
      field_simp
      try ring
  linear_combination (θ (h5 hqe) (eAT (qe := qe) ey ex) (cAT cy cx) * θ (h5 hqe) (eBT (qe := qe) ey ex) (cBT cy cx)) * hM

noncomputable def Dv (ex : ℤ) (cx : ℂ) : L :=
  Jb hqe * ev (fS hqe ey cy) ex cx - gNum hqe ey cy ex cx - kap (h5 hqe) * thV hqe ey cy ex cx

def CGood (cx : ℂ) : Prop :=
  cx ≠ 0 ∧ cX cy cx * (-1) ≠ 1 ∧ cY cy cx * (-1) ≠ 1 ∧ cAT cy cx ≠ 1 ∧ cBT cy cx ≠ 1

lemma CGood.okx {cx : ℂ} (h : CGood cy cx) (t ex : ℤ) : OKX (qe := qe) ey cy t ex cx := by
  intro _ h'; exact h.2.1 h'.2
lemma CGood.oky {cx : ℂ} (h : CGood cy cx) (t ex : ℤ) : OKY (qe := qe) ey cy t ex cx := by
  intro _ h'; exact h.2.2.1 h'.2

lemma CGood.td {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) (ex : ℤ) : Td hqe ey cy ex cx ≠ 0 := by
  unfold Td
  exact mul_ne_zero (θ_ne_zero (h5 hqe) (cAT_ne cy h.1 hcy) fun _ _ => h.2.2.2.1)
    (θ_ne_zero (h5 hqe) (cBT_ne cy h.1 hcy) fun _ _ => h.2.2.2.2)

theorem Dv_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (h : CGood cy cx) :
    Dv hqe ey cy (ex + 5 * qe) cx = muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * Dv hqe ey cy ex cx := by
  have hf := fV_FE hqe ey cy hcy ex h.1
  have hg := gNum_FE hqe ey cy hcy ex h.1 (h.okx ey cy 0 ex) (h.okx ey cy 1 ex) (h.oky ey cy 0 ex) (h.oky ey cy 1 ex)
  have ht := thV_FE hqe ey cy hcy ex h.1 (h.td hqe ey cy hcy ex) (h.td hqe ey cy hcy (ex + 5 * qe))
  unfold Dv
  linear_combination Jb hqe * hf - hg - kap (h5 hqe) * ht

lemma TS_ev' (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hd : Td hqe ey cy ex cx ≠ 0) :
    ev (TS (qe := qe) ey cy) ex cx = Pv hqe ey cy ex cx * thV hqe ey cy ex cx := by
  rw [TS_ev hqe ey cy ex hcx, Pv, thV, mul_div_cancel₀ _ hd]

noncomputable def GS : ℤ → L :=
  PG1 hqe ey cy 0 + PG1 hqe ey cy 1 + (PG2 hqe ey cy 0 + PG2 hqe ey cy 1)

lemma PG1_ent {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Ent (PG1 hqe ey cy t) := Ent.sumS (term1_udec hqe ey cy h0 h1)
lemma PG2_ent {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Ent (PG2 hqe ey cy t) := Ent.sumS (term2_udec hqe ey cy h0 h1)

lemma GS_ent : Ent (GS hqe ey cy) :=
  ((PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)).add (PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl)).add
    ((PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)).add (PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl))

lemma GS_ev (ex : ℤ) {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) :
    ev (GS hqe ey cy) ex cx = Pv hqe ey cy ex cx * gNum hqe ey cy ex cx := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  unfold GS
  rw [ev_add (a0.add a1) (b0.add b1), ev_add a0 a1, ev_add b0 b1,
    PG1_ev hqe ey cy le_rfl (by norm_num) ex h.1 hcy (h.okx ey cy 0 ex),
    PG1_ev hqe ey cy (by norm_num) le_rfl ex h.1 hcy (h.okx ey cy 1 ex),
    PG2_ev hqe ey cy le_rfl (by norm_num) ex h.1 hcy (h.oky ey cy 0 ex),
    PG2_ev hqe ey cy (by norm_num) le_rfl ex h.1 hcy (h.oky ey cy 1 ex), gNum]
  ring

noncomputable def FS : ℤ → L :=
  MTC.conv (PS (qe := qe) ey cy) (fun n => Jb hqe * fS hqe ey cy n) - GS hqe ey cy -
    fun n => kap (h5 hqe) * TS (qe := qe) ey cy n

lemma FS_ent : Ent (FS hqe ey cy) :=
  (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)).sub ((TS_ent hqe ey cy).smul _)

theorem FS_ev (ex : ℤ) {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) :
    ev (FS hqe ey cy) ex cx = Pv hqe ey cy ex cx * Dv hqe ey cy ex cx := by
  unfold FS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)) ((TS_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) (GS_ent hqe ey cy),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex h.1, ev_smul (fS_ent hqe ey cy),
    ev_smul (TS_ent hqe ey cy), PS_ev hqe ey cy ex h.1, GS_ev hqe ey cy ex hcy h,
    TS_ev' hqe ey cy ex h.1 (h.td hqe ey cy hcy ex), Dv]
  ring

noncomputable def muF : L := mono (-(28 * qe) + 9 * ey) (-cy ^ (9 : ℤ))

theorem FS_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (h : CGood cy cx) :
    ev (FS hqe ey cy) (ex + 5 * qe) cx =
      muF (qe := qe) ey cy * mono (-(ex * 11)) (cx ^ (-(11 : ℤ))) * ev (FS hqe ey cy) ex cx := by
  rw [FS_ev hqe ey cy _ hcy h, FS_ev hqe ey cy _ hcy h, Pv_FE hqe ey cy ex h.1 hcy, Dv_FE hqe ey cy hcy ex h]
  have hm : mono (-(34 * qe) + 12 * ey - 13 * ex) (cy ^ (12 : ℤ) * cx ^ (-13 : ℤ)) *
      (muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ))) =
      muF (qe := qe) ey cy * mono (-(ex * 11)) (cx ^ (-(11 : ℤ))) := by
    unfold muD muF
    simp only [mono_mul]
    apply mono_ext
    · ring
    · have := h.1
      simp only [zpow_neg, zpow_ofNat]
      field_simp
      try ring
  linear_combination (Pv hqe ey cy ex cx * Dv hqe ey cy ex cx) * hm

lemma cgood_nat (hcy : ‖cy‖ = 1) (n : ℕ) : CGood cy ((n : ℂ) + 2) := by
  have hx : ‖((n : ℂ) + 2)‖ = (n : ℝ) + 2 := by
    rw [show ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have h1 : (1 : ℝ) < (n : ℝ) + 2 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hneg : ∀ k : ℤ, k < 0 → ((n : ℝ) + 2) ^ k ≠ 1 := fun k hk => (zpow_lt_one_of_neg₀ h1 hk).ne
  have hpos : ∀ k : ℤ, 0 < k → ((n : ℝ) + 2) ^ k ≠ 1 := fun k hk => (one_lt_zpow₀ h1 hk).ne'
  refine ⟨by rw [← norm_ne_zero_iff, hx]; positivity, ?_, ?_, ?_, ?_⟩
  · unfold cX; refine ne_one_of_norm ?_
    rw [norm_mul, norm_neg, norm_one, norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hneg (-3) (by norm_num)
  · unfold cY; refine ne_one_of_norm ?_
    rw [norm_mul, norm_neg, norm_one, norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hpos 2 (by norm_num)
  · unfold cAT; refine ne_one_of_norm ?_
    rw [norm_neg, norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hneg (-2) (by norm_num)
  · unfold cBT; refine ne_one_of_norm ?_
    rw [norm_neg, norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hpos 3 (by norm_num)

theorem FS_mem_Th (hcy : ‖cy‖ = 1) : FS hqe ey cy ∈ Th (5 * qe) 11 (muF (qe := qe) ey cy) := by
  have hcy0 : cy ≠ 0 := by rw [← norm_ne_zero_iff, hcy]; norm_num
  have hinj : Function.Injective (fun n : ℕ => (n : ℂ) + 2) := fun a b h => by
    simpa using h
  refine mem_Th_of_ev (FS_ent hqe ey cy) 0 (Set.range fun n : ℕ => (n : ℂ) + 2) (Set.infinite_range_of_injective hinj)
    (by rintro c ⟨n, rfl⟩; exact (cgood_nat cy hcy n).1) ?_
  rintro c ⟨n, rfl⟩
  have := FS_FE hqe ey cy hcy0 0 (cgood_nat cy hcy n)
  rw [show ((11 : ℕ) : ℤ) = 11 by norm_num, show (((5 * qe : ℕ) : ℤ)) = 5 * qe by push_cast; ring]
  exact this

end FCore

end MTC.H232
