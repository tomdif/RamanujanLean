/-
# Values of `F` at the zeros of `j(A_{r₀}(x); q^{160})`, and the residue identity there

At `x₀` with `A_{r₀}(x₀) = Q^{ℓ₀}` only the pole term `(t₁, k₁)` of the second `g`-family and the
`r = r₀` row of `P · θ` survive (`FS_ev_A`); the bracket vanishes by the `q³ → q⁴⁸` dissection of
`j(q^{7t₁} y; q³)` over `ρ = c₀ − s`, `c₀ = 7k₁ + 4ℓ₀ − 2` (`brA_zero`).
-/
import RamanujanTau.MTC.ResB373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

section EvA
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma Fix2_ev (t r ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix2 hqe ey cy t r) ex cx =
      mono (3 * qe * c2 t) ((-1) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy * mono (ex * t) (cx ^ t) *
      (((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [Fix2, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, ev_monoS]
  have hA' : ((idx4.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : (idx4.map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']

variable {r0 ℓ0 ex0 : ℤ} {cx0 : ℂ}

include hqe in
lemma AS0_ev (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) :
    ev (AS (qe := qe) ey cy r0) ex0 cx0 = 0 := by
  rw [AS_ev hqe, hA, hc, show (160 * qe * ℓ0 : ℤ) = ((160 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h160 hqe) ℓ0

include hqe in
lemma Fix1_zeroA (hr0 : r0 ∈ idx4) (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (t s : ℤ) : ev (Fix1 (qe := qe) ey cy t s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent (h3qe hqe) one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩))) ex0 hcx
    (AS0_ev hqe ey cy hA hc)

lemma Fix2_zeroA (hr0 : r0 ∈ idx4) (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (t r : ℤ) (hr : r ≠ r0) : ev (Fix2 hqe ey cy t r) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨r0, (List.mem_erase_of_ne (Ne.symm hr)).mpr hr0, rfl⟩))) ex0 hcx
    (AS0_ev hqe ey cy hA hc)

include hqe in
lemma TS_zeroA (hr0 : r0 ∈ idx4) (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (r s : ℤ) (hr : r ≠ r0) : ev (TS (qe := qe) ey cy r s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨r0, (List.mem_erase_of_ne (Ne.symm hr)).mpr hr0, rfl⟩))) ex0 hcx
    (AS0_ev hqe ey cy hA hc)

include hqe in
lemma PS_zeroA (hr0 : r0 ∈ idx4) (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) : ev (PS (qe := qe) ey cy) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_append, List.mem_map] at hF
    rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s)
    (List.mem_append_left _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩)) ex0 hcx (AS0_ev hqe ey cy hA hc)

lemma lam2_rel0 (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = r0) :
    (1 - mono (((160 * qe : ℕ) : ℤ) * lK t k - ((160 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) *
      ev (lam2 hqe ey cy t k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h160 hqe) (lK t k) (by norm_num : (-3 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) + 7 * ey)
    (zpow_ne_zero 7 hcy) ex0 hcx
  have he : qe * (40 * sK t k + 14) + 7 * ey + -3 * ex0 = ((160 * qe : ℕ) : ℤ) * ℓ0 := by
    rw [hs]; unfold eAT at hA; push_cast; linarith
  have hcc : cy ^ (7 : ℤ) * cx0 ^ (-3 : ℤ) = 1 := by unfold cAT at hc; exact hc
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam2_zero (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = r0) (hl : lK t k ≠ ℓ0) : ev (lam2 hqe ey cy t k) ex0 cx0 = 0 := by
  have h := lam2_rel0 hqe ey cy hA hc hcx hcy t k hs
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((160 * qe : ℕ) : ℤ) := by have := h160 hqe; omega
  have : ((160 * qe : ℕ) : ℤ) * (lK t k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam2_spec (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = r0) (hl : lK t k = ℓ0) :
    ev (lam2 hqe ey cy t k) ex0 cx0 = mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h160 hqe) := by
  unfold lam2
  rw [lamX_spec (h160 hqe) (lK t k) (by norm_num : (-3 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) + 7 * ey)
    (zpow_ne_zero 7 hcy) ex0 hcx (by rw [hs, hl]; unfold eAT at hA; push_cast; linarith)
    (by unfold cAT at hc; exact hc), hl]

variable {t1 k1 : ℤ}

/-- the value of the pole term of the second family. -/
noncomputable def Va (t1 k1 ℓ0 r0 ex0 : ℤ) (cx0 : ℂ) : L :=
  (mono (3 * qe * c2 t1) ((-1) ^ t1) * θ (h3qe hqe) (7 * qe * t1 + ey) cy * mono (ex0 * t1) (cx0 ^ t1) *
      (((idx4.erase r0).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)) *
    (sig2 (qe := qe) k1 * (mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h160 hqe)))

lemma term2_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = r0) (h4 : lK t1 k1 = ℓ0) (hr0 : r0 ∈ idx4)
    (t k : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) :
    ev (term2 hqe ey cy t k) ex0 cx0 = if t = t1 ∧ k = k1 then Va hqe ey cy t1 k1 ℓ0 r0 ex0 cx0 else 0 := by
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t _) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hs : sK t k = r0
  · by_cases hl : lK t k = ℓ0
    · obtain ⟨rfl, rfl⟩ := pole_unique ht ht1 hs hl h3 h4
      rw [if_pos ⟨rfl, rfl⟩, Fix2_ev hqe ey cy _ _ ex0 hcx, lam2_spec hqe ey cy hA hc hcx hcy _ _ hs hl, hs, Va]
    · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hl h4
      rw [if_neg hne, lam2_zero hqe ey cy hA hc hcx hcy t k hs hl, mul_zero, mul_zero]
  · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hs h3
    rw [if_neg hne, Fix2_zeroA hqe ey cy hr0 hA hc hcx t _ hs, zero_mul]

lemma PG2_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = r0) (h4 : lK t1 k1 = ℓ0) (hr0 : r0 ∈ idx4)
    (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) :
    ev (PG2 hqe ey cy t) ex0 cx0 = if t = t1 then Va hqe ey cy t1 k1 ℓ0 r0 ex0 cx0 else 0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy ht.1 ht.2)]
  by_cases htt : t = t1
  · rw [if_pos htt, hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h3 h4 hr0 t k ht, if_neg (fun h => hk h.2)]),
      evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h3 h4 hr0 t k1 ht, if_pos ⟨htt, rfl⟩]
  · rw [if_neg htt]
    exact hs_zero_of fun k => by
      rw [evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h3 h4 hr0 t k ht, if_neg (fun h => htt h.1)]

lemma PG1_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hr0 : r0 ∈ idx4) (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) : ev (PG1 hqe ey cy t) ex0 cx0 = 0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy ht.1 ht.2)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t _) (hL.smul _) ex0 hcx, Fix1_zeroA hqe ey cy hr0 hA hc hcx, zero_mul]

lemma GS_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = r0) (h4 : lK t1 k1 = ℓ0) (hr0 : r0 ∈ idx4) :
    ev (GS hqe ey cy) ex0 cx0 = Va hqe ey cy t1 k1 ℓ0 r0 ex0 cx0 := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have a2 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have b2 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  unfold GS
  rw [ev_add ((a0.add a1).add a2) ((b0.add b1).add b2), ev_add (a0.add a1) a2, ev_add a0 a1,
    ev_add (b0.add b1) b2, ev_add b0 b1]
  have p := fun t (ht : 0 ≤ t ∧ t ≤ 2) => PG1_A hqe ey cy hA hc hcx hr0 t ht
  have p' := fun t (ht : 0 ≤ t ∧ t ≤ 2) => PG2_A hqe ey cy hA hc hcx hcy ht1 h3 h4 hr0 t ht
  rw [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p' 0 (by norm_num), p' 1 (by norm_num),
    p' 2 (by norm_num)]
  rcases (by omega : t1 = 0 ∨ t1 = 1 ∨ t1 = 2) with rfl | rfl | rfl <;> simp

lemma TT_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hr0 : r0 ∈ idx4) :
    ev (TT (qe := qe) ey cy) ex0 cx0 = ∑ s ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r0 s ex0 cx0 *
      (((idx4.erase r0).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) := by
  unfold TT
  rw [ev_sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 3, TS (qe := qe) ey cy r s k) _
    (fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s)]
  have hr0' : r0 ∈ Finset.Icc (0 : ℤ) 3 := by
    simp only [idx4, List.mem_cons, List.not_mem_nil, or_false] at hr0
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_eq_single r0 (fun r _ hr => by
      rw [ev_sum (F := fun s k => TS (qe := qe) ey cy r s k) _ (fun s _ => TS_ent hqe ey cy r s)]
      exact Finset.sum_eq_zero fun s _ => TS_zeroA hqe ey cy hr0 hA hc hcx r s hr) (fun h => absurd hr0' h),
    ev_sum (F := fun s k => TS (qe := qe) ey cy r0 s k) _ (fun s _ => TS_ent hqe ey cy r0 s)]
  exact Finset.sum_congr rfl fun s _ => TS_ev' hqe ey cy r0 s ex0 hcx

/-- the scalar in front of the pole term. -/
noncomputable def SA (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  sig2 (qe := qe) k1 * mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
    (mono (3 * qe * c2 t1) ((-1) ^ t1) * mono (ex0 * t1) (cx0 ^ t1))

/-- the bracket at an `A`-zero. -/
noncomputable def brA (t1 k1 ℓ0 r0 ex0 : ℤ) (cx0 : ℂ) : L :=
  SA (qe := qe) t1 k1 ℓ0 ex0 cx0 * θ (h3qe hqe) (7 * qe * t1 + ey) cy *
      (idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod +
    ∑ s ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r0 s ex0 cx0 *
      ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod

/-- **`F` at an `A`-zero**. -/
theorem FS_ev_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hr0 : r0 ∈ idx4) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = r0) (h4 : lK t1 k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h160 hqe) *
      ((idx4.erase r0).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        brA hqe ey cy t1 k1 ℓ0 r0 ex0 cx0) := by
  unfold FS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)) ((TT_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) (GS_ent hqe ey cy),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_zeroA hqe ey cy hr0 hA hc hcx,
    ev_smul (TT_ent hqe ey cy), GS_A hqe ey cy hA hc hcx hcy ht1 h3 h4 hr0, TT_A hqe ey cy hA hc hcx hr0,
    Va, brA, SA]
  have hsum : kap (h160 hqe) * ∑ s ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r0 s ex0 cx0 *
      (((idx4.erase r0).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) =
      kap (h160 hqe) * ((idx4.erase r0).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ∑ s ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r0 s ex0 cx0 *
          ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum]
  ring

/-! ## The residue identity at an `A`-zero -/

lemma θ48_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hlk : 4 * ℓ0 = 3 * k1 + r0 - t1 - 1) (s : ℤ) :
    θ (h48 hqe) (e1T (qe := qe) ey r0 s ex0) (c1T cy cx0) =
      θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 2 - s) + 4 * (7 * qe * t1 + ey)) (-cy ^ 4) := by
  congr 1
  · unfold e1T; unfold eAT at hA; push_cast
    first
      | linear_combination hA + 28 * (qe : ℤ) * hlk | linear_combination -hA + 28 * (qe : ℤ) * hlk
      | linear_combination hA - 28 * (qe : ℤ) * hlk | linear_combination -hA - 28 * (qe : ℤ) * hlk
  · unfold c1T; unfold cAT at hc
    have h3 : cx0 ^ (3 : ℤ) = cy ^ (7 : ℤ) := by
      have := eq_inv_of_mul_eq_one_left hc
      rw [this, zpow_neg, inv_inv]
    rw [h3]
    simp only [zpow_neg, zpow_ofNat]
    field_simp
    try ring

lemma θ160_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (s : ℤ) :
    θ (h160 hqe) (e2T (qe := qe) ey r0 s ex0) (c2T cy cx0) =
      Msh (160 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) * θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0) := by
  have hcc : c2T cy cx0 = cBT cy cx0 := by
    unfold cAT at hc
    unfold c2T cBT
    rw [show cx0 ^ (4 : ℤ) * cy ^ (4 : ℤ) = (cx0 ^ (7 : ℤ) * cy ^ (-3 : ℤ)) * (cy ^ (7 : ℤ) * cx0 ^ (-3 : ℤ)) by
      simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
  rw [hcc]
  exact θ_sh (h160 hqe) (cBT_ne cy hcx hcy) ℓ0 (by
    unfold e2T eBT; unfold eAT at hA; push_cast
    first | linear_combination hA | linear_combination -hA)

lemma Tn_A (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hlk : 4 * ℓ0 = 3 * k1 + r0 - t1 - 1) (s : ℤ) :
    Tn hqe ey cy r0 s ex0 cx0 = mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0) *
      θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 2 - s) + 4 * (7 * qe * t1 + ey)) (-cy ^ 4) *
      (Msh (160 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) * θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)) := by
  unfold Tn
  rw [θ48_A hqe ey cy hA hc hcx hcy hlk s, θ160_A hqe ey cy hA hc hcx hcy s]

/-- **the residue identity at an `A`-zero**, modulo four monomial identities. -/
theorem brA_zero (hA : eAT (qe := qe) ey r0 ex0 = 160 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hlk : 4 * ℓ0 = 3 * k1 + r0 - t1 - 1)
    (hm : ∀ s ∈ Finset.Icc (0 : ℤ) 3,
      SA (qe := qe) t1 k1 ℓ0 ex0 cx0 * dmon (qe := qe) (7 * qe * t1 + ey) cy (7 * k1 + 4 * ℓ0 - 2 - s) +
        mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0) * Msh (160 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) = 0) :
    brA hqe ey cy t1 k1 ℓ0 r0 ex0 cx0 = 0 := by
  unfold brA
  rw [dissect_any hqe (7 * qe * t1 + ey) hcy (7 * k1 + 4 * ℓ0 - 2)]
  simp only [Tn_A hqe ey cy hA hc hcx hcy hlk, summ]
  exact alg4 (SA (qe := qe) t1 k1 ℓ0 ex0 cx0)
    ((idx4.map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)
    (fun s => dmon (qe := qe) (7 * qe * t1 + ey) cy (7 * k1 + 4 * ℓ0 - 2 - s))
    (fun s => mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0))
    (fun s => Msh (160 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0))
    (fun s => θ (h48 hqe) (18 * qe - 12 * qe * (7 * k1 + 4 * ℓ0 - 2 - s) + 4 * (7 * qe * t1 + ey)) (-cy ^ 4))
    (fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0))
    (fun s => ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)
    hm (fun s hs => List.prod_map_erase (fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)) (mem_idx4 hs))

end EvA

end MTC
