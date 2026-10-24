/-
# Values of `F` at the zeros of `j(B_{s₀}(x); q^{160})`

At `x₀ = cx₀ t^{ex₀}` with `B_{s₀}(x₀) = Q^{ℓ₀}` every factor `j(B_{s₀})` vanishes, so only the pole term
`(t₁, k₁)` of `P · g` (with `s(k₁) = s₀`, `ℓ(k₁) = ℓ₀`) and the `s = s₀` column of `P · θ` survive:

`FS_ev_B` — `F(x₀) = −κ · Π_{s ≠ s₀} j(B_s) · brB`, where
`brB = σ₁ · (−1)^{ℓ₀+1} Q^{−C(ℓ₀,2)} · j(q^{7t₁}x₀; q³) · Π_r j(A_r) + Σ_r Tn(r, s₀) · Π_{r' ≠ r} j(A_{r'})`.
-/
import RamanujanTau.MTC.FCore373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma hs_zero_of {u : SummableFamily ℤ ℂ ℤ} (h : ∀ k, u k = 0) : hs u = 0 := by
  rw [hs_eq_mul (s := u) 0 (fun k => by rw [h k, zero_mul]), zero_mul]

lemma hs_single_of {u : SummableFamily ℤ ℂ ℤ} (k0 : ℤ) (h : ∀ k, k ≠ k0 → u k = 0) : hs u = u k0 := by
  classical
  have hu : u = SummableFamily.single k0 (u k0) := by
    ext k : 1
    by_cases hk : k = k0
    · subst hk; simp [SummableFamily.single]
    · simp [SummableFamily.single, hk, h k hk]
  conv_lhs => rw [hu]
  rw [hs_eq, SummableFamily.hsum_single]

lemma ev_cprodL_zero {l : List (ℤ → L)} (hl : ∀ F ∈ l, Ent F) {G : ℤ → L} (hG : G ∈ l) (e : ℤ) {c : ℂ}
    (hc : c ≠ 0) (h0 : ev G e c = 0) : ev (cprodL l) e c = 0 := by
  rw [ev_cprodL l hl e hc]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨G, hG, h0⟩)

lemma sum_rearr (κ B : L) (f g : ℤ → L) (S : Finset ℤ) :
    κ * ∑ r ∈ S, f r * (g r * B) = κ * B * ∑ r ∈ S, f r * g r := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

section EvB
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

/-! ## Direct values of the fixed factors -/

lemma Fix1_ev (t s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix1 (qe := qe) ey cy t s) ex cx = θ (h3qe hqe) (7 * qe * t + ex) cx *
      ((idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [Fix1, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent (h3qe hqe) one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    thX_ev (h3qe hqe) one_ne_zero, one_mul, zpow_one]
  have hA' : (idx4.map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      (idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx4.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']
  try ring_nf

lemma TS_ev' (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (TS (qe := qe) ey cy r s) ex cx = Tn hqe ey cy r s ex cx *
      (((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [TS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    TnS_ev hqe ey cy r s ex hcx]
  have hA' : ((idx4.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx4.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx4.erase s).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']

/-! ## Vanishing at a `B`-zero -/

variable {s0 ℓ0 ex0 : ℤ} {cx0 : ℂ}

include hqe in
lemma BS0_ev (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) :
    ev (BS (qe := qe) ey cy s0) ex0 cx0 = 0 := by
  rw [BS_ev hqe, hB, hc, show (160 * qe * ℓ0 : ℤ) = ((160 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h160 hqe) ℓ0

include hqe in
lemma Fix1_zero (hs0 : s0 ∈ idx4) (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (t s : ℤ) (hs : s ≠ s0) : ev (Fix1 (qe := qe) ey cy t s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent (h3qe hqe) one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨s0, (List.mem_erase_of_ne (Ne.symm hs)).mpr hs0, rfl⟩))) ex0 hcx
    (BS0_ev hqe ey cy hB hc)

lemma Fix2_zero (hs0 : s0 ∈ idx4) (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (t r : ℤ) : ev (Fix2 hqe ey cy t r) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩))) ex0 hcx
    (BS0_ev hqe ey cy hB hc)

include hqe in
lemma TS_zero (hs0 : s0 ∈ idx4) (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (r s : ℤ) (hs : s ≠ s0) : ev (TS (qe := qe) ey cy r s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨s0, (List.mem_erase_of_ne (Ne.symm hs)).mpr hs0, rfl⟩))) ex0 hcx
    (BS0_ev hqe ey cy hB hc)

include hqe in
lemma PS_zero (hs0 : s0 ∈ idx4) (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) : ev (PS (qe := qe) ey cy) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_append, List.mem_map] at hF
    rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s)
    (List.mem_append_right _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩)) ex0 hcx (BS0_ev hqe ey cy hB hc)

/-! ## The Lambert factors at a `B`-zero -/

lemma lam1_rel0 (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = s0) :
    (1 - mono (((160 * qe : ℕ) : ℤ) * lK t k - ((160 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) *
      ev (lam1 hqe ey cy t k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h160 hqe) (lK t k) (by norm_num : (7 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) - 3 * ey)
    (zpow_ne_zero (-3) hcy) ex0 hcx
  have he : qe * (40 * sK t k + 14) - 3 * ey + 7 * ex0 = ((160 * qe : ℕ) : ℤ) * ℓ0 := by
    rw [hs]; unfold eBT at hB; push_cast; linarith
  have hcc : cy ^ (-3 : ℤ) * cx0 ^ (7 : ℤ) = 1 := by unfold cBT at hc; rw [mul_comm]; exact hc
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam1_zero (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = s0) (hl : lK t k ≠ ℓ0) : ev (lam1 hqe ey cy t k) ex0 cx0 = 0 := by
  have h := lam1_rel0 hqe ey cy hB hc hcx hcy t k hs
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((160 * qe : ℕ) : ℤ) := by have := h160 hqe; omega
  have : ((160 * qe : ℕ) : ℤ) * (lK t k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam1_spec (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hs : sK t k = s0) (hl : lK t k = ℓ0) :
    ev (lam1 hqe ey cy t k) ex0 cx0 = mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h160 hqe) := by
  unfold lam1
  rw [lamX_spec (h160 hqe) (lK t k) (by norm_num : (7 : ℤ) ≠ 0) (qe * (40 * sK t k + 14) - 3 * ey)
    (zpow_ne_zero (-3) hcy) ex0 hcx (by rw [hs, hl]; unfold eBT at hB; push_cast; linarith)
    (by unfold cBT at hc; rw [mul_comm]; exact hc), hl]

/-! ## The `g`-part at a `B`-zero -/

lemma pole_unique {s0 ℓ0 t k t1 k1 : ℤ} (ht : 0 ≤ t ∧ t ≤ 2) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2)
    (h1 : sK t k = s0) (h2 : lK t k = ℓ0) (h3 : sK t1 k1 = s0) (h4 : lK t1 k1 = ℓ0) : t = t1 ∧ k = k1 := by
  have a := lK_spec t k; have b := lK_spec t1 k1
  rw [h1, h2] at a; rw [h3, h4] at b
  omega

variable {t1 k1 : ℤ}

/-- the value of the pole term. -/
noncomputable def Vb (t1 k1 ℓ0 s0 ex0 : ℤ) (cx0 : ℂ) : L :=
  θ (h3qe hqe) (7 * qe * t1 + ex0) cx0 *
    ((idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
      ((idx4.erase s0).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) *
    (sig1 (qe := qe) ey cy t1 k1 * (mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h160 hqe)))

lemma term1_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hs0 : s0 ∈ idx4) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = s0) (h4 : lK t1 k1 = ℓ0)
    (t k : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) :
    ev (term1 hqe ey cy t k) ex0 cx0 = if t = t1 ∧ k = k1 then Vb hqe ey cy t1 k1 ℓ0 s0 ex0 cx0 else 0 := by
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t _) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hs : sK t k = s0
  · by_cases hl : lK t k = ℓ0
    · obtain ⟨rfl, rfl⟩ := pole_unique ht ht1 hs hl h3 h4
      rw [if_pos ⟨rfl, rfl⟩, Fix1_ev hqe ey cy _ _ ex0 hcx, lam1_spec hqe ey cy hB hc hcx hcy _ _ hs hl, hs, Vb]
    · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hl h4
      rw [if_neg hne, lam1_zero hqe ey cy hB hc hcx hcy t k hs hl, mul_zero, mul_zero]
  · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hs h3
    rw [if_neg hne, Fix1_zero hqe ey cy hs0 hB hc hcx t _ hs, zero_mul]

lemma PG1_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hs0 : s0 ∈ idx4) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = s0) (h4 : lK t1 k1 = ℓ0)
    (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) :
    ev (PG1 hqe ey cy t) ex0 cx0 = if t = t1 then Vb hqe ey cy t1 k1 ℓ0 s0 ex0 cx0 else 0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy ht.1 ht.2)]
  by_cases htt : t = t1
  · rw [if_pos htt, hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term1_B hqe ey cy hB hc hcx hcy hs0 ht1 h3 h4 t k ht, if_neg (fun h => hk h.2)]),
      evColFam_apply, term1_B hqe ey cy hB hc hcx hcy hs0 ht1 h3 h4 t k1 ht, if_pos ⟨htt, rfl⟩]
  · rw [if_neg htt]
    exact hs_zero_of fun k => by
      rw [evColFam_apply, term1_B hqe ey cy hB hc hcx hcy hs0 ht1 h3 h4 t k ht, if_neg (fun h => htt h.1)]

lemma PG2_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hs0 : s0 ∈ idx4) (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 2) : ev (PG2 hqe ey cy t) ex0 cx0 = 0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy ht.1 ht.2)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h160 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t _) (hL.smul _) ex0 hcx, Fix2_zero hqe ey cy hs0 hB hc hcx, zero_mul]

lemma GS_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hs0 : s0 ∈ idx4) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = s0) (h4 : lK t1 k1 = ℓ0) :
    ev (GS hqe ey cy) ex0 cx0 = Vb hqe ey cy t1 k1 ℓ0 s0 ex0 cx0 := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have a2 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have b2 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  unfold GS
  rw [ev_add ((a0.add a1).add a2) ((b0.add b1).add b2), ev_add (a0.add a1) a2, ev_add a0 a1,
    ev_add (b0.add b1) b2, ev_add b0 b1]
  have p := fun t (ht : 0 ≤ t ∧ t ≤ 2) => PG1_B hqe ey cy hB hc hcx hcy hs0 ht1 h3 h4 t ht
  have p' := fun t (ht : 0 ≤ t ∧ t ≤ 2) => PG2_B hqe ey cy hB hc hcx hs0 t ht
  rw [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p' 0 (by norm_num), p' 1 (by norm_num),
    p' 2 (by norm_num)]
  rcases (by omega : t1 = 0 ∨ t1 = 1 ∨ t1 = 2) with rfl | rfl | rfl <;> simp

/-! ## The θ-part at a `B`-zero -/

lemma TT_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hs0 : s0 ∈ idx4) :
    ev (TT (qe := qe) ey cy) ex0 cx0 = ∑ r ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r s0 ex0 cx0 *
      (((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx4.erase s0).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) := by
  unfold TT
  rw [ev_sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 3, TS (qe := qe) ey cy r s k) _
    (fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ev_sum (F := fun s k => TS (qe := qe) ey cy r s k) _ (fun s _ => TS_ent hqe ey cy r s)]
  have hs0' : s0 ∈ Finset.Icc (0 : ℤ) 3 := by
    simp only [idx4, List.mem_cons, List.not_mem_nil, or_false] at hs0
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_eq_single s0 (fun s _ hs => TS_zero hqe ey cy hs0 hB hc hcx r s hs) (fun h => absurd hs0' h),
    TS_ev' hqe ey cy r s0 ex0 hcx]

/-- the bracket whose vanishing is the residue identity at a `B`-zero. -/
noncomputable def brB (t1 k1 ℓ0 s0 ex0 : ℤ) (cx0 : ℂ) : L :=
  sig1 (qe := qe) ey cy t1 k1 * mono (-(((160 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
      θ (h3qe hqe) (7 * qe * t1 + ex0) cx0 *
      (idx4.map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod +
    ∑ r ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r s0 ex0 cx0 *
      ((idx4.erase r).map fun r => θ (h160 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod

/-- **`F` at a `B`-zero**. -/
theorem FS_ev_B (hB : eBT (qe := qe) ey s0 ex0 = 160 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hs0 : s0 ∈ idx4) (ht1 : 0 ≤ t1 ∧ t1 ≤ 2) (h3 : sK t1 k1 = s0) (h4 : lK t1 k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h160 hqe) *
      ((idx4.erase s0).map fun s => θ (h160 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod *
        brB hqe ey cy t1 k1 ℓ0 s0 ex0 cx0) := by
  unfold FS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)) ((TT_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) (GS_ent hqe ey cy),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_zero hqe ey cy hs0 hB hc hcx,
    ev_smul (TT_ent hqe ey cy), GS_B hqe ey cy hB hc hcx hcy hs0 ht1 h3 h4, TT_B hqe ey cy hB hc hcx hs0,
    Vb, brB, sum_rearr]
  ring

end EvB

end MTC
