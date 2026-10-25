/-
# Values of `F` at the zeros of `P`, and the residue identities there (`f_{1,4,1}`)

The `n = 1, p = 3` analogue of `EvB373`, `ResB373`, `EvA373`.

* `FS_ev_B` — at `x₀` with `B_{s₀}(x₀) = Q^{ℓ₀}` only the pole term `k₁ = 3ℓ₀ − s₀` of `P · G1` and the
  `s = s₀` column of `P · θ` survive; `brB_zero` — the bracket vanishes by the `q → q⁹` dissection of
  `j(x₀; q)` over `ρ = c₀ − r`, modulo three monomial identities.
* `FS_ev_A`, `brA_zero` — the same at a zero of `j(A_{r₀})`, with the dissection of `j(y; q)`.
-/
import RamanujanTau.MTC.FCore141
import RamanujanTau.MTC.EvA373

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

section EvB
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma Fix1_ev (s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix1 (qe := qe) ey cy s) ex cx = θ hqe ex cx *
      ((idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [Fix1, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent hqe one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    thX_ev hqe one_ne_zero, one_mul, zpow_one, zero_add]
  have hA' : (idx3.map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      (idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx3.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']

lemma TS_ev' (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (TS (qe := qe) ey cy r s) ex cx = Tn hqe ey cy r s ex cx *
      (((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [TS, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact TnS_ent hqe ey cy r s
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append,
    TnS_ev hqe ey cy r s ex hcx]
  have hA' : ((idx3.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : ((idx3.erase s).map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']

variable {s0 ℓ0 ex0 : ℤ} {cx0 : ℂ}

include hqe in
lemma BS0_ev (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) :
    ev (BS (qe := qe) ey cy s0) ex0 cx0 = 0 := by
  rw [BS_ev hqe, hB, hc, show (45 * qe * ℓ0 : ℤ) = ((45 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h45 hqe) ℓ0

include hqe in
lemma Fix1_zero (hs0 : s0 ∈ idx3) (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (s : ℤ) (hs : s ≠ s0) : ev (Fix1 (qe := qe) ey cy s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent hqe one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨s0, (List.mem_erase_of_ne (Ne.symm hs)).mpr hs0, rfl⟩))) ex0 hcx
    (BS0_ev hqe ey cy hB hc)

lemma Fix2_zero (hs0 : s0 ∈ idx3) (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (r : ℤ) : ev (Fix2 hqe ey cy r) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩))) ex0 hcx
    (BS0_ev hqe ey cy hB hc)

include hqe in
lemma TS_zero (hs0 : s0 ∈ idx3) (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1)
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
lemma PS_zero (hs0 : s0 ∈ idx3) (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1)
    (hcx : cx0 ≠ 0) : ev (PS (qe := qe) ey cy) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_append, List.mem_map] at hF
    rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s)
    (List.mem_append_right _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩)) ex0 hcx (BS0_ev hqe ey cy hB hc)

lemma lam1_rel0 (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = s0) :
    (1 - mono (((45 * qe : ℕ) : ℤ) * lK k - ((45 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) *
      ev (lam1 hqe ey cy k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h45 hqe) (lK k) (by norm_num : (4 : ℤ) ≠ 0) (qe * (15 * sK k + 6) - ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-1) hcy)) ex0 hcx
  have he : qe * (15 * sK k + 6) - ey + 4 * ex0 = ((45 * qe : ℕ) : ℤ) * ℓ0 := by
    rw [hs]; unfold eBT at hB; push_cast; linarith
  have hcc : -(cy ^ (-1 : ℤ)) * cx0 ^ (4 : ℤ) = 1 := by unfold cBT at hc; rw [← hc]; ring
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam1_zero (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = s0) (hl : lK k ≠ ℓ0) : ev (lam1 hqe ey cy k) ex0 cx0 = 0 := by
  have h := lam1_rel0 hqe ey cy hB hc hcx hcy k hs
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((45 * qe : ℕ) : ℤ) := by have := h45 hqe; omega
  have : ((45 * qe : ℕ) : ℤ) * (lK k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam1_spec (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = s0) (hl : lK k = ℓ0) :
    ev (lam1 hqe ey cy k) ex0 cx0 = mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h45 hqe) := by
  unfold lam1
  rw [lamX_spec (h45 hqe) (lK k) (by norm_num : (4 : ℤ) ≠ 0) (qe * (15 * sK k + 6) - ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-1) hcy)) ex0 hcx (by rw [hs, hl]; unfold eBT at hB; push_cast; linarith)
    (by unfold cBT at hc; rw [← hc]; ring), hl]

lemma pole_unique {s0 ℓ0 k k1 : ℤ} (h1 : sK k = s0) (h2 : lK k = ℓ0) (h3 : sK k1 = s0) (h4 : lK k1 = ℓ0) :
    k = k1 := by
  have a := lK_spec k; have b := lK_spec k1
  rw [h1, h2] at a; rw [h3, h4] at b
  omega

variable {k1 : ℤ}

/-- the value of the pole term. -/
noncomputable def Vb (k1 ℓ0 s0 ex0 : ℤ) (cx0 : ℂ) : L :=
  θ hqe ex0 cx0 *
    ((idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
      ((idx3.erase s0).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) *
    (sig1 (qe := qe) k1 * (mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h45 hqe)))

lemma term1_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hs0 : s0 ∈ idx3) (h3 : sK k1 = s0) (h4 : lK k1 = ℓ0) (k : ℤ) :
    ev (term1 hqe ey cy k) ex0 cx0 = if k = k1 then Vb hqe ey cy k1 ℓ0 s0 ex0 cx0 else 0 := by
  have hL : Ent (lam1 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy _) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hs : sK k = s0
  · by_cases hl : lK k = ℓ0
    · obtain rfl := pole_unique hs hl h3 h4
      rw [if_pos rfl, Fix1_ev hqe ey cy _ ex0 hcx, lam1_spec hqe ey cy hB hc hcx hcy _ hs hl, hs, Vb]
    · have hne : ¬(k = k1) := by rintro rfl; exact hl h4
      rw [if_neg hne, lam1_zero hqe ey cy hB hc hcx hcy k hs hl, mul_zero, mul_zero]
  · have hne : ¬(k = k1) := by rintro rfl; exact hs h3
    rw [if_neg hne, Fix1_zero hqe ey cy hs0 hB hc hcx _ hs, zero_mul]

lemma PG1_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (hs0 : s0 ∈ idx3) (h3 : sK k1 = s0) (h4 : lK k1 = ℓ0) :
    ev (PG1 hqe ey cy) ex0 cx0 = Vb hqe ey cy k1 ℓ0 s0 ex0 cx0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy), hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term1_B hqe ey cy hB hc hcx hcy hs0 h3 h4 k, if_neg hk]),
    evColFam_apply, term1_B hqe ey cy hB hc hcx hcy hs0 h3 h4 k1, if_pos rfl]

lemma PG2_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hs0 : s0 ∈ idx3) : ev (PG2 hqe ey cy) ex0 cx0 = 0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam2 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy _) (hL.smul _) ex0 hcx, Fix2_zero hqe ey cy hs0 hB hc hcx, zero_mul]

lemma TT_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hs0 : s0 ∈ idx3) :
    ev (TT (qe := qe) ey cy) ex0 cx0 = ∑ r ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r s0 ex0 cx0 *
      (((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx3.erase s0).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) := by
  unfold TT
  rw [ev_sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 2, TS (qe := qe) ey cy r s k) _
    (fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ev_sum (F := fun s k => TS (qe := qe) ey cy r s k) _ (fun s _ => TS_ent hqe ey cy r s)]
  have hs0' : s0 ∈ Finset.Icc (0 : ℤ) 2 := by
    simp only [idx3, List.mem_cons, List.not_mem_nil, or_false] at hs0
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_eq_single s0 (fun s _ hs => TS_zero hqe ey cy hs0 hB hc hcx r s hs) (fun h => absurd hs0' h),
    TS_ev' hqe ey cy r s0 ex0 hcx]

/-- the bracket whose vanishing is the residue identity at a `B`-zero. -/
noncomputable def brB (k1 ℓ0 s0 ex0 : ℤ) (cx0 : ℂ) : L :=
  sig1 (qe := qe) k1 * mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * θ hqe ex0 cx0 *
      (idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod +
    ∑ r ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r s0 ex0 cx0 *
      ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod

/-- **`F` at a `B`-zero**. -/
theorem FS_ev_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hs0 : s0 ∈ idx3) (h3 : sK k1 = s0) (h4 : lK k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h45 hqe) *
      ((idx3.erase s0).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod *
        brB hqe ey cy k1 ℓ0 s0 ex0 cx0) := by
  unfold FS GS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub
      ((PG1_ent hqe ey cy).add (PG2_ent hqe ey cy))) ((TT_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) ((PG1_ent hqe ey cy).add (PG2_ent hqe ey cy)),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_zero hqe ey cy hs0 hB hc hcx,
    ev_add (PG1_ent hqe ey cy) (PG2_ent hqe ey cy), PG1_B hqe ey cy hB hc hcx hcy hs0 h3 h4,
    PG2_B hqe ey cy hB hc hcx hs0,
    ev_smul (TT_ent hqe ey cy), TT_B hqe ey cy hB hc hcx hs0, Vb, brB, sum_rearr]
  ring

end EvB

/-! ## The `q → q⁹` dissection -/

lemma Icc02 : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

lemma sum_Icc02 (f : ℤ → L) : ∑ r ∈ Finset.Icc (0 : ℤ) 2, f r = f 0 + f 1 + f 2 := by
  rw [Icc02, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

section Dis
variable {qe : ℕ} (hqe : 1 ≤ qe)

/-- the multiplier of the `ρ`-th summand of the `q → q⁹` dissection. -/
noncomputable def dmon (e : ℤ) (c : ℂ) (ρ : ℤ) : L := mono (qe * c2 (-ρ) - e * ρ) ((-1) ^ (-ρ) * c ^ (-ρ))

/-- the `ρ`-th summand. -/
noncomputable def summ (e : ℤ) (c : ℂ) (ρ : ℤ) : L :=
  dmon (qe := qe) e c ρ * θ (h9 hqe) (3 * qe - 3 * qe * ρ + 3 * e) (c ^ 3)

lemma c2_neg_add3 (ρ : ℤ) : c2 (-(ρ + 3)) = c2 (-ρ) + 3 * ρ + 6 := by
  rw [show -(ρ + 3) = -ρ + (-3) by ring, c2_add]; norm_num [c2]; ring

lemma summ_period (e : ℤ) {c : ℂ} (hc : c ≠ 0) (ρ : ℤ) : summ hqe e c (ρ + 3) = summ hqe e c ρ := by
  unfold summ dmon
  have hC : c ^ 3 ≠ 0 := pow_ne_zero _ hc
  rw [show 3 * (qe : ℤ) - 3 * qe * (ρ + 3) + 3 * e = (3 * qe - 3 * qe * ρ + 3 * e) + ((9 * qe : ℕ) : ℤ) * (-1) by
      push_cast; ring,
    θ_qshift (h9 hqe) _ hC (-1), ← mul_assoc]
  congr 1
  rw [mono_mul]
  apply mono_ext
  · rw [c2_neg_add3, show (-1 : ℤ) + 1 = 0 by norm_num, show c2 0 = 0 by decide]
    push_cast; ring
  · have e1 : -(ρ + 3) = -ρ + (-3) := by ring
    rw [e1, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hc]
    have h3 : c ^ (-3 : ℤ) * c ^ 3 = 1 := by
      rw [zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero _ hc)]
    have hm : ((-1 : ℂ)) ^ (-3 : ℤ) = -1 := by norm_num
    have hm1 : ((-1 : ℂ)) ^ (-1 : ℤ) = -1 := by norm_num
    rw [hm, hm1, neg_neg, zpow_one]
    linear_combination ((-1) ^ (-ρ) * c ^ (-ρ)) * h3

/-- HM (1.2f) with `m = 3` in base `q`. -/
lemma dissect3 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hqe e c = ∑ r ∈ Finset.Icc (0 : ℤ) 2, summ hqe e c (2 - r) := by
  rw [show ∑ r ∈ Finset.Icc (0 : ℤ) 2, summ hqe e c (2 - r) = ∑ ρ : Fin 3, summ hqe e c ((ρ : ℕ) : ℤ) by
    rw [sum_Icc02, Fin.sum_univ_three]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    norm_num
    ring]
  rw [θ_dissect hqe 3 (by norm_num) e hc]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold summ dmon
  refine congrArg₂ (· * ·) (mono_ext (by push_cast; ring) rfl) ?_
  rw [θ_N (show qe * 3 * 3 = 9 * qe by ring) _ (h9 hqe)]
  exact θ_cg (h9 hqe) (by push_cast; rw [show c2 3 = 3 by decide]; ring) (by norm_num)

/-- the dissection over any three consecutive indices. -/
lemma dissect_any (e : ℤ) {c : ℂ} (hc : c ≠ 0) (c0 : ℤ) :
    θ hqe e c = ∑ r ∈ Finset.Icc (0 : ℤ) 2, summ hqe e c (c0 - r) := by
  have step : ∀ k : ℤ, ∑ r ∈ Finset.Icc (0 : ℤ) 2, summ hqe e c (k + 1 - r) =
      ∑ r ∈ Finset.Icc (0 : ℤ) 2, summ hqe e c (k - r) := by
    intro k
    rw [sum_Icc02, sum_Icc02, show k + 1 - 0 = (k - 2) + 3 by ring, summ_period hqe e hc,
      show k + 1 - 1 = k - 0 by ring, show k + 1 - 2 = k - 1 by ring]
    ring
  induction c0 using Int.inductionOn' (b := 2) with
  | zero => exact dissect3 hqe e hc
  | succ k _ ih => rw [step k]; exact ih
  | pred k _ ih =>
      have h := step (k - 1)
      simp only [sub_add_cancel] at h
      rw [← h]; exact ih

end Dis

/-- the algebra of the termwise cancellation. -/
lemma alg3 (S P : L) (d m M T A A' : ℤ → L)
    (hm : ∀ r ∈ Finset.Icc (0 : ℤ) 2, S * d r + m r * M r = 0)
    (hp : ∀ r ∈ Finset.Icc (0 : ℤ) 2, A r * A' r = P) :
    S * (∑ r ∈ Finset.Icc (0 : ℤ) 2, d r * T r) * P +
      ∑ r ∈ Finset.Icc (0 : ℤ) 2, m r * T r * (M r * A r) * A' r = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  linear_combination (T r * P) * hm r hr + (m r * T r * M r) * hp r hr

section ResB
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)
variable {s0 ℓ0 ex0 k1 : ℤ} {cx0 : ℂ}

/-- the `q⁹`-theta function of `Tn(r, s₀)` is the dissection summand at `ρ = c₀ − r`. -/
lemma θ9_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (r : ℤ) :
    θ (h9 hqe) (e1T (qe := qe) ey r s0 ex0) (c1T cy cx0) =
      θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * s0 - 4 - r) + 3 * ex0) (cx0 ^ 3) := by
  rw [← θ_reflect (h9 hqe) _ (c1T_ne cy hcx hcy)]
  congr 1
  · unfold e1T; unfold eBT at hB; push_cast
    first | linear_combination hB | linear_combination -hB
  · unfold c1T; unfold cBT at hc
    have hx4 : cx0 ^ (4 : ℤ) ≠ 0 := zpow_ne_zero _ hcx
    have h' : cx0 ^ (4 : ℤ) * cy ^ (-1 : ℤ) = -1 := by linear_combination -hc
    have hcy1 : cy ^ (-1 : ℤ) = -(cx0 ^ (4 : ℤ))⁻¹ := by
      rw [show cy ^ (-1 : ℤ) = (cx0 ^ (4 : ℤ))⁻¹ * (cx0 ^ (4 : ℤ) * cy ^ (-1 : ℤ)) by field_simp, h']; ring
    rw [hcy1]
    simp only [zpow_ofNat]
    field_simp
    try ring

/-- the `q^{45}`-theta function of `Tn(r, s₀)` is `j(A_r)` up to a monomial. -/
lemma θ45_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (r : ℤ) :
    θ (h45 hqe) (e2T (qe := qe) ey r s0 ex0) (c2T cy cx0) =
      Msh (45 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) * θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0) := by
  have hcc : c2T cy cx0 = cAT cy cx0 := by
    unfold cBT at hc
    unfold c2T cAT
    rw [show cx0 ^ (3 : ℤ) * cy ^ (3 : ℤ) = (-(cy ^ (4 : ℤ) * cx0 ^ (-1 : ℤ))) * (-(cx0 ^ (4 : ℤ) * cy ^ (-1 : ℤ))) by
      simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
  rw [hcc]
  exact θ_sh (h45 hqe) (cAT_ne cy hcx hcy) ℓ0 (by
    unfold e2T eAT; unfold eBT at hB; push_cast
    first | linear_combination hB | linear_combination -hB)

lemma Tn_B (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (r : ℤ) :
    Tn hqe ey cy r s0 ex0 cx0 = mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0) *
      θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * s0 - 4 - r) + 3 * ex0) (cx0 ^ 3) *
      (Msh (45 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) * θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)) := by
  unfold Tn
  rw [θ9_B hqe ey cy hB hc hcx hcy r, θ45_B hqe ey cy hB hc hcx hcy r]

/-- **the residue identity at a `B`-zero**, modulo three monomial identities. -/
theorem brB_zero (hB : eBT (qe := qe) ey s0 ex0 = 45 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0)
    (hm : ∀ r ∈ Finset.Icc (0 : ℤ) 2,
      sig1 (qe := qe) k1 * mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
          dmon (qe := qe) ex0 cx0 (15 * ℓ0 - 4 * s0 - 4 - r) +
        mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0) * Msh (45 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0) = 0) :
    brB hqe ey cy k1 ℓ0 s0 ex0 cx0 = 0 := by
  unfold brB
  rw [dissect_any hqe ex0 hcx (15 * ℓ0 - 4 * s0 - 4)]
  simp only [Tn_B hqe ey cy hB hc hcx hcy, summ]
  exact alg3 (sig1 (qe := qe) k1 * mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)))
    ((idx3.map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod)
    (fun r => dmon (qe := qe) ex0 cx0 (15 * ℓ0 - 4 * s0 - 4 - r))
    (fun r => mono (eTn (qe := qe) ey r s0 ex0) (cTn cy r s0 cx0))
    (fun r => Msh (45 * qe) (eAT (qe := qe) ey r ex0) ℓ0 (cAT cy cx0))
    (fun r => θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * s0 - 4 - r) + 3 * ex0) (cx0 ^ 3))
    (fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0))
    (fun r => ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod)
    hm (fun r hr => List.prod_map_erase (fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)) (mem_idx3 hr))

end ResB

section EvA
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma Fix2_ev (r ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    ev (Fix2 hqe ey cy r) ex cx = θ hqe ey cy *
      (((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod *
        (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod) := by
  rw [Fix2, ev_cprodL _ (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r', _, rfl⟩ | ⟨s', _, rfl⟩
    · exact ent_monoS _ _
    · exact AS_ent hqe ey cy r'
    · exact BS_ent hqe ey cy s') ex hcx]
  simp only [List.map_cons, List.prod_cons, List.map_append, List.map_map, List.prod_append, ev_monoS]
  have hA' : ((idx3.erase r).map ((fun F => ev F ex cx) ∘ AS (qe := qe) ey cy)).prod =
      ((idx3.erase r).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun r' _ => ?_; simp [Function.comp, AS_ev hqe]
  have hB' : (idx3.map ((fun F => ev F ex cx) ∘ BS (qe := qe) ey cy)).prod =
      (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)).prod := by
    congr 1; refine List.map_congr_left fun s' _ => ?_; simp [Function.comp, BS_ev hqe]
  rw [hA', hB']
  simp only [mul_zero, zpow_zero]
  rw [show (mono 0 (1 : ℂ) : L) = 1 from rfl, mul_one]

variable {r0 ℓ0 ex0 : ℤ} {cx0 : ℂ}

include hqe in
lemma AS0_ev (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) :
    ev (AS (qe := qe) ey cy r0) ex0 cx0 = 0 := by
  rw [AS_ev hqe, hA, hc, show (45 * qe * ℓ0 : ℤ) = ((45 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h45 hqe) ℓ0

include hqe in
lemma Fix1_zeroA (hr0 : r0 ∈ idx3) (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (s : ℤ) : ev (Fix1 (qe := qe) ey cy s) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hF
    rcases hF with rfl | ⟨r, _, rfl⟩ | ⟨s', _, rfl⟩
    · exact thX_ent hqe one_ne_zero _ _
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s')
    (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩))) ex0 hcx
    (AS0_ev hqe ey cy hA hc)

lemma Fix2_zeroA (hr0 : r0 ∈ idx3) (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) (r : ℤ) (hr : r ≠ r0) : ev (Fix2 hqe ey cy r) ex0 cx0 = 0 :=
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
lemma TS_zeroA (hr0 : r0 ∈ idx3) (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1)
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
lemma PS_zeroA (hr0 : r0 ∈ idx3) (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1)
    (hcx : cx0 ≠ 0) : ev (PS (qe := qe) ey cy) ex0 cx0 = 0 :=
  ev_cprodL_zero (fun F hF => by
    simp only [List.mem_append, List.mem_map] at hF
    rcases hF with ⟨r, _, rfl⟩ | ⟨s, _, rfl⟩
    · exact AS_ent hqe ey cy r
    · exact BS_ent hqe ey cy s)
    (List.mem_append_left _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩)) ex0 hcx (AS0_ev hqe ey cy hA hc)

lemma lam2_rel0 (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = r0) :
    (1 - mono (((45 * qe : ℕ) : ℤ) * lK k - ((45 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) *
      ev (lam2 hqe ey cy k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h45 hqe) (lK k) (by norm_num : (-1 : ℤ) ≠ 0) (qe * (15 * sK k + 6) + 4 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 4 hcy)) ex0 hcx
  have he : qe * (15 * sK k + 6) + 4 * ey + -1 * ex0 = ((45 * qe : ℕ) : ℤ) * ℓ0 := by
    rw [hs]; unfold eAT at hA; push_cast; linarith
  have hcc : -(cy ^ (4 : ℤ)) * cx0 ^ (-1 : ℤ) = 1 := by unfold cAT at hc; rw [← hc]; ring
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam2_zero (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = r0) (hl : lK k ≠ ℓ0) : ev (lam2 hqe ey cy k) ex0 cx0 = 0 := by
  have h := lam2_rel0 hqe ey cy hA hc hcx hcy k hs
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((45 * qe : ℕ) : ℤ) := by have := h45 hqe; omega
  have : ((45 * qe : ℕ) : ℤ) * (lK k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam2_spec (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (k : ℤ) (hs : sK k = r0) (hl : lK k = ℓ0) :
    ev (lam2 hqe ey cy k) ex0 cx0 = mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h45 hqe) := by
  unfold lam2
  rw [lamX_spec (h45 hqe) (lK k) (by norm_num : (-1 : ℤ) ≠ 0) (qe * (15 * sK k + 6) + 4 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 4 hcy)) ex0 hcx (by rw [hs, hl]; unfold eAT at hA; push_cast; linarith)
    (by unfold cAT at hc; rw [← hc]; ring), hl]

variable {k1 : ℤ}

/-- the value of the pole term of the second family. -/
noncomputable def Va (k1 ℓ0 r0 ex0 : ℤ) (cx0 : ℂ) : L :=
  (θ hqe ey cy *
      (((idx3.erase r0).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)) *
    (sig1 (qe := qe) k1 * (mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h45 hqe)))

lemma term2_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (h3 : sK k1 = r0) (h4 : lK k1 = ℓ0) (hr0 : r0 ∈ idx3) (k : ℤ) :
    ev (term2 hqe ey cy k) ex0 cx0 = if k = k1 then Va hqe ey cy k1 ℓ0 r0 ex0 cx0 else 0 := by
  have hL : Ent (lam2 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy _) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hs : sK k = r0
  · by_cases hl : lK k = ℓ0
    · obtain rfl := pole_unique hs hl h3 h4
      rw [if_pos rfl, Fix2_ev hqe ey cy _ ex0 hcx, lam2_spec hqe ey cy hA hc hcx hcy _ hs hl, hs, Va]
    · have hne : ¬(k = k1) := by rintro rfl; exact hl h4
      rw [if_neg hne, lam2_zero hqe ey cy hA hc hcx hcy k hs hl, mul_zero, mul_zero]
  · have hne : ¬(k = k1) := by rintro rfl; exact hs h3
    rw [if_neg hne, Fix2_zeroA hqe ey cy hr0 hA hc hcx _ hs, zero_mul]

lemma PG2_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (h3 : sK k1 = r0) (h4 : lK k1 = ℓ0) (hr0 : r0 ∈ idx3) :
    ev (PG2 hqe ey cy) ex0 cx0 = Va hqe ey cy k1 ℓ0 r0 ex0 cx0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy), hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term2_A hqe ey cy hA hc hcx hcy h3 h4 hr0 k, if_neg hk]),
    evColFam_apply, term2_A hqe ey cy hA hc hcx hcy h3 h4 hr0 k1, if_pos rfl]

lemma PG1_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hr0 : r0 ∈ idx3) : ev (PG1 hqe ey cy) ex0 cx0 = 0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam1 hqe ey cy k) := lamX_ent (h45 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy _) (hL.smul _) ex0 hcx, Fix1_zeroA hqe ey cy hr0 hA hc hcx, zero_mul]

lemma TT_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hr0 : r0 ∈ idx3) :
    ev (TT (qe := qe) ey cy) ex0 cx0 = ∑ s ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r0 s ex0 cx0 *
      (((idx3.erase r0).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) := by
  unfold TT
  rw [ev_sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 2, TS (qe := qe) ey cy r s k) _
    (fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s)]
  have hr0' : r0 ∈ Finset.Icc (0 : ℤ) 2 := by
    simp only [idx3, List.mem_cons, List.not_mem_nil, or_false] at hr0
    simp only [Finset.mem_Icc]; omega
  rw [Finset.sum_eq_single r0 (fun r _ hr => by
      rw [ev_sum (F := fun s k => TS (qe := qe) ey cy r s k) _ (fun s _ => TS_ent hqe ey cy r s)]
      exact Finset.sum_eq_zero fun s _ => TS_zeroA hqe ey cy hr0 hA hc hcx r s hr) (fun h => absurd hr0' h),
    ev_sum (F := fun s k => TS (qe := qe) ey cy r0 s k) _ (fun s _ => TS_ent hqe ey cy r0 s)]
  exact Finset.sum_congr rfl fun s _ => TS_ev' hqe ey cy r0 s ex0 hcx

/-- the scalar in front of the pole term. -/
noncomputable def SA (k1 ℓ0 : ℤ) : L :=
  sig1 (qe := qe) k1 * mono (-(((45 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1))

/-- the bracket at an `A`-zero. -/
noncomputable def brA (k1 ℓ0 r0 ex0 : ℤ) (cx0 : ℂ) : L :=
  SA (qe := qe) k1 ℓ0 * θ hqe ey cy *
      (idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod +
    ∑ s ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r0 s ex0 cx0 *
      ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod

/-- **`F` at an `A`-zero**. -/
theorem FS_ev_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0) (hr0 : r0 ∈ idx3) (h3 : sK k1 = r0) (h4 : lK k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h45 hqe) *
      ((idx3.erase r0).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        brA hqe ey cy k1 ℓ0 r0 ex0 cx0) := by
  unfold FS GS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub
      ((PG1_ent hqe ey cy).add (PG2_ent hqe ey cy))) ((TT_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) ((PG1_ent hqe ey cy).add (PG2_ent hqe ey cy)),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_zeroA hqe ey cy hr0 hA hc hcx,
    ev_add (PG1_ent hqe ey cy) (PG2_ent hqe ey cy), PG1_A hqe ey cy hA hc hcx hr0,
    PG2_A hqe ey cy hA hc hcx hcy h3 h4 hr0,
    ev_smul (TT_ent hqe ey cy), TT_A hqe ey cy hA hc hcx hr0, Va, brA, SA]
  have hsum : kap (h45 hqe) * ∑ s ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r0 s ex0 cx0 *
      (((idx3.erase r0).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod) =
      kap (h45 hqe) * ((idx3.erase r0).map fun r => θ (h45 hqe) (eAT (qe := qe) ey r ex0) (cAT cy cx0)).prod *
        ∑ s ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r0 s ex0 cx0 *
          ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum]
  ring

lemma θ9_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (s : ℤ) :
    θ (h9 hqe) (e1T (qe := qe) ey r0 s ex0) (c1T cy cx0) =
      θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * r0 - 1 - s) + 3 * ey) (cy ^ 3) := by
  congr 1
  · unfold e1T; unfold eAT at hA; push_cast
    first | linear_combination -hA | linear_combination hA
  · unfold c1T; unfold cAT at hc
    have hx : cx0 = -(cy ^ 4) := by
      have : cy ^ (4 : ℤ) * cx0 ^ (-1 : ℤ) = -1 := by linear_combination -hc
      rw [zpow_neg, zpow_one, zpow_ofNat] at this
      field_simp at this
      first | linear_combination this | linear_combination -this
    rw [hx]
    simp only [zpow_neg, zpow_ofNat]
    field_simp
    try ring

lemma θ45_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (s : ℤ) :
    θ (h45 hqe) (e2T (qe := qe) ey r0 s ex0) (c2T cy cx0) =
      Msh (45 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) * θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0) := by
  have hcc : c2T cy cx0 = cBT cy cx0 := by
    unfold cAT at hc
    unfold c2T cBT
    rw [show cx0 ^ (3 : ℤ) * cy ^ (3 : ℤ) = (-(cx0 ^ (4 : ℤ) * cy ^ (-1 : ℤ))) * (-(cy ^ (4 : ℤ) * cx0 ^ (-1 : ℤ))) by
      simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
  rw [hcc]
  exact θ_sh (h45 hqe) (cBT_ne cy hcx hcy) ℓ0 (by
    unfold e2T eBT; unfold eAT at hA; push_cast
    first | linear_combination hA | linear_combination -hA)

lemma Tn_A (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (s : ℤ) :
    Tn hqe ey cy r0 s ex0 cx0 = mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0) *
      θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * r0 - 1 - s) + 3 * ey) (cy ^ 3) *
      (Msh (45 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) * θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)) := by
  unfold Tn
  rw [θ9_A hqe ey cy hA hc hcx hcy s, θ45_A hqe ey cy hA hc hcx hcy s]

/-- **the residue identity at an `A`-zero**, modulo three monomial identities. -/
theorem brA_zero (hA : eAT (qe := qe) ey r0 ex0 = 45 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (hcy : cy ≠ 0)
    (hm : ∀ s ∈ Finset.Icc (0 : ℤ) 2,
      SA (qe := qe) k1 ℓ0 * dmon (qe := qe) ey cy (15 * ℓ0 - 4 * r0 - 1 - s) +
        mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0) * Msh (45 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0) = 0) :
    brA hqe ey cy k1 ℓ0 r0 ex0 cx0 = 0 := by
  unfold brA
  rw [dissect_any hqe ey hcy (15 * ℓ0 - 4 * r0 - 1)]
  simp only [Tn_A hqe ey cy hA hc hcx hcy, summ]
  exact alg3 (SA (qe := qe) k1 ℓ0)
    ((idx3.map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)
    (fun s => dmon (qe := qe) ey cy (15 * ℓ0 - 4 * r0 - 1 - s))
    (fun s => mono (eTn (qe := qe) ey r0 s ex0) (cTn cy r0 s cx0))
    (fun s => Msh (45 * qe) (eBT (qe := qe) ey s ex0) ℓ0 (cBT cy cx0))
    (fun s => θ (h9 hqe) (3 * qe - 3 * qe * (15 * ℓ0 - 4 * r0 - 1 - s) + 3 * ey) (cy ^ 3))
    (fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0))
    (fun s => ((idx3.erase s).map fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)).prod)
    hm (fun s hs => List.prod_map_erase (fun s => θ (h45 hqe) (eBT (qe := qe) ey s ex0) (cBT cy cx0)) (mem_idx3 hs))

end EvA

end MTC.H141
