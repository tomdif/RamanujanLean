/-
# The entire function `F = P · (J̄ f − J̄ g − J_{160}³ θ-sum)` lies in `Th(55)`

* `Pv_FE` — `P(q^{40} x) = q^{−1136} y^{42} x^{−58} P(x)` (4 + 4 theta factors, permuted with shifts);
* `Dv_FE` — the difference `D = J̄ f − gNum − κ θV` satisfies `D(q^{40}x) = q^{66} y^{−7} x³ D(x)`;
* `FS_ev` — the series `FS` has values `P · D` at good points;
* `FS_mem_Th` — `FS ∈ Th (40 qe) 55 (q^{−1070} y^{35})` when `|y| = 1`.
-/
import RamanujanTau.MTC.PG373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-- the multiplier of `θ_qshift`. -/
noncomputable def Msh (N : ℕ) (e' s : ℤ) (c : ℂ) : L := mono (-(N * c2 (s + 1)) - e' * s + N * s) ((-1) ^ s * c ^ (-s))

lemma θ_sh {N : ℕ} (hN : 1 ≤ N) {e e' : ℤ} {c : ℂ} (hc : c ≠ 0) (s : ℤ) (h : e = e' + N * s) :
    θ hN e c = Msh N e' s c * θ hN e' c := by
  rw [h, θ_qshift hN e' hc s, Msh]

section FCore
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma cAT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cAT cy cx ≠ 0 := by
  unfold cAT; exact mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx)

lemma cBT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cBT cy cx ≠ 0 := by
  unfold cBT; exact mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)

/-- **the functional equation of `P`**. -/
theorem Pv_FE (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    Pv hqe ey cy (ex + 40 * qe) cx =
      mono (-(1136 * qe) + 42 * ey - 58 * ex) (cy ^ (42 : ℤ) * cx ^ (-58 : ℤ)) * Pv hqe ey cy ex cx := by
  have hA := cAT_ne cy hcx hcy
  have hB := cBT_ne cy hcx hcy
  simp only [Pv, idx4, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  have hN : ((160 * qe : ℕ) : ℤ) = 160 * qe := by push_cast; ring
  rw [θ_sh (h160 hqe) hA (-1) (e := eAT (qe := qe) ey 0 (ex + 40 * qe)) (e' := eAT (qe := qe) ey 1 ex)
      (by unfold eAT; push_cast; ring),
    θ_sh (h160 hqe) hA (-1) (e := eAT (qe := qe) ey 1 (ex + 40 * qe)) (e' := eAT (qe := qe) ey 2 ex)
      (by unfold eAT; push_cast; ring),
    θ_sh (h160 hqe) hA (-1) (e := eAT (qe := qe) ey 2 (ex + 40 * qe)) (e' := eAT (qe := qe) ey 3 ex)
      (by unfold eAT; push_cast; ring),
    show eAT (qe := qe) ey 3 (ex + 40 * qe) = eAT (qe := qe) ey 0 ex by unfold eAT; ring,
    θ_sh (h160 hqe) hB 1 (e := eBT (qe := qe) ey 0 (ex + 40 * qe)) (e' := eBT (qe := qe) ey 3 ex)
      (by unfold eBT; push_cast; ring),
    θ_sh (h160 hqe) hB 2 (e := eBT (qe := qe) ey 1 (ex + 40 * qe)) (e' := eBT (qe := qe) ey 0 ex)
      (by unfold eBT; push_cast; ring),
    θ_sh (h160 hqe) hB 2 (e := eBT (qe := qe) ey 2 (ex + 40 * qe)) (e' := eBT (qe := qe) ey 1 ex)
      (by unfold eBT; push_cast; ring),
    θ_sh (h160 hqe) hB 2 (e := eBT (qe := qe) ey 3 (ex + 40 * qe)) (e' := eBT (qe := qe) ey 2 ex)
      (by unfold eBT; push_cast; ring)]
  have hM : Msh (160 * qe) (eAT (qe := qe) ey 1 ex) (-1) (cAT cy cx) * Msh (160 * qe) (eAT (qe := qe) ey 2 ex) (-1) (cAT cy cx) *
      Msh (160 * qe) (eAT (qe := qe) ey 3 ex) (-1) (cAT cy cx) * Msh (160 * qe) (eBT (qe := qe) ey 3 ex) 1 (cBT cy cx) *
      Msh (160 * qe) (eBT (qe := qe) ey 0 ex) 2 (cBT cy cx) * Msh (160 * qe) (eBT (qe := qe) ey 1 ex) 2 (cBT cy cx) *
      Msh (160 * qe) (eBT (qe := qe) ey 2 ex) 2 (cBT cy cx) =
      mono (-(1136 * qe) + 42 * ey - 58 * ex) (cy ^ (42 : ℤ) * cx ^ (-58 : ℤ)) := by
    simp only [Msh, mono_mul]
    apply mono_ext
    · push_cast
      simp only [show (-1 : ℤ) + 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num,
        show (2 : ℤ) + 1 = 3 by norm_num, show c2 0 = 0 by decide, show c2 2 = 1 by decide,
        show c2 3 = 3 by decide]
      unfold eAT eBT; ring
    · unfold cAT cBT
      simp only [neg_neg, zpow_neg, zpow_one, mul_inv, inv_inv, zpow_ofNat]
      field_simp
      try ring
  linear_combination
    (θ (h160 hqe) (eAT (qe := qe) ey 0 ex) (cAT cy cx) * θ (h160 hqe) (eAT (qe := qe) ey 1 ex) (cAT cy cx) *
      θ (h160 hqe) (eAT (qe := qe) ey 2 ex) (cAT cy cx) * θ (h160 hqe) (eAT (qe := qe) ey 3 ex) (cAT cy cx) *
      θ (h160 hqe) (eBT (qe := qe) ey 0 ex) (cBT cy cx) * θ (h160 hqe) (eBT (qe := qe) ey 1 ex) (cBT cy cx) *
      θ (h160 hqe) (eBT (qe := qe) ey 2 ex) (cBT cy cx) * θ (h160 hqe) (eBT (qe := qe) ey 3 ex) (cBT cy cx)) * hM

/-- `D = J̄ f − J̄ g − κ θV`. -/
noncomputable def Dv (ex : ℤ) (cx : ℂ) : L :=
  Jb hqe * ev (fS hqe ey cy) ex cx - gNum hqe ey cy ex cx - kap (h160 hqe) * thV hqe ey cy ex cx

/-- the coefficient conditions that make every denominator nonzero at every `x = cx t^{ex}`. -/
def CGood (cx : ℂ) : Prop :=
  cx ≠ 0 ∧ cX cy cx * (-1) ≠ 1 ∧ cY cy cx * (-1) ≠ 1 ∧ cAT cy cx ≠ 1 ∧ cBT cy cx ≠ 1

lemma CGood.okx {cx : ℂ} (h : CGood cy cx) (t ex : ℤ) : OKX (qe := qe) ey cy t ex cx := by
  intro _ h'; exact h.2.1 h'.2
lemma CGood.oky {cx : ℂ} (h : CGood cy cx) (t ex : ℤ) : OKY (qe := qe) ey cy t ex cx := by
  intro _ h'; exact h.2.2.1 h'.2

lemma CGood.td {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) (r s ex : ℤ) : Td hqe ey cy r s ex cx ≠ 0 := by
  unfold Td
  exact mul_ne_zero (θ_ne_zero (h160 hqe) (cAT_ne cy h.1 hcy) fun _ _ => h.2.2.2.1)
    (θ_ne_zero (h160 hqe) (cBT_ne cy h.1 hcy) fun _ _ => h.2.2.2.2)

/-- **the functional equation of `D`**. -/
theorem Dv_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (h : CGood cy cx) :
    Dv hqe ey cy (ex + 40 * qe) cx = muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * Dv hqe ey cy ex cx := by
  have hf := fV_FE hqe ey cy hcy ex h.1
  have hg := gNum_FE hqe ey cy hcy ex h.1 (h.okx ey cy 0 ex) (h.okx ey cy 1 ex) (h.okx ey cy 2 ex)
    (h.oky ey cy 0 ex) (h.oky ey cy 1 ex) (h.oky ey cy 2 ex)
  have ht := thV_FE hqe ey cy hcy ex h.1 (fun r s => h.td hqe ey cy hcy r s ex)
    (fun r s => h.td hqe ey cy hcy r s (ex + 40 * qe))
  unfold Dv
  linear_combination Jb hqe * hf - hg - kap (h160 hqe) * ht

/-! ## The series -/

/-- the θ-sum series `Σ_{r,s} P · Tn/Td`. -/
noncomputable def TT : ℤ → L := fun k => ∑ r ∈ Finset.Icc (0 : ℤ) 3, ∑ s ∈ Finset.Icc (0 : ℤ) 3, TS (qe := qe) ey cy r s k

include hqe in
lemma TT_ent : Ent (TT (qe := qe) ey cy) :=
  Ent.sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 3, TS (qe := qe) ey cy r s k) _
    fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s

lemma mem_idx4 {r : ℤ} (hr : r ∈ Finset.Icc (0 : ℤ) 3) : r ∈ idx4 := by
  simp only [Finset.mem_Icc] at hr
  simp only [idx4, List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma TT_ev (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hd : ∀ r s, Td hqe ey cy r s ex cx ≠ 0) :
    ev (TT (qe := qe) ey cy) ex cx = Pv hqe ey cy ex cx * thV hqe ey cy ex cx := by
  unfold TT thV
  rw [ev_sum (F := fun r k => ∑ s ∈ Finset.Icc (0 : ℤ) 3, TS (qe := qe) ey cy r s k) _
    (fun r _ => Ent.sum (F := fun s k => TS (qe := qe) ey cy r s k) _ fun s _ => TS_ent hqe ey cy r s), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [ev_sum (F := fun s k => TS (qe := qe) ey cy r s k) _ (fun s _ => TS_ent hqe ey cy r s), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  exact TS_ev hqe ey cy (mem_idx4 hr) (mem_idx4 hs) ex hcx (hd r s)

/-- the `g`-part series. -/
noncomputable def GS : ℤ → L :=
  PG1 hqe ey cy 0 + PG1 hqe ey cy 1 + PG1 hqe ey cy 2 + (PG2 hqe ey cy 0 + PG2 hqe ey cy 1 + PG2 hqe ey cy 2)

lemma PG1_ent {t : ℤ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : Ent (PG1 hqe ey cy t) := Ent.sumS (term1_udec hqe ey cy h0 h2)
lemma PG2_ent {t : ℤ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : Ent (PG2 hqe ey cy t) := Ent.sumS (term2_udec hqe ey cy h0 h2)

lemma GS_ent : Ent (GS hqe ey cy) :=
  (((PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)).add (PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num))).add
    (PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl)).add
  (((PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)).add (PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num))).add
    (PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl))

lemma GS_ev (ex : ℤ) {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) :
    ev (GS hqe ey cy) ex cx = Pv hqe ey cy ex cx * gNum hqe ey cy ex cx := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have a2 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 2)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) (by norm_num)
  have b2 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 2) le_rfl
  unfold GS
  rw [ev_add ((a0.add a1).add a2) ((b0.add b1).add b2), ev_add (a0.add a1) a2, ev_add a0 a1,
    ev_add (b0.add b1) b2, ev_add b0 b1]
  have p := fun t (h0 : (0 : ℤ) ≤ t) (h2 : t ≤ 2) => PG1_ev hqe ey cy h0 h2 ex h.1 hcy (h.okx ey cy t ex)
  have p' := fun t (h0 : (0 : ℤ) ≤ t) (h2 : t ≤ 2) => PG2_ev hqe ey cy h0 h2 ex h.1 hcy (h.oky ey cy t ex)
  rw [p 0 le_rfl (by norm_num), p 1 (by norm_num) (by norm_num), p 2 (by norm_num) le_rfl,
    p' 0 le_rfl (by norm_num), p' 1 (by norm_num) (by norm_num), p' 2 (by norm_num) le_rfl, gNum]
  ring

/-- **the auxiliary entire series** `F = P · J̄ f − P · J̄ g − κ P θV`. -/
noncomputable def FS : ℤ → L :=
  MTC.conv (PS (qe := qe) ey cy) (fun n => Jb hqe * fS hqe ey cy n) - GS hqe ey cy -
    fun n => kap (h160 hqe) * TT (qe := qe) ey cy n

lemma FS_ent : Ent (FS hqe ey cy) :=
  (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)).sub ((TT_ent hqe ey cy).smul _)

theorem FS_ev (ex : ℤ) {cx : ℂ} (hcy : cy ≠ 0) (h : CGood cy cx) :
    ev (FS hqe ey cy) ex cx = Pv hqe ey cy ex cx * Dv hqe ey cy ex cx := by
  unfold FS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)) ((TT_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) (GS_ent hqe ey cy),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex h.1, ev_smul (fS_ent hqe ey cy),
    ev_smul (TT_ent hqe ey cy), PS_ev hqe ey cy ex h.1, GS_ev hqe ey cy ex hcy h,
    TT_ev hqe ey cy ex h.1 (fun r s => h.td hqe ey cy hcy r s ex), Dv]
  ring

/-- the multiplier of `F`. -/
noncomputable def muF : L := mono (-(1070 * qe) + 35 * ey) (cy ^ (35 : ℤ))

theorem FS_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (h : CGood cy cx) :
    ev (FS hqe ey cy) (ex + 40 * qe) cx =
      muF (qe := qe) ey cy * mono (-(ex * 55)) (cx ^ (-(55 : ℤ))) * ev (FS hqe ey cy) ex cx := by
  rw [FS_ev hqe ey cy _ hcy h, FS_ev hqe ey cy _ hcy h, Pv_FE hqe ey cy ex h.1 hcy, Dv_FE hqe ey cy hcy ex h]
  have hm : mono (-(1136 * qe) + 42 * ey - 58 * ex) (cy ^ (42 : ℤ) * cx ^ (-58 : ℤ)) *
      (muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ))) =
      muF (qe := qe) ey cy * mono (-(ex * 55)) (cx ^ (-(55 : ℤ))) := by
    unfold muD muF
    simp only [mono_mul]
    apply mono_ext
    · ring
    · have := h.1
      simp only [zpow_neg, zpow_ofNat]
      field_simp
      try ring
  linear_combination (Pv hqe ey cy ex cx * Dv hqe ey cy ex cx) * hm

/-! ## Membership in `Th(55)` -/

lemma ne_one_of_norm {a : ℂ} (h : ‖a‖ ≠ 1) : a ≠ 1 := fun h1 => h (by rw [h1, norm_one])

/-- the real points `n + 2` are good when `|y| = 1`. -/
lemma cgood_nat (hcy : ‖cy‖ = 1) (n : ℕ) : CGood cy ((n : ℂ) + 2) := by
  have hx : ‖((n : ℂ) + 2)‖ = (n : ℝ) + 2 := by
    rw [show ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have h1 : (1 : ℝ) < (n : ℝ) + 2 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hneg : ∀ k : ℤ, k < 0 → ((n : ℝ) + 2) ^ k ≠ 1 := fun k hk => (zpow_lt_one_of_neg₀ h1 hk).ne
  have hpos : ∀ k : ℤ, 0 < k → ((n : ℝ) + 2) ^ k ≠ 1 := fun k hk => (one_lt_zpow₀ h1 hk).ne'
  refine ⟨by rw [← norm_ne_zero_iff, hx]; positivity, ?_, ?_, ?_, ?_⟩
  · unfold cX; refine ne_one_of_norm ?_
    rw [norm_mul, norm_neg, norm_mul, norm_zpow, norm_zpow, hcy, hx, norm_neg, norm_one]
    simpa using hneg (-7) (by norm_num)
  · unfold cY; refine ne_one_of_norm ?_
    rw [norm_mul, norm_neg, norm_mul, norm_zpow, norm_zpow, hcy, hx, norm_neg, norm_one]
    simpa using hpos 3 (by norm_num)
  · unfold cAT; refine ne_one_of_norm ?_
    rw [norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hneg (-3) (by norm_num)
  · unfold cBT; refine ne_one_of_norm ?_
    rw [norm_mul, norm_zpow, norm_zpow, hcy, hx]
    simpa using hpos 7 (by norm_num)

/-- **`F ∈ Th(55)`**. -/
theorem FS_mem_Th (hcy : ‖cy‖ = 1) : FS hqe ey cy ∈ Th (40 * qe) 55 (muF (qe := qe) ey cy) := by
  have hcy0 : cy ≠ 0 := by rw [← norm_ne_zero_iff, hcy]; norm_num
  have hinj : Function.Injective (fun n : ℕ => (n : ℂ) + 2) := fun a b h => by
    simpa using h
  refine mem_Th_of_ev (FS_ent hqe ey cy) 0 (Set.range fun n : ℕ => (n : ℂ) + 2) (Set.infinite_range_of_injective hinj)
    (by rintro c ⟨n, rfl⟩; exact (cgood_nat cy hcy n).1) ?_
  rintro c ⟨n, rfl⟩
  have := FS_FE hqe ey cy hcy0 0 (cgood_nat cy hcy n)
  rw [show ((55 : ℕ) : ℤ) = 55 by norm_num, show (((40 * qe : ℕ) : ℤ)) = 40 * qe by push_cast; ring]
  exact this

end FCore

end MTC
