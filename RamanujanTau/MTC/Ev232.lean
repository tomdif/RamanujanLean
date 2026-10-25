/-
# Values of `F` at the zeros of `P`, and the residue identities (`f_{2,3,2}`)

At a zero of `j(B)` (`B(x₀) = Q^{ℓ₀}`) only the pole term `(t₁, k₁)` with `ℓ₀ = 2k₁ − t₁` of `P·G1` and `Tn` survive;
at a zero of `j(A)` only the pole term of `P·G2` and `Tn`. Since `p = 1`, the `q²`-theta factor of `Tn` is directly a
monomial times `j(q^{3t₁}x₀; q²)` (resp. `j(q^{3t₁}y; q²)`), so each residue identity is one monomial identity.
-/
import RamanujanTau.MTC.FCore232
import RamanujanTau.MTC.EvA373

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

lemma pole_unique2 {ℓ0 t k t1 k1 : ℤ} (ht : 0 ≤ t ∧ t ≤ 1) (ht1 : 0 ≤ t1 ∧ t1 ≤ 1)
    (h2 : lK t k = ℓ0) (h4 : lK t1 k1 = ℓ0) : t = t1 ∧ k = k1 := by
  unfold lK at h2 h4; omega

section EvB
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)
variable {ℓ0 ex0 t1 k1 : ℤ} {cx0 : ℂ}

include hqe in
lemma BS0_ev (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) :
    ev (BS (qe := qe) ey cy) ex0 cx0 = 0 := by
  rw [BS_ev hqe, hB, hc, show (5 * qe * ℓ0 : ℤ) = ((5 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h5 hqe) ℓ0

lemma lam1_rel0 (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) :
    (1 - mono (((5 * qe : ℕ) : ℤ) * lK t k - ((5 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) * ev (lam1 hqe ey cy t k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h5 hqe) (lK t k) (by norm_num : (3 : ℤ) ≠ 0) (qe * 4 - 2 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-2) hcy)) ex0 hcx
  have he : qe * 4 - 2 * ey + 3 * ex0 = ((5 * qe : ℕ) : ℤ) * ℓ0 := by unfold eBT at hB; push_cast; linarith
  have hcc : -(cy ^ (-2 : ℤ)) * cx0 ^ (3 : ℤ) = 1 := by unfold cBT at hc; rw [← hc]; ring
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam1_zero (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hl : lK t k ≠ ℓ0) : ev (lam1 hqe ey cy t k) ex0 cx0 = 0 := by
  have h := lam1_rel0 hqe ey cy hB hc hcx hcy t k
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((5 * qe : ℕ) : ℤ) := by have := h5 hqe; omega
  have : ((5 * qe : ℕ) : ℤ) * (lK t k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam1_spec (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hl : lK t k = ℓ0) :
    ev (lam1 hqe ey cy t k) ex0 cx0 = mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h5 hqe) := by
  unfold lam1
  rw [lamX_spec (h5 hqe) (lK t k) (by norm_num : (3 : ℤ) ≠ 0) (qe * 4 - 2 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero (-2) hcy)) ex0 hcx (by rw [hl]; unfold eBT at hB; push_cast; linarith)
    (by unfold cBT at hc; rw [← hc]; ring), hl]

noncomputable def Vb (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  θ (h2qe hqe) (3 * qe * t1 + ex0) cx0 * θ (h5 hqe) (eAT (qe := qe) ey ex0) (cAT cy cx0) *
    (sig1 (qe := qe) ey cy t1 k1 * (mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h5 hqe)))

lemma term1_B (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) (t k : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ev (term1 hqe ey cy t k) ex0 cx0 = if t = t1 ∧ k = k1 then Vb hqe ey cy t1 k1 ℓ0 ex0 cx0 else 0 := by
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hl : lK t k = ℓ0
  · obtain ⟨rfl, rfl⟩ := pole_unique2 ht ht1 hl h4
    rw [if_pos ⟨rfl, rfl⟩, lam1_spec hqe ey cy hB hc hcx hcy _ _ hl, Vb, Fix1,
      ev_conv (thX_ent (h2qe hqe) one_ne_zero _ _) (AS_ent hqe ey cy) ex0 hcx, thX_ev (h2qe hqe) one_ne_zero, AS_ev hqe]
    simp only [one_mul, zpow_one]
  · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hl h4
    rw [if_neg hne, lam1_zero hqe ey cy hB hc hcx hcy t k hl, mul_zero, mul_zero]

lemma PG1_B (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ev (PG1 hqe ey cy t) ex0 cx0 = if t = t1 then Vb hqe ey cy t1 k1 ℓ0 ex0 cx0 else 0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy ht.1 ht.2)]
  by_cases htt : t = t1
  · rw [if_pos htt, hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term1_B hqe ey cy hB hc hcx hcy ht1 h4 t k ht, if_neg (fun h => hk h.2)]),
      evColFam_apply, term1_B hqe ey cy hB hc hcx hcy ht1 h4 t k1 ht, if_pos ⟨htt, rfl⟩]
  · rw [if_neg htt]
    exact hs_zero_of fun k => by
      rw [evColFam_apply, term1_B hqe ey cy hB hc hcx hcy ht1 h4 t k ht, if_neg (fun h => htt h.1)]

lemma PG2_B (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) : ev (PG2 hqe ey cy t) ex0 cx0 = 0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy ht.1 ht.2)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t) (hL.smul _) ex0 hcx, Fix2, ev_conv (ent_monoS _ _) (BS_ent hqe ey cy) ex0 hcx,
    BS0_ev hqe ey cy hB hc, mul_zero, zero_mul]

/-- the bracket at a `B`-zero. -/
noncomputable def brB (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  sig1 (qe := qe) ey cy t1 k1 * mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
      θ (h2qe hqe) (3 * qe * t1 + ex0) cx0 * θ (h5 hqe) (eAT (qe := qe) ey ex0) (cAT cy cx0) +
    Tn hqe ey cy ex0 cx0

theorem FS_ev_B (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h5 hqe) * brB hqe ey cy t1 k1 ℓ0 ex0 cx0) := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  unfold FS GS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub ((a0.add a1).add (b0.add b1)))
      ((TS_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) ((a0.add a1).add (b0.add b1)),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_ev hqe ey cy ex0 hcx, Pv, Td,
    show θ (h5 hqe) (eBT (qe := qe) ey ex0) (cBT cy cx0) = 0 by rw [← BS_ev hqe]; exact BS0_ev hqe ey cy hB hc,
    ev_add (a0.add a1) (b0.add b1), ev_add a0 a1, ev_add b0 b1,
    PG1_B hqe ey cy hB hc hcx hcy ht1 h4 0 (by norm_num), PG1_B hqe ey cy hB hc hcx hcy ht1 h4 1 (by norm_num),
    PG2_B hqe ey cy hB hc hcx 0 (by norm_num), PG2_B hqe ey cy hB hc hcx 1 (by norm_num),
    ev_smul (TS_ent hqe ey cy), TS_ev hqe ey cy ex0 hcx, brB]
  rcases (by omega : t1 = 0 ∨ t1 = 1) with rfl | rfl <;> simp [Vb] <;> ring

/-- **the residue identity at a `B`-zero**, modulo one monomial identity. -/
theorem brB_zero (hB : eBT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cBT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (h4 : lK t1 k1 = ℓ0)
    (hm : sig1 (qe := qe) ey cy t1 k1 * mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) +
      mono (eTn (qe := qe) ey) (cTn cy) * Msh (2 * qe) (3 * qe * t1 + ex0) (3 - 5 * k1 + t1) cx0 *
        Msh (5 * qe) (eAT (qe := qe) ey ex0) ℓ0 (cAT cy cx0) = 0) :
    brB hqe ey cy t1 k1 ℓ0 ex0 cx0 = 0 := by
  have h1 : θ (h2qe hqe) (e1T ey ex0) (c1T cy cx0) =
      Msh (2 * qe) (3 * qe * t1 + ex0) (3 - 5 * k1 + t1) cx0 * θ (h2qe hqe) (3 * qe * t1 + ex0) cx0 := by
    rw [← θ_reflect (h2qe hqe) _ (c1T_ne cy hcx hcy)]
    have hcc : (c1T cy cx0)⁻¹ = cx0 := by
      unfold c1T; unfold cBT at hc
      have hx3 : cx0 ^ (3 : ℤ) ≠ 0 := zpow_ne_zero _ hcx
      have h' : cy ^ (-2 : ℤ) = -(cx0 ^ (3 : ℤ))⁻¹ := by
        rw [show cy ^ (-2 : ℤ) = (cx0 ^ (3 : ℤ))⁻¹ * (cx0 ^ (3 : ℤ) * cy ^ (-2 : ℤ)) by field_simp,
          show cx0 ^ (3 : ℤ) * cy ^ (-2 : ℤ) = -1 by linear_combination -hc]; ring
      rw [h']; simp only [zpow_ofNat]; field_simp
    rw [hcc]
    exact θ_sh (h2qe hqe) hcx _ (by
      unfold e1T; unfold eBT at hB; unfold lK at h4; push_cast
      have : (qe : ℤ) * 4 + 3 * ex0 - 2 * ey = 5 * qe * (2 * k1 - t1) := by rw [h4]; exact hB
      linear_combination -this)
  have h2 : θ (h5 hqe) (e2T (qe := qe) ey ex0) (c2T cy cx0) =
      Msh (5 * qe) (eAT (qe := qe) ey ex0) ℓ0 (cAT cy cx0) * θ (h5 hqe) (eAT (qe := qe) ey ex0) (cAT cy cx0) := by
    have hcc : c2T cy cx0 = cAT cy cx0 := by
      unfold cBT at hc; unfold c2T cAT
      rw [show cx0 * cy = (-(cy ^ (3 : ℤ) * cx0 ^ (-2 : ℤ))) * (-(cx0 ^ (3 : ℤ) * cy ^ (-2 : ℤ))) by
        simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
    rw [hcc]
    exact θ_sh (h5 hqe) (cAT_ne cy hcx hcy) ℓ0 (by
      unfold e2T eAT; unfold eBT at hB; push_cast; linear_combination hB)
  unfold brB Tn
  rw [h1, h2]
  linear_combination (θ (h2qe hqe) (3 * qe * t1 + ex0) cx0 * θ (h5 hqe) (eAT (qe := qe) ey ex0) (cAT cy cx0)) * hm

end EvB

section EvA
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)
variable {ℓ0 ex0 t1 k1 : ℤ} {cx0 : ℂ}

include hqe in
lemma AS0_ev (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) :
    ev (AS (qe := qe) ey cy) ex0 cx0 = 0 := by
  rw [AS_ev hqe, hA, hc, show (5 * qe * ℓ0 : ℤ) = ((5 * qe : ℕ) : ℤ) * ℓ0 by push_cast; ring]
  exact θ_qpow (h5 hqe) ℓ0

lemma lam2_rel0 (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) :
    (1 - mono (((5 * qe : ℕ) : ℤ) * lK t k - ((5 * qe : ℕ) : ℤ) * ℓ0) (1 : ℂ)⁻¹) * ev (lam2 hqe ey cy t k) ex0 cx0 = 0 := by
  have hrel := lamX_rel (h5 hqe) (lK t k) (by norm_num : (-2 : ℤ) ≠ 0) (qe * 4 + 3 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 3 hcy)) ex0 hcx
  have he : qe * 4 + 3 * ey + -2 * ex0 = ((5 * qe : ℕ) : ℤ) * ℓ0 := by unfold eAT at hA; push_cast; linarith
  have hcc : -(cy ^ (3 : ℤ)) * cx0 ^ (-2 : ℤ) = 1 := by unfold cAT at hc; rw [← hc]; ring
  rw [he, hcc, θ_qpow] at hrel
  exact hrel

lemma lam2_zero (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hl : lK t k ≠ ℓ0) : ev (lam2 hqe ey cy t k) ex0 cx0 = 0 := by
  have h := lam2_rel0 hqe ey cy hA hc hcx hcy t k
  refine (mul_eq_zero.mp h).resolve_left (one_sub_mono_ne_zero ?_)
  rintro ⟨h1, _⟩
  apply hl
  have hN : (0 : ℤ) < ((5 * qe : ℕ) : ℤ) := by have := h5 hqe; omega
  have : ((5 * qe : ℕ) : ℤ) * (lK t k - ℓ0) = 0 := by rw [mul_sub]; exact h1
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

lemma lam2_spec (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (t k : ℤ) (hl : lK t k = ℓ0) :
    ev (lam2 hqe ey cy t k) ex0 cx0 = mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) * kap (h5 hqe) := by
  unfold lam2
  rw [lamX_spec (h5 hqe) (lK t k) (by norm_num : (-2 : ℤ) ≠ 0) (qe * 4 + 3 * ey)
    (neg_ne_zero.mpr (zpow_ne_zero 3 hcy)) ex0 hcx (by rw [hl]; unfold eAT at hA; push_cast; linarith)
    (by unfold cAT at hc; rw [← hc]; ring), hl]

noncomputable def SA (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  sig2 (qe := qe) k1 * mono (-(((5 * qe : ℕ) : ℤ) * c2 ℓ0)) ((-1) ^ (ℓ0 + 1)) *
    (mono (2 * qe * c2 t1) ((-1) ^ t1) * mono (ex0 * t1) (cx0 ^ t1))

noncomputable def Va (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  SA (qe := qe) t1 k1 ℓ0 ex0 cx0 * θ (h2qe hqe) (3 * qe * t1 + ey) cy *
    θ (h5 hqe) (eBT (qe := qe) ey ex0) (cBT cy cx0) * kap (h5 hqe)

lemma term2_A (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) (t k : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ev (term2 hqe ey cy t k) ex0 cx0 = if t = t1 ∧ k = k1 then Va hqe ey cy t1 k1 ℓ0 ex0 cx0 else 0 := by
  have hL : Ent (lam2 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  unfold term2
  rw [ev_conv (Fix2_ent hqe ey cy t) (hL.smul _) ex0 hcx, ev_smul hL]
  by_cases hl : lK t k = ℓ0
  · obtain ⟨rfl, rfl⟩ := pole_unique2 ht ht1 hl h4
    rw [if_pos ⟨rfl, rfl⟩, lam2_spec hqe ey cy hA hc hcx hcy _ _ hl, Va, SA, Fix2,
      ev_conv (ent_monoS _ _) (BS_ent hqe ey cy) ex0 hcx, ev_monoS, BS_ev hqe]
    ring
  · have hne : ¬(t = t1 ∧ k = k1) := by rintro ⟨rfl, rfl⟩; exact hl h4
    rw [if_neg hne, lam2_zero hqe ey cy hA hc hcx hcy t k hl, mul_zero, mul_zero]

lemma PG2_A (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ev (PG2 hqe ey cy t) ex0 cx0 = if t = t1 then Va hqe ey cy t1 k1 ℓ0 ex0 cx0 else 0 := by
  unfold PG2
  rw [ev_sumS (term2_udec hqe ey cy ht.1 ht.2)]
  by_cases htt : t = t1
  · rw [if_pos htt, hs_single_of k1 (fun k hk => by
      rw [evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h4 t k ht, if_neg (fun h => hk h.2)]),
      evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h4 t k1 ht, if_pos ⟨htt, rfl⟩]
  · rw [if_neg htt]
    exact hs_zero_of fun k => by
      rw [evColFam_apply, term2_A hqe ey cy hA hc hcx hcy ht1 h4 t k ht, if_neg (fun h => htt h.1)]

lemma PG1_A (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0)
    (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 1) : ev (PG1 hqe ey cy t) ex0 cx0 = 0 := by
  unfold PG1
  rw [ev_sumS (term1_udec hqe ey cy ht.1 ht.2)]
  refine hs_zero_of fun k => ?_
  have hL : Ent (lam1 hqe ey cy t k) := lamX_ent (h5 hqe) _ (by norm_num) _ _
  rw [evColFam_apply]
  unfold term1
  rw [ev_conv (Fix1_ent hqe ey cy t) (hL.smul _) ex0 hcx, Fix1,
    ev_conv (thX_ent (h2qe hqe) one_ne_zero _ _) (AS_ent hqe ey cy) ex0 hcx, AS0_ev hqe ey cy hA hc, mul_zero, zero_mul]

noncomputable def brA (t1 k1 ℓ0 ex0 : ℤ) (cx0 : ℂ) : L :=
  SA (qe := qe) t1 k1 ℓ0 ex0 cx0 * θ (h2qe hqe) (3 * qe * t1 + ey) cy * θ (h5 hqe) (eBT (qe := qe) ey ex0) (cBT cy cx0) +
    Tn hqe ey cy ex0 cx0

theorem FS_ev_A (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1) (h4 : lK t1 k1 = ℓ0) :
    ev (FS hqe ey cy) ex0 cx0 = -(kap (h5 hqe) * brA hqe ey cy t1 k1 ℓ0 ex0 cx0) := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  unfold FS GS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub ((a0.add a1).add (b0.add b1)))
      ((TS_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) ((a0.add a1).add (b0.add b1)),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex0 hcx, PS_ev hqe ey cy ex0 hcx, Pv, Td,
    show θ (h5 hqe) (eAT (qe := qe) ey ex0) (cAT cy cx0) = 0 by rw [← AS_ev hqe]; exact AS0_ev hqe ey cy hA hc,
    ev_add (a0.add a1) (b0.add b1), ev_add a0 a1, ev_add b0 b1,
    PG1_A hqe ey cy hA hc hcx 0 (by norm_num), PG1_A hqe ey cy hA hc hcx 1 (by norm_num),
    PG2_A hqe ey cy hA hc hcx hcy ht1 h4 0 (by norm_num), PG2_A hqe ey cy hA hc hcx hcy ht1 h4 1 (by norm_num),
    ev_smul (TS_ent hqe ey cy), TS_ev hqe ey cy ex0 hcx, brA]
  rcases (by omega : t1 = 0 ∨ t1 = 1) with rfl | rfl <;> simp [Va] <;> ring

theorem brA_zero (hA : eAT (qe := qe) ey ex0 = 5 * qe * ℓ0) (hc : cAT cy cx0 = 1) (hcx : cx0 ≠ 0) (hcy : cy ≠ 0)
    (h4 : lK t1 k1 = ℓ0)
    (hm : SA (qe := qe) t1 k1 ℓ0 ex0 cx0 +
      mono (eTn (qe := qe) ey) (cTn cy) * Msh (2 * qe) (3 * qe * t1 + ey) (2 - 5 * k1 + t1) cy *
        Msh (5 * qe) (eBT (qe := qe) ey ex0) ℓ0 (cBT cy cx0) = 0) :
    brA hqe ey cy t1 k1 ℓ0 ex0 cx0 = 0 := by
  have h1 : θ (h2qe hqe) (e1T ey ex0) (c1T cy cx0) =
      Msh (2 * qe) (3 * qe * t1 + ey) (2 - 5 * k1 + t1) cy * θ (h2qe hqe) (3 * qe * t1 + ey) cy := by
    have hcc : c1T cy cx0 = cy := by
      unfold c1T; unfold cAT at hc
      have hx : cx0 ^ 2 = -(cy ^ 3) := by
        have h' : cy ^ (3 : ℤ) * cx0 ^ (-2 : ℤ) = -1 := by linear_combination -hc
        rw [zpow_neg, zpow_ofNat, zpow_ofNat] at h'
        field_simp at h'
        first | linear_combination -h' | linear_combination h'
      simp only [zpow_neg, zpow_ofNat]; rw [hx]; field_simp; try ring
    rw [hcc]
    exact θ_sh (h2qe hqe) hcy _ (by
      unfold e1T; unfold eAT at hA; unfold lK at h4; push_cast
      have : (qe : ℤ) * 4 + 3 * ey - 2 * ex0 = 5 * qe * (2 * k1 - t1) := by rw [h4]; exact hA
      linear_combination -this)
  have h2 : θ (h5 hqe) (e2T (qe := qe) ey ex0) (c2T cy cx0) =
      Msh (5 * qe) (eBT (qe := qe) ey ex0) ℓ0 (cBT cy cx0) * θ (h5 hqe) (eBT (qe := qe) ey ex0) (cBT cy cx0) := by
    have hcc : c2T cy cx0 = cBT cy cx0 := by
      unfold cAT at hc; unfold c2T cBT
      rw [show cx0 * cy = (-(cx0 ^ (3 : ℤ) * cy ^ (-2 : ℤ))) * (-(cy ^ (3 : ℤ) * cx0 ^ (-2 : ℤ))) by
        simp only [zpow_neg, zpow_ofNat]; field_simp; try ring, hc, mul_one]
    rw [hcc]
    exact θ_sh (h5 hqe) (cBT_ne cy hcx hcy) ℓ0 (by
      unfold e2T eBT; unfold eAT at hA; push_cast; linear_combination hA)
  unfold brA Tn
  rw [h1, h2]
  linear_combination (θ (h2qe hqe) (3 * qe * t1 + ey) cy * θ (h5 hqe) (eBT (qe := qe) ey ex0) (cBT cy cx0)) * hm

end EvA

end MTC.H232
