/-
# HM Theorem 0.3 for `f_{2,3,2}` at real points

At the χ₀ points every coefficient is `±1`, so the coefficient test `CGood` fails although no denominator vanishes.
`FS_ev_of` and `hm03_of` replace `CGood` by the exact conditions: the four Lambert series have no pole
(`eX, eY ∉ 10 qe ℤ`) and `Td ≠ 0` (`eAT, eBT ∉ 5 qe ℤ`).
-/
import RamanujanTau.MTC.Zeros232

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section Real
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma okX_of {t ex : ℤ} {cx : ℂ} (h : eX (qe := qe) ey t ex % (10 * qe) ≠ 0) : OKX (qe := qe) ey cy t ex cx := by
  rintro r ⟨h1, _⟩
  apply h
  unfold wE at h1
  push_cast at h1
  rw [show eX (qe := qe) ey t ex = 10 * qe * (1 - r) by linarith]
  simp

lemma okY_of {t ex : ℤ} {cx : ℂ} (h : eY (qe := qe) ey t ex % (10 * qe) ≠ 0) : OKY (qe := qe) ey cy t ex cx := by
  rintro r ⟨h1, _⟩
  apply h
  unfold wE at h1
  push_cast at h1
  rw [show eY (qe := qe) ey t ex = 10 * qe * (1 - r) by linarith]
  simp

lemma td_of {ex : ℤ} {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) (hA : eAT (qe := qe) ey ex % (5 * qe) ≠ 0)
    (hB : eBT (qe := qe) ey ex % (5 * qe) ≠ 0) : Td hqe ey cy ex cx ≠ 0 := by
  unfold Td
  refine mul_ne_zero (θ_ne_zero (h5 hqe) (cAT_ne cy hcx hcy) fun a ha => ?_)
    (θ_ne_zero (h5 hqe) (cBT_ne cy hcx hcy) fun a ha => ?_)
  · exact absurd (by rw [ha]; push_cast; simp) hA
  · exact absurd (by rw [ha]; push_cast; simp) hB

theorem FS_ev_of (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hX0 : OKX (qe := qe) ey cy 0 ex cx) (hX1 : OKX (qe := qe) ey cy 1 ex cx)
    (hY0 : OKY (qe := qe) ey cy 0 ex cx) (hY1 : OKY (qe := qe) ey cy 1 ex cx) (hd : Td hqe ey cy ex cx ≠ 0) :
    ev (FS hqe ey cy) ex cx = Pv hqe ey cy ex cx * Dv hqe ey cy ex cx := by
  have a0 := PG1_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have a1 := PG1_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  have b0 := PG2_ent hqe ey cy le_rfl (by norm_num : (0 : ℤ) ≤ 1)
  have b1 := PG2_ent hqe ey cy (by norm_num : (0 : ℤ) ≤ 1) le_rfl
  have hGS : ev (GS hqe ey cy) ex cx = Pv hqe ey cy ex cx * gNum hqe ey cy ex cx := by
    unfold GS
    rw [ev_add (a0.add a1) (b0.add b1), ev_add a0 a1, ev_add b0 b1,
      PG1_ev hqe ey cy le_rfl (by norm_num) ex hcx hcy hX0, PG1_ev hqe ey cy (by norm_num) le_rfl ex hcx hcy hX1,
      PG2_ev hqe ey cy le_rfl (by norm_num) ex hcx hcy hY0, PG2_ev hqe ey cy (by norm_num) le_rfl ex hcx hcy hY1, gNum]
    ring
  unfold FS
  rw [ev_sub (((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)).sub (GS_ent hqe ey cy)) ((TS_ent hqe ey cy).smul _),
    ev_sub ((PS_ent hqe ey cy).conv ((fS_ent hqe ey cy).smul _)) (GS_ent hqe ey cy),
    ev_conv (PS_ent hqe ey cy) ((fS_ent hqe ey cy).smul _) ex hcx, ev_smul (fS_ent hqe ey cy),
    ev_smul (TS_ent hqe ey cy), PS_ev hqe ey cy ex hcx, hGS, TS_ev' hqe ey cy ex hcx hd, Dv]
  ring

/-- **HM Theorem 0.3 for `f_{2,3,2}`** at any point where no denominator vanishes, given `F ≡ 0`. -/
theorem hm03_of (hF : FS hqe ey cy = 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0)
    (hX0 : eX (qe := qe) ey 0 ex % (10 * qe) ≠ 0) (hX1 : eX (qe := qe) ey 1 ex % (10 * qe) ≠ 0)
    (hY0 : eY (qe := qe) ey 0 ex % (10 * qe) ≠ 0) (hY1 : eY (qe := qe) ey 1 ex % (10 * qe) ≠ 0)
    (hA : eAT (qe := qe) ey ex % (5 * qe) ≠ 0) (hB : eBT (qe := qe) ey ex % (5 * qe) ≠ 0) :
    Jb hqe * ev (fS hqe ey cy) ex cx = gNum hqe ey cy ex cx + kap (h5 hqe) * thV hqe ey cy ex cx := by
  have hd := td_of hqe ey cy hcx hcy hA hB
  have h1 := FS_ev_of hqe ey cy ex hcx hcy (okX_of ey cy hX0) (okX_of ey cy hX1) (okY_of ey cy hY0)
    (okY_of ey cy hY1) hd
  rw [hF, show (0 : ℤ → L) = fun _ => (0 : L) from rfl, ev_zero] at h1
  have := (mul_eq_zero.mp h1.symm).resolve_left hd
  unfold Dv at this
  linear_combination this

end Real

/-! ## The eight χ₀ points -/

lemma hz : (Z84 ^ (42 : ℤ) : ℂ) ≠ 0 := zpow_ne_zero _ Z_ne

/-- HM Theorem 0.3 at `x = −t^{6a}`, `y = −t^{6b}` (`q = t^{36}`) for the eight χ₀ points. -/
theorem hm03_77 : Jb hq36 * ev (fS hq36 42 (-1)) 42 (-1) = gNum hq36 42 (-1) 42 (-1) + kap (h5 hq36) * thV hq36 42 (-1) 42 (-1) :=
  hm03_of hq36 42 (-1) Fb7_eq_zero 42 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_16_13 : Jb hq36 * ev (fS hq36 78 (-1)) 96 (-1) = gNum hq36 78 (-1) 96 (-1) + kap (h5 hq36) * thV hq36 78 (-1) 96 (-1) :=
  hm03_of hq36 78 (-1) Fb13_eq_zero 96 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_11_13 : Jb hq36 * ev (fS hq36 78 (-1)) 66 (-1) = gNum hq36 78 (-1) 66 (-1) + kap (h5 hq36) * thV hq36 78 (-1) 66 (-1) :=
  hm03_of hq36 78 (-1) Fb13_eq_zero 66 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_22_17 : Jb hq36 * ev (fS hq36 102 (-1)) 132 (-1) = gNum hq36 102 (-1) 132 (-1) + kap (h5 hq36) * thV hq36 102 (-1) 132 (-1) :=
  hm03_of hq36 102 (-1) Fb17_eq_zero 132 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_20_19 : Jb hq36 * ev (fS hq36 114 (-1)) 120 (-1) = gNum hq36 114 (-1) 120 (-1) + kap (h5 hq36) * thV hq36 114 (-1) 120 (-1) :=
  hm03_of hq36 114 (-1) Fb19_eq_zero 120 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_16_19 : Jb hq36 * ev (fS hq36 114 (-1)) 96 (-1) = gNum hq36 114 (-1) 96 (-1) + kap (h5 hq36) * thV hq36 114 (-1) 96 (-1) :=
  hm03_of hq36 114 (-1) Fb19_eq_zero 96 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hm03_25_25 : Jb hq36 * ev (fS hq36 150 (-1)) 150 (-1) = gNum hq36 150 (-1) 150 (-1) + kap (h5 hq36) * thV hq36 150 (-1) 150 (-1) :=
  hm03_of hq36 150 (-1) Fb25_eq_zero 150 hm1 hm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end MTC.H232
