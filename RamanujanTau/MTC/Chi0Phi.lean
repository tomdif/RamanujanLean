/-
# The χ₀ endgame: the `Φ` side

`L5_lam` at `q = Q = t⁶` writes `(1 + φ(Q)) (Q⁵;Q⁵)_∞` as three Lambert numerators in base `Q^{15} = t^{90}`.
The `n = 2` split (`Alam_split2`) moves `A₁₀` and `A₂₀` to base `t^{360}`, and changes of `z` (`czB`) express
everything through the four classes `Bv 174, Bv 6, Bv 66, Bv 114` of the HM side.
-/
import RamanujanTau.MTC.Chi0Split
import RamanujanTau.MTC.LemC

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

lemma hs_splitF {N : ℕ} (hN : 1 ≤ N) (ex ez : ℤ) (hw : ∀ r, wE N ex ez r ≠ 0) (ρ : ℤ) :
    hs (splitF hN ex ez hw ρ) =
      Av (h4N hN) (N + 2 * ex) (-1) (N * (1 + 2 * ρ) + 2 * ez) (-1) +
        mono (N * (ρ - 1) + ex + ez) 1 * Av (h4N hN) (2 * ex - N) (-1) (N * (3 + 2 * ρ) + 2 * ez) (-1) := by
  unfold splitF
  rw [hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_smul, ← hs_eq, ← hs_eq,
    Av_eq_Alam (h4N hN) (by norm_num) (by norm_num) (lamOK_of_wE (hwA ex ez hw ρ)),
    Av_eq_Alam (h4N hN) (by norm_num) (by norm_num) (lamOK_of_wE (hwB ex ez hw ρ))]
  rfl

lemma hw_LF (b : ℤ) : ∀ r, wE (15 * 6) ((18 - b) * ((6 : ℕ) : ℤ)) (b * ((6 : ℕ) : ℤ)) r ≠ 0 := fun r h => by
  unfold wE at h; push_cast at h; omega

lemma Av4 (e : ℤ) (c : ℂ) (f : ℤ) (d : ℂ) : Av (h4N (h15 h6)) e c f d = Av hN360 e c f d :=
  Av_N (h4N (h15 h6)) (by norm_num) hN360 e c f d

/-- `A₁₀` and `A₂₀` split into base `t^{360}`. -/
theorem LF_split (b : ℤ) :
    hs (LF h6 b) =
      (Av hN360 (90 + 2 * ((18 - b) * 6)) (-1) (90 + 2 * (b * 6)) (-1) +
        mono (-90 + (18 - b) * 6 + b * 6) 1 * Av hN360 (2 * ((18 - b) * 6) - 90) (-1) (270 + 2 * (b * 6)) (-1)) +
      mono (b * 6) (-1) * (Av hN360 (90 + 2 * ((18 - b) * 6)) (-1) (270 + 2 * (b * 6)) (-1) +
        mono ((18 - b) * 6 + b * 6) 1 * Av hN360 (2 * ((18 - b) * 6) - 90) (-1) (450 + 2 * (b * 6)) (-1)) := by
  have h := Alam_split2 (h15 h6) ((18 - b) * ((6 : ℕ) : ℤ)) (b * ((6 : ℕ) : ℤ)) (hw_LF b)
  rw [hs_splitF, hs_splitF] at h
  simp only [Av4] at h
  have e : hs (LF h6 b) = Alam (h15 h6) one_ne_zero one_ne_zero (lamOK_of_wE (cx := 1) (cz := 1) (hw_LF b)) := rfl
  rw [e, h]
  push_cast
  ring_nf

/-! ## The eight pieces -/

/-- the theta part of the change `−t^{b₀} → −1` at `x = −t^a`. -/
noncomputable def Rt (a b0 : ℤ) : L :=
  mono b0 (-1) * hs (kF hN360 0) * θ hN360 (-b0) 1 * θ hN360 (a + b0) (-1) / (θ hN360 (a + b0) 1 * θ hN360 a 1)

lemma zs {a : ℤ} (z : ℤ) (h : (a + z) % 360 ≠ 0) : Av hN360 a (-1) (z + 360) (-1) = mono (-z) 1 * Av hN360 a (-1) z (-1) := by
  have h1 := Av_zshift' hN360 (ex := a) (ez := z) (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0)
    (lamOK360' h)
  rw [show ((10 * 36 : ℕ) : ℤ) = 360 by norm_num, show -(mono z (-1) : L) = mono z 1 by simp [mono]] at h1
  rw [h1, ← mul_assoc, mono_mul, show (mono (-z + z) (1 * 1) : L) = 1 from mono_ext (by ring) (by norm_num), one_mul]

lemma xs {a z : ℤ} (h : (a - 360 + z) % 360 ≠ 0) :
    Av hN360 a (-1) z (-1) = th360 z (-1) + mono (a - 360) 1 * Av hN360 (a - 360) (-1) z (-1) := by
  have h1 := Av_qshift hN360 (ex := a - 360) (ez := z) (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0)
    (lamOK360' h)
  rw [show a - 360 + ((10 * 36 : ℕ) : ℤ) = a by push_cast; ring,
    show (mono (a - 360) (-1) : L) = -mono (a - 360) 1 by simp [mono]] at h1
  unfold th360; linear_combination h1

lemma θa_ne {a : ℤ} (h : a % 360 ≠ 0) : θ hN360 a 1 ≠ 0 :=
  θ_ne_zero hN360 one_ne_zero fun k hk => absurd (by rw [hk]; push_cast; simp) h

lemma B186 : Bv 186 = Jb6 - Bv 174 := by
  rw [show (186 : ℤ) = -174 + 360 by norm_num, Bv_qs (by norm_num), Bv_inv (by norm_num)]
  simp only [monoT]
  have := tt_ne
  field_simp
  ring

lemma Bm294 : Bv (-294) = mono 294 1 * (Bv 66 - Jb6) := by
  have h := Bv_qs (e := -294) (by norm_num)
  rw [show (-294 : ℤ) + 360 = 66 by norm_num] at h
  rw [h, show (mono 294 1 : L) * (Jb6 + mono (-294) 1 * Bv (-294) - Jb6) = (mono 294 1 * mono (-294) 1) * Bv (-294) by ring,
    mono_mul, show (mono (294 + -294) ((1 : ℂ) * 1) : L) = 1 from mono_ext (by norm_num) (by norm_num), one_mul]

lemma pc1 : Jb6 * Av hN360 186 (-1) 210 (-1) = Jb6 * th360 210 (-1) - th360 210 (-1) * Bv 174 + mono (-174) 1 * Rt (-174) 210 := by
  rw [xs (by norm_num), show (186 : ℤ) - 360 = -174 by norm_num, mul_add, mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num)),
    Bv_inv (by norm_num)]
  unfold Rt
  simp only [monoT]
  have := tt_ne
  field_simp
  ring

lemma pc2 : Jb6 * Av hN360 6 (-1) 390 (-1) = mono (-30) 1 * (th360 30 (-1) * Bv 6 + Rt 6 30) := by
  rw [show (390 : ℤ) = 30 + 360 by norm_num, zs 30 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num))]
  unfold Rt; ring

lemma pc3 : Jb6 * Av hN360 186 (-1) 390 (-1) = mono (-30) 1 * (th360 30 (-1) * (Jb6 - Bv 174) + Rt 186 30) := by
  rw [show (390 : ℤ) = 30 + 360 by norm_num, zs 30 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num)),
    B186]
  unfold Rt; ring

lemma pc4 : Jb6 * Av hN360 6 (-1) 570 (-1) = mono (-210) 1 * (th360 210 (-1) * Bv 6 + Rt 6 210) := by
  rw [show (570 : ℤ) = 210 + 360 by norm_num, zs 210 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num))]
  unfold Rt; ring

lemma pc5 : Jb6 * Av hN360 66 (-1) 330 (-1) =
    Jb6 * th360 330 (-1) + mono (-294) 1 * (th360 330 (-1) * (mono 294 1 * (Bv 66 - Jb6)) + Rt (-294) 330) := by
  rw [xs (by norm_num), show (66 : ℤ) - 360 = -294 by norm_num, mul_add, mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num)),
    Bm294]
  unfold Rt; ring

lemma pc6 : Jb6 * Av hN360 (-114) (-1) 510 (-1) = mono (-150) 1 * (th360 150 (-1) * (-mono 114 1 * Bv 114) + Rt (-114) 150) := by
  rw [show (510 : ℤ) = 150 + 360 by norm_num, zs 150 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num)),
    Bv_inv (by norm_num)]
  unfold Rt; ring

lemma pc7 : Jb6 * Av hN360 66 (-1) 510 (-1) = mono (-150) 1 * (th360 150 (-1) * Bv 66 + Rt 66 150) := by
  rw [show (510 : ℤ) = 150 + 360 by norm_num, zs 150 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num))]
  unfold Rt; ring

lemma pc8 : Jb6 * Av hN360 (-114) (-1) 690 (-1) = mono (-330) 1 * (th360 330 (-1) * (-mono 114 1 * Bv 114) + Rt (-114) 330) := by
  rw [show (690 : ℤ) = 330 + 360 by norm_num, zs 330 (by norm_num), mul_left_comm,
    czB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (θa_ne (by norm_num)),
    Bv_inv (by norm_num)]
  unfold Rt; ring

/-! ## `(Q⁵;Q⁵)_∞` -/

lemma h30 : 1 ≤ 6 * 5 := by norm_num
lemma h90 : 1 ≤ 90 := by norm_num

lemma J30_eq : θ h90 60 1 = ιN h30 MockTheta5.JTP.qfacInf := by
  rw [θu h30 h90 3 2 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) le_rfl, ← RankProof.Pinf_one_one,
    ιN_Pinf_split h30 1 1 3 le_rfl le_rfl (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul, mul_zero, add_zero, mul_one, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul]
  ring

lemma th360_refl (e : ℤ) : th360 (360 - e) (-1) = th360 e (-1) := by
  have h := θ_reflect hN360 e (by norm_num : (-1 : ℂ) ≠ 0)
  unfold th360
  rw [show (((10 * 36 : ℕ) : ℤ)) = 360 by norm_num, show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  exact h

lemma th360_qs (e s : ℤ) : th360 (e + 360 * s) (-1) = mono (-(360 * c2 (s + 1)) - e * s + 360 * s) 1 * th360 e (-1) := by
  have h := θ_qshift hN360 e (by norm_num : (-1 : ℂ) ≠ 0) s
  unfold th360
  rw [show (((10 * 36 : ℕ) : ℤ)) = 360 by norm_num] at h
  rw [h]
  congr 1
  refine mono_ext rfl ?_
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one, ← mul_zpow]; norm_num

/-- `(Q⁵;Q⁵)_∞ = j(−t^{150}; t^{360}) − t^{30} j(−t^{30}; t^{360})`. -/
lemma eQdis : ιN h6 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) = th360 150 (-1) - mono 30 1 * th360 30 (-1) := by
  rw [← ιN_Ea h6 (by norm_num) h30, ← J30_eq, θ]
  have hsp := hs_split (thF h90 60 1) (thF hN360 210 (-1)) ((-mono 60 1 : L) • thF hN360 390 (-1)) eEO
    (fun m => by
      simp only [thF, monoFam_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inl]
      refine mono_ext ?_ ?_
      · unfold thE; have h1 := two_c2 (2 * m); have h2 := two_c2 m; push_cast; nlinarith
      · unfold thC; rw [one_zpow, mul_one, two_mul, zpow_add₀ (by norm_num)])
    (fun m => by
      simp only [thF, monoFam_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
        HahnSeries.of_symm_smul_of_eq_mul]
      rw [neg_mul, mono_mul, neg_mono]
      refine mono_ext ?_ ?_
      · unfold thE; have h1 := two_c2 (2 * m + 1); have h2 := two_c2 m; push_cast; nlinarith
      · unfold thC; rw [one_zpow, mul_one, one_mul, neg_one_zpow_sq, zpow_add₀ (by norm_num), zpow_one,
          zpow_mul]; norm_num)
  rw [hsp, hs_eq (_ • _), SummableFamily.hsum_smul, ← hs_eq]
  have e1 : hs (thF hN360 210 (-1)) = th360 150 (-1) := by
    show th360 210 (-1) = th360 150 (-1)
    rw [show (210 : ℤ) = 360 - 150 by norm_num, th360_refl]
  have e2 : hs (thF hN360 390 (-1)) = mono (-30) 1 * th360 30 (-1) := by
    show th360 390 (-1) = _
    rw [show (390 : ℤ) = 30 + 360 * 1 by norm_num, th360_qs]
    exact congrArg (· * _) (mono_ext (by norm_num [c2]) rfl)
  rw [e1, e2, ← mul_assoc, mono_neg1, mono_mul,
    show (mono (60 + -30) (-1 * 1) : L) = -mono 30 1 by rw [mono_neg1]; exact mono_ext (by norm_num) (by norm_num)]
  ring

/-- `A₁₅ = (Q^{15};Q^{15})³ / j(Q³; Q^{15})`, multiplied out. -/
lemma LF15_eq : θ (h15 h6) 18 1 * hs (LF h6 15) = (ιN (h15 h6) MockTheta5.JTP.qfacInf) ^ 3 := by
  have e : hs (LF h6 15) = Av (h15 h6) ((18 - 15) * ((6 : ℕ) : ℤ)) 1 (15 * ((6 : ℕ) : ℤ)) 1 := by
    rw [Av_eq_Alam (h15 h6) one_ne_zero one_ne_zero (lamOK18 h6 15)]; rfl
  norm_num at e
  have hok : LamOK (15 * 6) 18 1 0 1 := fun r ⟨h1, _⟩ => by unfold wE at h1; push_cast at h1; omega
  have z := Av_zshift' (h15 h6) (ex := 18) (ez := 0) one_ne_zero one_ne_zero hok
  have k := kappa_eq_jacobi (h15 h6) (a := 18) (by norm_num) (by norm_num) (cx := 1) one_ne_zero
    (mono_ne_one' (Or.inl (by norm_num)))
  rw [← Av_eq_Ab' (h15 h6) one_ne_zero one_ne_zero hok] at k
  rw [show (mono 0 1 : L) = 1 from rfl, show (0 : ℤ) + ((15 * 6 : ℕ) : ℤ) = 90 by norm_num] at z
  rw [e]
  linear_combination θ (h15 h6) 18 1 * z - k

/-- the eight change-of-`z` theta terms of the `Φ` side, with their weights. -/
noncomputable def T1s : L :=
  (tt ^ (-174 : ℤ) * Rt (-174) 210 + tt ^ (-12 : ℤ) * Rt 6 30 - tt ^ (30 : ℤ) * Rt 186 30 - tt ^ (-42 : ℤ) * Rt 6 210) +
  (tt ^ (-282 : ℤ) * Rt (-294) 330 + tt ^ (-120 : ℤ) * Rt (-114) 150 - tt ^ (-18 : ℤ) * Rt 66 150 -
    tt ^ (-90 : ℤ) * Rt (-114) 330)

/-- **the `Φ` side**: `J̄ (1+φ(Q)) (Q⁵;Q⁵)_∞ = −(Q⁵;Q⁵)_∞ (B₁₇₄ + t⁻⁴² B₆ + t⁻¹⁸ B₆₆ + t⁻⁶ B₁₁₄)
+ (Q⁵;Q⁵)_∞ J̄ + T₁ + t⁶ J̄ A₁₅`. -/
theorem phi_side : Jb6 * (ιN h6 (RankProof.Phi 1) * ιN h6 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)) =
    -ιN h6 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) *
        (Bv 174 + tt ^ (-42 : ℤ) * Bv 6 + tt ^ (-18 : ℤ) * Bv 66 + tt ^ (-6 : ℤ) * Bv 114) +
      ιN h6 (RankProof.Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) * Jb6 + T1s + tt ^ (6 : ℤ) * Jb6 * hs (LF h6 15) := by
  rw [L5_lam h6, LF_split 10, LF_split 20, eQdis]
  norm_num
  have q1 := pc1; have q2 := pc2; have q3 := pc3; have q4 := pc4
  have q5 := pc5; have q6 := pc6; have q7 := pc7; have q8 := pc8
  have r1 : th360 210 (-1) = th360 150 (-1) := by rw [show (210 : ℤ) = 360 - 150 by norm_num, th360_refl]
  have r2 : th360 330 (-1) = th360 30 (-1) := by rw [show (330 : ℤ) = 360 - 30 by norm_num, th360_refl]
  rw [r1] at q1 q4
  rw [r2] at q5 q8
  unfold T1s
  simp only [monoT, monoTn, mono_neg1] at *
  have htt := tt_ne
  linear_combination (norm := (field_simp; ring)) q1 + tt ^ (18 : ℤ) * q2 - tt ^ (60 : ℤ) * q3 -
    tt ^ (168 : ℤ) * q4 + tt ^ (12 : ℤ) * q5 + tt ^ (30 : ℤ) * q6 - tt ^ (132 : ℤ) * q7 - tt ^ (240 : ℤ) * q8

end MTC.Chi0L
