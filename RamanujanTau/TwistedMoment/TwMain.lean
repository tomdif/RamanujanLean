/-
# Main theorem: the symmetrised twisted second moment with power saving

`twisted_moment`: for all `h, k ≥ 1` and `X ≥ 2^{300}`, with `H = X^{299/300}`,

    ‖TwAv h k X H − MainTw h k X H‖ ≤ C (hk)^{33} X^{599/600},

where `TwAv h k X H = (1/H)∫_X^{X+H}∫_{16}^u |L(Δ,6+it)|²((h/k)^{it} + (k/h)^{it}) dt du`
and `MainTw` is the smoothed diagonal `kM = hN`.
-/
import RamanujanTau.TwistedMoment.TwFinal

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2 RamanujanTau.HeckeL
open scoped Interval

lemma continuousOn_S (lam : ℕ → ℝ) [GoodSeq lam] (T' : ℝ) :
    ContinuousOn (fun t => ∑' q, bG2 lam lam (GoodSeq.c lam) t q) (Icc 16 T') :=
  continuousOn_tsum (fun q => (continuousOn_bG2 q).mono (fun x hx => lt_of_lt_of_le (by norm_num) hx.1))
    (summable_vq (lam := lam) T') (fun q t ht => norm_bG2_le ht.1 ht.2 q)

lemma tsum_zzF_split (lam : ℕ → ℝ) [GoodSeq lam] {X H : ℝ} (hs : Summable (zzF lam X H))
    (hz : Summable (zz lam X H)) :
    Summable (fun m : ℕ => zzF lam X H (m, m)) ∧
      ∑' q, zzF lam X H q = ∑' q, zz lam X H q + ∑' m : ℕ, zzF lam X H (m, m) := by
  set dg : ℕ × ℕ → ℂ := fun q => if q.1 = q.2 then zzF lam X H q else 0 with hdg
  have hpt : ∀ q, zzF lam X H q = zz lam X H q + dg q := by
    intro q
    simp only [hdg]
    by_cases hq : q.1 = q.2
    · rw [if_pos hq]; unfold zz; rw [if_pos hq, zero_add]
    · rw [if_neg hq, zzF_off X H hq, add_zero]
  have hsd : Summable dg := (hs.sub hz).congr fun q => by rw [hpt q]; ring
  set d : ℕ → ℕ × ℕ := fun m => (m, m) with hd
  have hdinj : Function.Injective d := fun a b hab => by simpa [hd] using congrArg Prod.fst hab
  have hsupp : Function.support dg ⊆ Set.range d := by
    intro q hq
    rw [Function.mem_support] at hq
    simp only [hdg] at hq
    split_ifs at hq with h1
    · exact ⟨q.1, by simp only [hd]; ext <;> simp [h1]⟩
    · exact absurd rfl hq
  have hdd : ∀ m, dg (d m) = zzF lam X H (m, m) := fun m => by simp [hdg, hd]
  refine ⟨(hsd.comp_injective hdinj).congr hdd, ?_⟩
  rw [tsum_congr hpt, hz.tsum_add hsd, ← hdinj.tsum_eq hsupp]
  simp_rw [hdd]

lemma sqrt_le_self' {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

set_option maxHeartbeats 3200000 in
/-- **The symmetrised twisted second moment, unconditionally.** -/
theorem twisted_moment : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h k : ℕ), 1 ≤ h → 1 ≤ k → ∀ X : ℝ, 2 ^ (300 : ℕ) ≤ X →
    ‖TwAv h k X (X ^ (299 / 300 : ℝ)) - MainTw h k X (X ^ (299 / 300 : ℝ))‖ ≤
      C * ((h * k : ℕ) : ℝ) ^ 33 * X ^ (599 / 600 : ℝ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := gavgOff_le
  obtain ⟨CE, hCE0, hCE⟩ := delta_afe
  have hA := Arank_nonneg
  have hCs := Cscs_nonneg
  refine ⟨C₀ * (4 * (Arank + Cscs + 1)) + 8 * CE, by positivity, fun h k hh hk X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hX
  have hX16 : (16 : ℝ) ≤ X := le_trans (by
    calc (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
      _ ≤ 2 ^ (300 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)) hX
  set S := Ssz h k with hSdef
  have hS := Ssz_pos hh hk
  set r : ℝ := (Real.sqrt S)⁻¹ with hrdef
  have hr0 : r ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hS).ne'
  have hr2 : r ^ 2 = S⁻¹ := by rw [hrdef, inv_pow, Real.sq_sqrt hS.le]
  have hrS : r ^ 2 * S ≤ 1 := by rw [hr2, inv_mul_cancel₀ hS.ne']
  letI ip : GoodSeq (gS h k 1 r) := goodSeq_gS hh hk (by norm_num) hrS
  letI im : GoodSeq (gS h k (-1) r) := goodSeq_gS hh hk (by norm_num) hrS
  set c := Real.log ((h * k : ℕ) : ℝ) with hc
  have hcp : GoodSeq.c (gS h k 1 r) = c := rfl
  have hcm : GoodSeq.c (gS h k (-1) r) = c := rfl
  have hgp : ∀ n, gS h k 1 r n ^ 2 ≤ C1 * n := sq_le_of_sum GoodSeq.zero GoodSeq.rankin
  have hgm : ∀ n, gS h k (-1) r n ^ 2 ≤ C1 * n := sq_le_of_sum GoodSeq.zero GoodSeq.rankin
  obtain ⟨hzp, hbp⟩ := hC₀ (gS h k 1 r) X X hX hX16 le_rfl
  obtain ⟨hzm, hbm⟩ := hC₀ (gS h k (-1) r) X X hX hX16 le_rfl
  clear hX
  have hX0 : (0 : ℝ) < X := by linarith
  set H := X ^ (299 / 300 : ℝ) with hH
  have hH0 : 0 < H := by positivity
  have hHX : H ≤ X := by
    calc H ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      _ = X := Real.rpow_one X
  set T' := X + H with hT'
  set Sp : ℝ → ℂ := fun t => ∑' q, bG2 (gS h k 1 r) (gS h k 1 r) c t q with hSp
  set Sm : ℝ → ℂ := fun t => ∑' q, bG2 (gS h k (-1) r) (gS h k (-1) r) c t q with hSm
  set K : ℂ := ((Real.sqrt ((h * k : ℕ) : ℝ) / (2 * r ^ 2) : ℝ) : ℂ) with hK
  set Fs : ℝ → ℂ := fun t => ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) * (ph h k t + ph k h t) with hFs
  set Er : ℝ → ℂ := fun t => Fs t - K * (Sp t - Sm t) with hEr
  have hSpc : ContinuousOn Sp (Icc 16 T') := continuousOn_S (gS h k 1 r) T'
  have hSmc : ContinuousOn Sm (Icc 16 T') := continuousOn_S (gS h k (-1) r) T'
  have hFsc : ContinuousOn Fs (Icc 16 T') := by
    refine Continuous.continuousOn ?_
    have h1 := continuous_zsqD
    unfold zsqD at h1
    exact (Complex.continuous_ofReal.comp h1).mul ((continuous_ph h k).add (continuous_ph k h))
  have hErc : ContinuousOn Er (Icc 16 T') := hFsc.sub (continuousOn_const.mul (hSpc.sub hSmc))
  -- decomposition
  have hdec : TwAv h k X H = K * Av X H Sp + (-K) * Av X H Sm + Av X H Er := by
    unfold TwAv
    have e : (fun t : ℝ => ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) * (ph h k t + ph k h t)) =
        fun t : ℝ => K * Sp t + (-K) * Sm t + Er t := by
      funext t; simp only [hEr, hFs]; ring
    rw [e, Av_add (F := fun t => K * Sp t + (-K) * Sm t) (G := Er) hX16 hH0
        ((continuousOn_const.mul hSpc).add (continuousOn_const.mul hSmc)) hErc,
      Av_add (F := fun t => K * Sp t) (G := fun t => (-K) * Sm t) hX16 hH0
        (continuousOn_const.mul hSpc) (continuousOn_const.mul hSmc), Av_smul, Av_smul]
  obtain ⟨hFp, hAp⟩ := gavg_eq (lam := gS h k 1 r) hX16 hH0
  obtain ⟨hFm, hAm⟩ := gavg_eq (lam := gS h k (-1) r) hX16 hH0
  have hAvp : Av X H Sp = ∑' q, zzF (gS h k 1 r) X H q := hAp
  have hAvm : Av X H Sm = ∑' q, zzF (gS h k (-1) r) X H q := hAm
  obtain ⟨hdp, hsp⟩ := tsum_zzF_split (gS h k 1 r) hFp hzp
  obtain ⟨hdm, hsm⟩ := tsum_zzF_split (gS h k (-1) r) hFm hzm
  -- the diagonal is the main term
  have hmain : K * (∑' m : ℕ, zzF (gS h k 1 r) X H (m, m)) + (-K) * (∑' m : ℕ, zzF (gS h k (-1) r) X H (m, m)) =
      MainTw h k X H := by
    rw [neg_mul, ← sub_eq_add_neg, ← mul_sub, ← hdp.tsum_sub hdm]
    unfold MainTw
    rw [← tsum_mul_left, ← tsum_mul_left]
    congr 1; funext m
    unfold zzF coefG
    rw [hcp, hcm]
    unfold gS
    rw [hK]
    have hr2' : (r : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr0
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    try dsimp only
    try rw [← hc]
    push_cast
    field_simp
    ring
  have hfin : TwAv h k X H - MainTw h k X H =
      K * ∑' q, zz (gS h k 1 r) X H q + (-K) * ∑' q, zz (gS h k (-1) r) X H q + Av X H Er := by
    rw [hdec, hAvp, hAvm, hsp, hsm, ← hmain]; ring
  -- the AFE error
  have hErb : ∀ t, 16 ≤ t → ‖Er t‖ ≤ 2 * CE * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have hp := twist_pointwise hh hk hr0 hgp hgm ht
    have e : Er t = (((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) - ∑' p, bD t (2 * ellT t) p) * (ph h k t + ph k h t) := by
      simp only [hEr, hFs, hSp, hSm, hK]
      rw [sub_mul, hp, ← hc]
    rw [e, norm_mul]
    have h1 : ‖((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) - ∑' p, bD t (2 * ellT t) p‖ ≤ CE * t ^ (-(1 / 2 : ℝ)) :=
      hCE t ht
    have h2 : ‖ph h k t + ph k h t‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_ph, norm_ph]; norm_num
    have h3 : 0 ≤ CE * t ^ (-(1 / 2 : ℝ)) := by positivity
    calc _ ≤ CE * t ^ (-(1 / 2 : ℝ)) * 2 := mul_le_mul h1 h2 (norm_nonneg _) h3
      _ = _ := by ring
  have hp1 : (1 : ℝ) ≤ X ^ (599 / 600 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hAvEr : ‖Av X H Er‖ ≤ 8 * CE * X ^ (599 / 600 : ℝ) := by
    refine norm_Av_le hH0 fun u hu => ?_
    have h16u : 16 ≤ u := by linarith [hu.1]
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => 2 * CE * t ^ (-(1 / 2 : ℝ))) h16u
      (Eventually.of_forall fun t ht => hErb t ht.1.le) ?_).trans ?_
    · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl ((show (0:ℝ) < x by linarith [hx.1]).ne')))) |>.intervalIntegrable_of_Icc
          (μ := volume) h16u
    · rw [intervalIntegral.integral_const_mul]
      have h1 := integral_rpow_le' (e := -(1 / 2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 16) h16u
      have h3 : u ^ (-(1 / 2 : ℝ) + 1) / (-(1 / 2 : ℝ) + 1) = 2 * u ^ (-(1 / 2 : ℝ) + 1) := by ring
      rw [h3] at h1
      have hu2 : u ≤ 2 * X := by linarith [hu.2]
      have h4 : u ^ (-(1 / 2 : ℝ) + 1) ≤ 2 * X ^ (599 / 600 : ℝ) := by
        calc u ^ (-(1 / 2 : ℝ) + 1) ≤ u ^ (599 / 600 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ ≤ (2 * X) ^ (599 / 600 : ℝ) := Real.rpow_le_rpow (by linarith) hu2 (by norm_num)
          _ = 2 ^ (599 / 600 : ℝ) * X ^ (599 / 600 : ℝ) := Real.mul_rpow (by norm_num) hX0.le
          _ ≤ 2 * X ^ (599 / 600 : ℝ) := by
              gcongr
              calc (2 : ℝ) ^ (599 / 600 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      calc 2 * CE * ∫ t in (16 : ℝ)..u, t ^ (-(1 / 2 : ℝ)) ≤ 2 * CE * (2 * u ^ (-(1 / 2 : ℝ) + 1)) := by gcongr
        _ ≤ 2 * CE * (2 * (2 * X ^ (599 / 600 : ℝ))) := by gcongr
        _ = 8 * CE * X ^ (599 / 600 : ℝ) := by ring
  -- the off-diagonal
  set W : ℝ := ((h * k : ℕ) : ℝ) with hW
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have he8 : Real.exp (8 * c) = W ^ 8 := by
    rw [hc, show (8 : ℝ) * Real.log W = Real.log (W ^ 8) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [hcp] at hbp
  rw [hcm] at hbm
  rw [he8] at hbp hbm
  have hKn : ‖K‖ = Real.sqrt W * S / 2 := by
    rw [hK, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hr2]
    field_simp
  rw [hfin]
  have hsq := sqrt_le_self' hW1
  have hW33 : 1 ≤ W ^ 33 := one_le_pow₀ hW1
  have hp0 : 0 ≤ X ^ (599 / 600 : ℝ) := by positivity
  calc ‖K * ∑' q, zz (gS h k 1 r) X H q + (-K) * ∑' q, zz (gS h k (-1) r) X H q + Av X H Er‖
      ≤ ‖K‖ * ‖∑' q, zz (gS h k 1 r) X H q‖ + ‖K‖ * ‖∑' q, zz (gS h k (-1) r) X H q‖ + ‖Av X H Er‖ := by
        have e1 : ‖K * ∑' q, zz (gS h k 1 r) X H q + (-K) * ∑' q, zz (gS h k (-1) r) X H q + Av X H Er‖ ≤
            ‖K * ∑' q, zz (gS h k 1 r) X H q‖ + ‖(-K) * ∑' q, zz (gS h k (-1) r) X H q‖ + ‖Av X H Er‖ :=
          norm_add₃_le
        rw [norm_mul, norm_mul, norm_neg] at e1
        exact e1
    _ ≤ ‖K‖ * (C₀ * W ^ 8 * X ^ (599 / 600 : ℝ)) + ‖K‖ * (C₀ * W ^ 8 * X ^ (599 / 600 : ℝ)) +
        8 * CE * X ^ (599 / 600 : ℝ) := by gcongr
    _ = C₀ * (4 * (Arank + Cscs + 1)) * (Real.sqrt W * W ^ 32) * X ^ (599 / 600 : ℝ) +
        8 * CE * X ^ (599 / 600 : ℝ) := by
        rw [hKn, hSdef]; unfold Ssz; rw [← hW]; ring
    _ ≤ C₀ * (4 * (Arank + Cscs + 1)) * W ^ 33 * X ^ (599 / 600 : ℝ) +
        8 * CE * W ^ 33 * X ^ (599 / 600 : ℝ) := by
        have h1 : Real.sqrt W * W ^ 32 ≤ W ^ 33 := by
          calc Real.sqrt W * W ^ 32 ≤ W * W ^ 32 := by gcongr
            _ = W ^ 33 := by ring
        have h2 : 8 * CE * X ^ (599 / 600 : ℝ) ≤ 8 * CE * W ^ 33 * X ^ (599 / 600 : ℝ) := by
          have : 0 ≤ 8 * CE * X ^ (599 / 600 : ℝ) := by positivity
          nlinarith
        have h3 : 0 ≤ C₀ * (4 * (Arank + Cscs + 1)) := by positivity
        gcongr
    _ = _ := by ring

end RamanujanTau.TwistedMoment
