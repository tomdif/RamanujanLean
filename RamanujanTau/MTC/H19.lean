/-
# HM (1.9) as an element of `Th(Q³⁰, 10, Q⁻¹⁰⁵)`

`F(x) = J̄_{5,20} j(−Q⁶x;Q³⁰) j(−Q³x³;Q³⁰) − Q² x² J̄_{30,120} j(−Qx;Q⁵) j(−Q²⁷x²;Q³⁰)
        − j(Q²x²;Q²⁰) j(Q⁶x;Q¹⁵) j(Q¹²x²;Q⁶⁰)`  (`Q = t^{168}`)

as a coefficient sequence in `x`: each theta is `thS` at its own base, `x ↦ x^d` is `subst`, products are `conv`.
`F19_mem`: `F ∈ Th 5040 10 (Q⁻¹⁰⁵)`; `ev_F19`: its value at `x = c t^e` as theta products.
-/
import RamanujanTau.MTC.ThExtra
import RamanujanTau.MTC.Final0

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma h5040 : 1 ≤ 5040 := by norm_num
lemma h2520 : 1 ≤ 2520 := by norm_num
lemma h10080 : 1 ≤ 10080 := by norm_num

lemma mono_pow' (E : ℤ) (c : ℂ) (k : ℕ) : (mono E c : L) ^ k = mono (k * E) (c ^ k) := by
  show (single E c : L) ^ k = single ((k : ℤ) * E) (c ^ k)
  rw [single_pow, nsmul_eq_mul]

noncomputable def sa1 : ℤ → L := thS (NQ := 5040) (-1008) (-1)
noncomputable def sa2 : ℤ → L := MTC.subst (thS (NQ := 5040) (-504) (-1)) 3 0 1
noncomputable def sb1 : ℤ → L := thS (NQ := 840) (-168) (-1)
noncomputable def sb2 : ℤ → L := MTC.subst (thS (NQ := 5040) (-4536) (-1)) 2 0 1
noncomputable def sc1 : ℤ → L := MTC.subst (thS (NQ := 3360) (-336) 1) 2 0 1
noncomputable def sc2 : ℤ → L := thS (NQ := 2520) (-1008) 1
noncomputable def sc3 : ℤ → L := MTC.subst (thS (NQ := 10080) (-2016) 1) 2 0 1

noncomputable def T1s : ℤ → L := B20 5 • MTC.conv sa1 sa2
noncomputable def T2s : ℤ → L := (mono 336 1 * θ h20160 5040 (-1)) • shiftS (MTC.conv sb1 sb2) (-2)
noncomputable def T3s : ℤ → L := MTC.conv (MTC.conv sc1 sc2) sc3
noncomputable def F19 : ℤ → L := T1s - T2s - T3s

/-! ## Membership -/

lemma n1 : (-1 : ℂ) ≠ 0 := by norm_num

lemma sa1_mem : sa1 ∈ Th 5040 1 (mono (-1008) 1) :=
  Th.congr_μ (by rw [neg_neg]) (thS_mem (NQ := 5040) (-1008) n1)

lemma sa2_mem : sa2 ∈ Th 5040 9 (mono (-16632) 1) := by
  have h0 := thS_mem (NQ := 5040) (-504) n1
  have h1 := Th.subst (d := 3) (N := 1680) (m := 1) (by norm_num) h0
  have h2 := Th.base_mul h1 3
  exact Th.congr_μ (by rw [neg_neg, mono_pow', mono_mul]; exact mono_ext (by norm_num [c2]) (by norm_num)) h2

lemma sb1_mem : sb1 ∈ Th 5040 6 (mono (-13608) 1) := by
  have h0 := thS_mem (NQ := 840) (-168) n1
  have h2 := Th.base_mul h0 6
  exact Th.congr_μ (by rw [neg_neg, mono_pow', mono_mul]; exact mono_ext (by norm_num [c2]) (by norm_num)) h2

lemma sb2_mem : sb2 ∈ Th 5040 4 (mono (-14112) 1) := by
  have h0 := thS_mem (NQ := 5040) (-4536) n1
  have h1 := Th.subst (d := 2) (N := 2520) (m := 1) (by norm_num) h0
  have h2 := Th.base_mul h1 2
  exact Th.congr_μ (by rw [neg_neg, mono_pow', mono_mul]; exact mono_ext (by norm_num [c2]) (by norm_num)) h2

lemma sc1_mem : sc1 ∈ Th 5040 6 (mono (-11088) (-1)) := by
  have h0 := thS_mem (NQ := 3360) (-336) one_ne_zero
  have h1 := Th.subst (d := 2) (N := 1680) (m := 1) (by norm_num) h0
  have h2 := Th.base_mul h1 3
  exact Th.congr_μ (by rw [mono_pow', mono_mul]; exact mono_ext (by norm_num [c2]) (by norm_num)) h2

lemma sc2_mem : sc2 ∈ Th 5040 2 (mono (-4536) 1) := by
  have h0 := thS_mem (NQ := 2520) (-1008) one_ne_zero
  have h2 := Th.base_mul h0 2
  exact Th.congr_μ (by rw [mono_pow', mono_mul]; exact mono_ext (by norm_num [c2]) (by norm_num)) h2

lemma sc3_mem : sc3 ∈ Th 5040 2 (mono (-2016) (-1)) := by
  have h0 := thS_mem (NQ := 10080) (-2016) one_ne_zero
  exact Th.subst (d := 2) (N := 5040) (m := 1) (by norm_num) h0

lemma T1_mem : T1s ∈ Th 5040 10 (mono (-17640) 1) := by
  have h := conv_mem h5040 le_rfl (by norm_num) one_ne_zero one_ne_zero sa1_mem sa2_mem
  exact Submodule.smul_mem _ _ (Th.congr_μ (by exact mono_ext (by norm_num) (by norm_num)) h)

lemma T2_mem : T2s ∈ Th 5040 10 (mono (-17640) 1) := by
  have h := conv_mem h5040 (by norm_num) (by norm_num) one_ne_zero one_ne_zero sb1_mem sb2_mem
  have h' := Th.shift_mem h 2
  exact Submodule.smul_mem _ _ (Th.congr_μ (by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)) h')

lemma T3_mem : T3s ∈ Th 5040 10 (mono (-17640) 1) := by
  have h := conv_mem h5040 (by norm_num) (by norm_num) n1 one_ne_zero sc1_mem sc2_mem
  have h' := conv_mem h5040 (by norm_num) (by norm_num) (mul_ne_zero n1 one_ne_zero) n1 h sc3_mem
  exact Th.congr_μ (by exact mono_ext (by norm_num) (by norm_num)) h'

theorem F19_mem : F19 ∈ Th 5040 10 (mono (-17640) 1) :=
  Submodule.sub_mem _ (Submodule.sub_mem _ T1_mem T2_mem) T3_mem

/-! ## Values -/

lemma ent_thS {N : ℕ} (hN : 1 ≤ N) (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0) : Ent (thS (NQ := N) ep cp) :=
  Th.ent le_rfl (neg_ne_zero.mpr hcp) hN (thS_mem ep hcp)

lemma Ea1 : Ent sa1 := ent_thS h5040 _ n1
lemma Ea2 : Ent sa2 := (ent_thS h5040 _ n1).subst (by norm_num) 0 1
lemma Eb1 : Ent sb1 := ent_thS h840 _ n1
lemma Eb2 : Ent sb2 := (ent_thS h5040 _ n1).subst (by norm_num) 0 1
lemma Ec1 : Ent sc1 := (ent_thS h3360 _ one_ne_zero).subst (by norm_num) 0 1
lemma Ec2 : Ent sc2 := ent_thS h2520 _ one_ne_zero
lemma Ec3 : Ent sc3 := (ent_thS h10080 _ one_ne_zero).subst (by norm_num) 0 1

lemma ET1 : Ent T1s := (Ea1.conv Ea2).smul _
lemma ET2 : Ent T2s := ((Eb1.conv Eb2).shift _).smul _
lemma ET3 : Ent T3s := (Ec1.conv Ec2).conv Ec3

lemma ev_T1 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T1s e c = B20 5 * (θ h5040 (e - -1008) (c / -1) * θ h5040 (0 + 3 * e - -504) (1 * c ^ (3 : ℤ) / -1)) := by
  rw [show T1s = fun k => B20 5 * MTC.conv sa1 sa2 k from rfl, ev_smul (Ea1.conv Ea2), ev_conv Ea1 Ea2 _ hc]
  unfold sa1 sa2
  rw [thS_ev h5040, ev_subst (ent_thS h5040 _ n1) (by norm_num), thS_ev h5040]
  all_goals norm_num

lemma ev_T2 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T2s e c = mono 336 1 * θ h20160 5040 (-1) * (mono (-(e * -2)) (c ^ (-(-2 : ℤ))) *
      (θ h840 (e - -168) (c / -1) * θ h5040 (0 + 2 * e - -4536) (1 * c ^ (2 : ℤ) / -1))) := by
  rw [show T2s = fun k => (mono 336 1 * θ h20160 5040 (-1)) * shiftS (MTC.conv sb1 sb2) (-2) k from rfl,
    ev_smul ((Eb1.conv Eb2).shift _), ev_shift (Eb1.conv Eb2) _ _ hc, ev_conv Eb1 Eb2 _ hc]
  unfold sb1 sb2
  rw [thS_ev h840, ev_subst (ent_thS h5040 _ n1) (by norm_num), thS_ev h5040]
  all_goals norm_num

lemma ev_T3 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T3s e c = θ h3360 (0 + 2 * e - -336) (1 * c ^ (2 : ℤ) / 1) * θ h2520 (e - -1008) (c / 1) *
      θ h10080 (0 + 2 * e - -2016) (1 * c ^ (2 : ℤ) / 1) := by
  rw [show T3s = MTC.conv (MTC.conv sc1 sc2) sc3 from rfl, ev_conv (Ec1.conv Ec2) Ec3 _ hc, ev_conv Ec1 Ec2 _ hc]
  unfold sc1 sc2 sc3
  rw [ev_subst (ent_thS h3360 _ one_ne_zero) (by norm_num), thS_ev h3360, thS_ev h2520,
    ev_subst (ent_thS h10080 _ one_ne_zero) (by norm_num), thS_ev h10080]
  all_goals norm_num

lemma ev_F19 (e : ℤ) {c : ℂ} (hc : c ≠ 0) : ev F19 e c = ev T1s e c - ev T2s e c - ev T3s e c := by
  rw [show F19 = T1s - T2s - T3s from rfl, ev_sub (ET1.sub ET2) ET3, ev_sub ET1 ET2]

end MTC
