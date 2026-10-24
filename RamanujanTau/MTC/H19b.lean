/-
# HM (1.9) by counting zeros, and HM (8.17)

`F19 ∈ Th(Q³⁰, 10)` vanishes at the eleven inequivalent points
`x = −Q⁹, −Q¹⁹, −Q²⁴, −Q²⁹` (every term has a vanishing theta factor),
`x = Q⁹, Q¹⁹, Q²⁴, Q²⁹` (`j(Q⁶x;Q¹⁵)` or `j(Q²x²;Q²⁰)` vanishes; the other two terms agree by
`j(−1;q) = 2 j(−q;q⁴)` and quasi-periodicity), `x = −Q⁴, −Q¹⁴` (`j(−Qx;Q⁵) = 0`; a product identity) and
`x = iQ^{3/2}` (`j(−Q²⁷x²;Q³⁰) = 0`; HM (1.4b) and a 2-dissection), hence `F19 = 0` (`F19_zero`).
At `x = 1` this is (8.17) (`E817_holds`), so the first mock theta conjecture holds (`mtc0`).
-/
import RamanujanTau.MTC.H19

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

lemma θz {N : ℕ} (h : 1 ≤ N) (m : ℤ) {e : ℤ} {c : ℂ} (he : e = N * m) (hc : c = 1) : θ h e c = 0 := by
  subst hc; rw [he]; exact θ_qpow h m

/-- quasi-periodicity with prescribed normal form. -/
lemma θ_red {N : ℕ} (h : 1 ≤ N) (e e0 : ℤ) (k : ℕ) {c : ℂ} (hc : c ≠ 0) (E : ℤ) (C : ℂ) (he : e = e0 + N * k)
    (hE : E = -(k * e0) - N * c2 k) (hC : C = (-1) ^ k * c ^ (-(k : ℤ))) : θ h e c = mono E C * θ h e0 c := by
  rw [he, θ_shk h e0 hc k, hE, hC]

lemma ev_T1' (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T1s e c = B20 5 * (θ h5040 (e + 1008) (-c) * θ h5040 (3 * e + 504) (-c ^ 3)) := by
  rw [ev_T1 e hc, θ_cg' h5040 (show e - -1008 = e + 1008 by ring) (show c / -1 = -c by ring),
    θ_cg' h5040 (show (0 : ℤ) + 3 * e - -504 = 3 * e + 504 by ring)
      (show 1 * c ^ (3 : ℤ) / -1 = -c ^ 3 by rw [zpow_ofNat]; ring)]

lemma ev_T2' (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T2s e c = mono 336 1 * θ h20160 5040 (-1) * (mono (2 * e) (c ^ 2) *
      (θ h840 (e + 168) (-c) * θ h5040 (2 * e + 4536) (-c ^ 2))) := by
  rw [ev_T2 e hc, θ_cg' h840 (show e - -168 = e + 168 by ring) (show c / -1 = -c by ring),
    θ_cg' h5040 (show (0 : ℤ) + 2 * e - -4536 = 2 * e + 4536 by ring)
      (show 1 * c ^ (2 : ℤ) / -1 = -c ^ 2 by rw [zpow_ofNat]; ring),
    mono_ext_x (show -(e * -2) = 2 * e by ring) (show c ^ (-(-2 : ℤ)) = c ^ 2 by rw [neg_neg, zpow_ofNat])]

lemma ev_T3' (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev T3s e c = θ h3360 (2 * e + 336) (c ^ 2) * θ h2520 (e + 1008) c * θ h10080 (2 * e + 2016) (c ^ 2) := by
  rw [ev_T3 e hc, θ_cg' h3360 (show (0 : ℤ) + 2 * e - -336 = 2 * e + 336 by ring)
      (show 1 * c ^ (2 : ℤ) / 1 = c ^ 2 by rw [zpow_ofNat]; ring),
    θ_cg' h2520 (show e - -1008 = e + 1008 by ring) (show c / 1 = c by ring),
    θ_cg' h10080 (show (0 : ℤ) + 2 * e - -2016 = 2 * e + 2016 by ring)
      (show 1 * c ^ (2 : ℤ) / 1 = c ^ 2 by rw [zpow_ofNat]; ring)]

/-- `J̄_{0,30} = 2 J̄_{30,120}`. -/
lemma hX : θ h5040 0 (-1) = 2 * θ h20160 5040 (-1) := by
  rw [θbar0 h5040, θ_N' (by norm_num) _ h20160]
  norm_num

/-- `J̄_{0,5} = 2 J̄_{5,20}`. -/
lemma hY : θ h840 0 (-1) = 2 * B20 5 := by
  rw [θbar0 h840, θ_N' (by norm_num) _ h3360]
  unfold B20
  norm_num

lemma mono1 (E : ℤ) (h : E = 0) : (mono E 1 : L) = 1 := by rw [h]; rfl

/-! ## The trivial zeros -/

theorem z1 : ev F19 1512 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h5040 1 (e := 3 * 1512 + 504) (c := -(-1) ^ 3) (by norm_num) (by norm_num),
    θz h840 2 (e := 1512 + 168) (c := -(-1)) (by norm_num) (by norm_num),
    θz h3360 1 (e := 2 * 1512 + 336) (c := (-1) ^ 2) (by norm_num) (by norm_num)]
  ring

theorem z2 : ev F19 3192 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h5040 2 (e := 3 * 3192 + 504) (c := -(-1) ^ 3) (by norm_num) (by norm_num),
    θz h840 4 (e := 3192 + 168) (c := -(-1)) (by norm_num) (by norm_num),
    θz h3360 2 (e := 2 * 3192 + 336) (c := (-1) ^ 2) (by norm_num) (by norm_num)]
  ring

theorem z3 : ev F19 4032 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h5040 1 (e := 4032 + 1008) (c := -(-1)) (by norm_num) (by norm_num),
    θz h840 5 (e := 4032 + 168) (c := -(-1)) (by norm_num) (by norm_num),
    θz h10080 1 (e := 2 * 4032 + 2016) (c := (-1) ^ 2) (by norm_num) (by norm_num)]
  ring

theorem z4 : ev F19 4872 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h5040 3 (e := 3 * 4872 + 504) (c := -(-1) ^ 3) (by norm_num) (by norm_num),
    θz h840 6 (e := 4872 + 168) (c := -(-1)) (by norm_num) (by norm_num),
    θz h3360 3 (e := 2 * 4872 + 336) (c := (-1) ^ 2) (by norm_num) (by norm_num)]
  ring

/-! ## `x = Q⁹, Q¹⁹, Q²⁴, Q²⁹` -/

theorem z5 : ev F19 1512 1 = 0 := by
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero,
    θz h2520 1 (e := 1512 + 1008) (c := 1) (by norm_num) rfl,
    θ_red h5040 (3 * 1512 + 504) 0 1 (c := -1 ^ 3) (by norm_num) 0 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h840 (1512 + 168) 0 2 (c := -1) n1 (-840) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h5040 (2 * 1512 + 4536) 2520 1 (c := -1 ^ 2) (by norm_num) (-2520) 1 (by norm_num) (by norm_num [c2])
      (by norm_num)]
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (1512 : ℤ) + 1008 = 2520 by norm_num, hX, hY]
  have e : (mono 336 1 : L) * mono (2 * 1512) 1 * mono (-840) 1 * mono (-2520) 1 = 1 := by
    simp only [mono_mul]; rw [show (1 : L) = mono 0 1 from rfl]; exact mono_ext_x (by norm_num) (by norm_num)
  rw [mono1 0 rfl]
  linear_combination (-(2 * B20 5 * θ h20160 5040 (-1) * θ h5040 2520 (-1))) * e

theorem z6 : ev F19 3192 1 = 0 := by
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero,
    θz h3360 2 (e := 2 * 3192 + 336) (c := 1 ^ 2) (by norm_num) (by norm_num),
    θ_red h5040 (3 * 3192 + 504) 0 2 (c := -1 ^ 3) (by norm_num) (-5040) 1 (by norm_num) (by norm_num [c2])
      (by norm_num),
    θ_red h840 (3192 + 168) 0 4 (c := -1) n1 (-5040) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h5040 (2 * 3192 + 4536) 840 2 (c := -1 ^ 2) (by norm_num) (-6720) 1 (by norm_num) (by norm_num [c2])
      (by norm_num)]
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (3192 : ℤ) + 1008 = ((5040 : ℕ) : ℤ) - 840 by norm_num, refl_m h5040, hX, hY]
  have e : (mono 336 1 : L) * mono (2 * 3192) 1 * mono (-5040) 1 * mono (-6720) 1 = mono (-5040) 1 := by
    simp only [mono_mul]; exact mono_ext_x (by norm_num) (by norm_num)
  linear_combination (-(2 * B20 5 * θ h20160 5040 (-1) * θ h5040 840 (-1))) * e

theorem z7 : ev F19 4032 1 = 0 := by
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero,
    θz h2520 2 (e := 4032 + 1008) (c := 1) (by norm_num) rfl,
    θ_red h5040 (4032 + 1008) 0 1 (c := -1) n1 0 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h840 (4032 + 168) 0 5 (c := -1) n1 (-8400) 1 (by norm_num) (by norm_num [c2]) (by norm_num)]
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (3 : ℤ) * 4032 + 504 = 2 * 4032 + 4536 by norm_num, hX, hY, mono1 0 rfl]
  have e : (mono 336 1 : L) * mono (2 * 4032) 1 * mono (-8400) 1 = 1 := by
    simp only [mono_mul]; rw [show (1 : L) = mono 0 1 from rfl]; exact mono_ext_x (by norm_num) (by norm_num)
  linear_combination (-(2 * B20 5 * θ h20160 5040 (-1) * θ h5040 (2 * 4032 + 4536) (-1))) * e

theorem z8 : ev F19 4872 1 = 0 := by
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero,
    θz h3360 3 (e := 2 * 4872 + 336) (c := 1 ^ 2) (by norm_num) (by norm_num),
    θ_red h5040 (4872 + 1008) 840 1 (c := -1) n1 (-840) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h5040 (3 * 4872 + 504) 0 3 (c := -1 ^ 3) (by norm_num) (-15120) 1 (by norm_num) (by norm_num [c2])
      (by norm_num),
    θ_red h840 (4872 + 168) 0 6 (c := -1) n1 (-12600) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h5040 (2 * 4872 + 4536) 4200 2 (c := -1 ^ 2) (by norm_num) (-13440) 1 (by norm_num) (by norm_num [c2])
      (by norm_num)]
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (4200 : ℤ) = ((5040 : ℕ) : ℤ) - 840 by norm_num, refl_m h5040, hX, hY]
  have e : (mono 336 1 : L) * mono (2 * 4872) 1 * mono (-12600) 1 * mono (-13440) 1 =
      mono (-840) 1 * mono (-15120) 1 := by
    simp only [mono_mul]; exact mono_ext_x (by norm_num) (by norm_num)
  linear_combination (-(2 * B20 5 * θ h20160 5040 (-1) * θ h5040 840 (-1))) * e

/-! ## `x = −Q⁴, −Q¹⁴` -/

/-- `J̄_{5,20} J_{10,30} J_{15,30} = J_{10,20} J̄_{10,15} J_{20,60}`. -/
theorem P9 : B20 5 * θ h5040 1680 1 * θ h5040 2520 1 = θ h3360 1680 1 * θ h2520 1680 (-1) * θ h10080 3360 1 := by
  unfold B20
  rw [θb h168 h3360 20 5 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h5040 30 10 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h5040 30 15 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 10 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h2520 15 10 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h10080 60 20 2 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 120 ≠ 0 := fun r hr => PA_ne h168 r 120 hr (by norm_num)
  field_simp [hP]

/-- `J̄_{5,20} J_{20,30} J_{15,30} = J_{10,20} J̄_{5,15} J_{40,60}`. -/
theorem P10 : B20 5 * θ h5040 3360 1 * θ h5040 2520 1 = θ h3360 1680 1 * θ h2520 840 (-1) * θ h10080 6720 1 := by
  unfold B20
  rw [θb h168 h3360 20 5 3 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h5040 30 20 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h5040 30 15 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h3360 20 10 6 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h2520 15 5 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h10080 60 40 2 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 120 ≠ 0 := fun r hr => PA_ne h168 r 120 hr (by norm_num)
  field_simp [hP]

theorem z9 : ev F19 672 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h840 1 (e := 672 + 168) (c := -(-1)) (by norm_num) (by norm_num)]
  rw [show (-(-1 : ℂ)) = 1 by norm_num, show (-(-1 : ℂ) ^ 3) = 1 by norm_num, show ((-1 : ℂ)) ^ 2 = 1 by norm_num,
    show (672 : ℤ) + 1008 = 1680 by norm_num, show (3 : ℤ) * 672 + 504 = 2520 by norm_num,
    show (2 : ℤ) * 672 + 336 = 1680 by norm_num, show (2 : ℤ) * 672 + 2016 = 3360 by norm_num]
  linear_combination P9

theorem z10 : ev F19 2352 (-1) = 0 := by
  rw [ev_F19 _ n1, ev_T1' _ n1, ev_T2' _ n1, ev_T3' _ n1,
    θz h840 3 (e := 2352 + 168) (c := -(-1)) (by norm_num) (by norm_num)]
  rw [show (-(-1 : ℂ)) = 1 by norm_num, show (-(-1 : ℂ) ^ 3) = 1 by norm_num, show ((-1 : ℂ)) ^ 2 = 1 by norm_num,
    θ_red h5040 (3 * 2352 + 504) 2520 1 one_ne_zero (-2520) (-1) (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h3360 (2 * 2352 + 336) 1680 1 one_ne_zero (-1680) (-1) (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_red h2520 (2352 + 1008) 840 1 n1 (-840) 1 (by norm_num) (by norm_num [c2]) (by norm_num),
    show (2352 : ℤ) + 1008 = 3360 by norm_num, show (2 : ℤ) * 2352 + 2016 = 6720 by norm_num]
  have e : (mono (-1680) (-1) : L) * mono (-840) 1 = mono (-2520) (-1) := by
    rw [mono_mul]; exact mono_ext_x (by norm_num) (by norm_num)
  linear_combination (mono (-2520) (-1) : L) * P10 -
    (θ h3360 1680 1 * θ h2520 840 (-1) * θ h10080 6720 1) * e

/-! ## `x = i Q^{3/2}` -/

theorem z11 : ev F19 252 Complex.I = 0 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [ev_F19 _ hI, ev_T1' _ hI, ev_T2' _ hI, ev_T3' _ hI,
    θz h5040 1 (e := 2 * 252 + 4536) (c := -Complex.I ^ 2) (by norm_num) (by simp)]
  have hm := θ_mul h5040 1260 1260 (c1 := -Complex.I) (c2 := Complex.I) (neg_ne_zero.mpr hI) hI
  have hq : θ (h2N h5040) (2 * ((5040 : ℕ) : ℤ) + 1260 - 1260) (-(-Complex.I / Complex.I)) = 0 :=
    θz (h2N h5040) 1 (by norm_num) (by rw [neg_div, neg_neg, div_self hI])
  rw [hq, mul_zero, mul_zero, sub_zero, θ_cg' (h2N h5040) (show (1260 + 1260 : ℤ) = 2520 by norm_num)
      (show -(-Complex.I * Complex.I) = -1 by rw [neg_mul, neg_neg, Complex.I_mul_I]),
    θ_cg' (h2N h5040) (show (((5040 : ℕ) : ℤ) + 1260 - 1260) = 5040 by norm_num)
      (show -(-Complex.I / Complex.I) = 1 by rw [neg_div, neg_neg, div_self hI]),
    θ_N' (by norm_num) (h2N h5040) h10080, θ_N' (by norm_num) (h2N h5040) h10080] at hm
  have hd := dissect2 h2520 1260 hI
  rw [θz (hN' h2520 2 two_pos) 0 (e := 2 * 1260 - ((2520 : ℕ) : ℤ)) (c := -Complex.I ^ 2) (by norm_num) (by simp),
    mul_zero, add_zero, show (mono 0 1 : L) = 1 from rfl, one_mul,
    θ_cg' (hN' h2520 2 two_pos) (show (((2520 : ℕ) : ℤ) + 2 * 1260) = 5040 by norm_num)
      (show -Complex.I ^ 2 = 1 by simp), θ_N' (by norm_num) (hN' h2520 2 two_pos) h10080] at hd
  rw [show (252 : ℤ) + 1008 = 1260 by norm_num, show (3 : ℤ) * 252 + 504 = 1260 by norm_num,
    show -Complex.I ^ 3 = Complex.I by rw [pow_three, ← mul_assoc, Complex.I_mul_I]; ring,
    show (2 : ℤ) * 252 + 336 = 840 by norm_num, show Complex.I ^ 2 = -1 by simp,
    show (2 : ℤ) * 252 + 2016 = 2520 by norm_num, hd]
  have hB : θ h3360 840 (-1) = B20 5 := by unfold B20; norm_num
  rw [hB]
  linear_combination B20 5 * hm

/-! ## The zero count -/

theorem F19_zero : F19 = 0 := by
  refine zero_count h5040 10 one_ne_zero F19_mem
    ![1512, 3192, 4032, 4872, 1512, 3192, 4032, 4872, 672, 2352, 252]
    ![-1, -1, -1, -1, 1, 1, 1, 1, -1, -1, Complex.I] ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [Complex.I_ne_zero]
  · intro i j hij a ha
    fin_cases i <;> fin_cases j <;> simp at hij ha ⊢ <;> first | omega | exact Complex.I_ne_one | norm_num | (intro h; have := congrArg Complex.re h; norm_num at this)
  · intro i
    fin_cases i
    exacts [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11]

/-! ## (8.17) -/

/-- `J_{6,15} J_{12,60} = J_{3,12} J̄_{3,30}`. -/
theorem PX : θ h2520 1008 1 * θ h10080 2016 1 = j12 3 * θ h5040 504 (-1) := by
  unfold j12
  rw [θu h168 h2520 15 6 4 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 h10080 60 12 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θu h168 (h48 hqT) 12 3 5 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    θb h168 h5040 30 3 1 (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [PJ, prod_range_succ, prod_range_zero, one_mul]
  norm_num
  have hP : ∀ r : ℕ, 1 ≤ r → PA h168 r 60 ≠ 0 := fun r hr => PA_ne h168 r 60 hr (by norm_num)
  field_simp [hP]

theorem E817_holds : E817 := by
  have h0 : ev F19 0 1 = 0 := by rw [F19_zero]; exact ev_zero 0 1
  rw [ev_F19 _ one_ne_zero, ev_T1' _ one_ne_zero, ev_T2' _ one_ne_zero, ev_T3' _ one_ne_zero] at h0
  rw [show (-(1 : ℂ) ^ 3) = -1 by norm_num, show (-(1 : ℂ) ^ 2) = -1 by norm_num, show (1 : ℂ) ^ 2 = 1 by norm_num,
    show (0 : ℤ) + 1008 = 1008 by norm_num, show (3 : ℤ) * 0 + 504 = 504 by norm_num,
    show (2 : ℤ) * 0 + 4536 = ((5040 : ℕ) : ℤ) - 504 by norm_num, refl_m h5040,
    show (2 : ℤ) * 0 + 336 = 336 by norm_num, show (2 : ℤ) * 0 + 2016 = 2016 by norm_num,
    show (2 : ℤ) * 0 = 0 by norm_num, show (0 : ℤ) + 168 = 168 by norm_num, mono1 0 rfl, one_mul] at h0
  have hW : θ h5040 504 (-1) ≠ 0 := θ_ne_zero h5040 (by norm_num) fun _ _ => by norm_num
  unfold E817
  have e6 : jb30 6 = θ h5040 1008 (-1) := by unfold jb30; rw [θ_N' (by norm_num) _ h5040]; norm_num
  have e2 : J20 2 = θ h3360 336 1 := by unfold J20; norm_num
  rw [e6, e2]
  apply mul_right_cancel₀ hW
  linear_combination h0 + θ h3360 336 1 * PX

/-- **The first mock theta conjecture** (Hickerson's MTC₀, in Andrews–Garvan form, multiplied out):
`(q;q)_∞ f₀(q) + 2 (q;q)_∞ φ(q²) = J_{5,10} J_{2,5}`, i.e. `f₀(q) = θ₄(0,q⁵) G(q) − 2 φ(q²)`. -/
theorem mtc0 :
    MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0 +
        2 * MockTheta5.JTP.qfacInf * (Ea 2 two_ne_zero (Phi 1) - 1) = Jp 5 10 * Jp 2 5 :=
  mtc0_of E817_holds

end MTC
