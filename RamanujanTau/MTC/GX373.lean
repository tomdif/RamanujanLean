/-
# The `g`-side at the MTC₀ point (HM §8, the display after Cor. 8.4)

At `x* = Z²¹ t^{105}`, `y* = Z⁶³ t^{105} = −x*`, `q = t^{42}` the six Appell–Lerch terms of `J̄ g_{3,7,3}` pair up:
both `X_t` and `Y_t` equal `Q^{14−10t}` (`Q = t^{168}`), and
`(−y)^t j(q^{7t}x; q³) + (−x)^t j(q^{7t}y; q³) = (−y)^t [j(q^{7t}x) + (−1)^t j(−q^{7t}x)]`,
which the `m = 2` dissection (HM (1.2f)) evaluates: `t = 0 ↦ 2J₁`, `t = 1 ↦ 2Q⁻²J₁`, `t = 2 ↦ 0`.

`gNum_xstar`: `J̄ g(x*, y*) = 2 j(Q²; Q³) (A(Q^{14}) + Q^{−2} A(Q⁴))`, `A = J̄_{0,30} m(·, Q^{30}, −1)`.
-/
import RamanujanTau.MTC.G373
import RamanujanTau.MTC.Z84
import RamanujanTau.ALTheta

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma neg_mono_g (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

lemma θ_N' {N N' : ℕ} (h : N = N') (hN : 1 ≤ N) (hN' : 1 ≤ N') (e : ℤ) (c : ℂ) : θ hN e c = θ hN' e c := by
  subst h; rfl

lemma θ_cg' {N : ℕ} (hN : 1 ≤ N) {e e' : ℤ} {c c' : ℂ} (he : e = e') (hc : c = c') : θ hN e c = θ hN e' c' := by
  subst he hc; rfl

/-! ## The `m = 2` dissection -/

section Dis2
variable {N : ℕ} (hN : 1 ≤ N)

lemma dissect2 (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hN e c = mono 0 1 * θ (hN' hN 2 two_pos) (N + 2 * e) (-c ^ 2) +
      mono (N - e) (-c⁻¹) * θ (hN' hN 2 two_pos) (2 * e - N) (-c ^ 2) := by
  rw [θ_dissect hN 2 two_pos e hc, Fin.sum_univ_two]
  refine congrArg₂ (· + ·) (congrArg₂ (· * ·) (mono_ext (by simp [c2]) (by simp))
      (θ_cg' _ (by simp [c2]; try ring) (by ring)))
    (congrArg₂ (· * ·) (mono_ext (by simp [c2]) (by simp)) (θ_cg' _ (by simp [c2]; try ring) (by ring)))

lemma pair_plus (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hN e c + θ hN e (-c) = 2 * θ (hN' hN 2 two_pos) (N + 2 * e) (-c ^ 2) := by
  rw [dissect2 hN e hc, dissect2 hN e (neg_ne_zero.mpr hc)]
  have h1 : (mono (N - e) (-c⁻¹) : L) + mono (N - e) (-(-c)⁻¹) = 0 := by
    rw [inv_neg, neg_neg, ← neg_mono_g]; ring
  have h0 : (mono 0 1 : L) = 1 := rfl
  rw [neg_sq]
  linear_combination θ (hN' hN 2 two_pos) (2 * e - N) (-c ^ 2) * h1 +
    2 * θ (hN' hN 2 two_pos) (N + 2 * e) (-c ^ 2) * h0

lemma pair_minus (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hN e c - θ hN e (-c) = 2 * mono (N - e) (-c⁻¹) * θ (hN' hN 2 two_pos) (2 * e - N) (-c ^ 2) := by
  rw [dissect2 hN e hc, dissect2 hN e (neg_ne_zero.mpr hc)]
  have h1 : (mono (N - e) (-(-c)⁻¹) : L) = -mono (N - e) (-c⁻¹) := by
    rw [inv_neg, neg_neg, neg_mono_g, neg_neg]
  rw [neg_sq, h1]
  ring

end Dis2

/-! ## The specialization -/

lemma hqG : 1 ≤ 42 := by norm_num
lemma h504 : 1 ≤ 504 := by norm_num

lemma Z63_eq : Z84 ^ (63 : ℤ) = -Z84 ^ (21 : ℤ) := by
  rw [Z_neg', ← zpow_add₀ Z_ne]; norm_num

lemma negsq21 : -(Z84 ^ (21 : ℤ)) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, show (21 : ℤ) * ((2 : ℕ) : ℤ) = 42 by norm_num, ← Z_neg1, neg_neg]

lemma θ504 (e : ℤ) (c : ℂ) : θ (hN' (h3qe hqG) 2 two_pos) e c = θ h504 e c :=
  θ_N' (by norm_num) _ _ e c

lemma θ504_qpow3 : θ h504 1512 1 = 0 := by
  rw [show (1512 : ℤ) = ((504 : ℕ) : ℤ) * 3 by norm_num]; exact θ_qpow h504 3

/-- `j(Q⁴; Q³) = −Q⁻¹ j(Q²; Q³)`. -/
lemma θ504_672 : θ h504 672 1 = mono (-168) (-1) * θ h504 336 1 := by
  have h := θ_qshift h504 168 (one_ne_zero) 1
  rw [show (168 : ℤ) + ((504 : ℕ) : ℤ) * 1 = 672 by norm_num] at h
  have hr : θ h504 (((504 : ℕ) : ℤ) - 336) 1 = θ h504 336 1 := by
    have := θ_reflect h504 336 one_ne_zero; rwa [inv_one] at this
  rw [h, show (168 : ℤ) = ((504 : ℕ) : ℤ) - 336 by norm_num, hr]
  congr 1
  exact mono_ext (by norm_num [c2]) (by norm_num)

lemma c21_ne : Z84 ^ (21 : ℤ) ≠ 0 := zpow_ne_zero _ Z_ne

/-- the three brackets. -/
lemma brk0 :
    mono (3 * (42 : ℕ) * c2 0 + 105 * 0) ((-Z84 ^ (63 : ℤ)) ^ (0 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 0 + 105) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 0 + 105 * 0) ((-Z84 ^ (21 : ℤ)) ^ (0 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 0 + 105) (Z84 ^ (63 : ℤ)) =
      2 * θ h504 336 1 := by
  have hp := pair_plus (h3qe hqG) (7 * (42 : ℕ) * 0 + 105) c21_ne
  rw [negsq21, θ504, show (((3 * 42 : ℕ) : ℤ) + 2 * (7 * ((42 : ℕ) : ℤ) * 0 + 105)) = 336 by norm_num] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 0 + 105 * 0) ((-Z84 ^ (63 : ℤ)) ^ (0 : ℤ)) : L) = 1 :=
    mono_ext (by norm_num [c2]) (by rw [zpow_zero])
  have m2 : (mono (3 * (42 : ℕ) * c2 0 + 105 * 0) ((-Z84 ^ (21 : ℤ)) ^ (0 : ℤ)) : L) = 1 :=
    mono_ext (by norm_num [c2]) (by rw [zpow_zero])
  rw [m1, m2, one_mul, one_mul, Z63_eq]
  exact hp

lemma brk1 :
    mono (3 * (42 : ℕ) * c2 1 + 105 * 1) ((-Z84 ^ (63 : ℤ)) ^ (1 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 1 + 105) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 1 + 105 * 1) ((-Z84 ^ (21 : ℤ)) ^ (1 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 1 + 105) (Z84 ^ (63 : ℤ)) =
      2 * mono (-336) 1 * θ h504 336 1 := by
  have hp := pair_minus (h3qe hqG) (7 * (42 : ℕ) * 1 + 105) c21_ne
  rw [negsq21, θ504, show 2 * (7 * ((42 : ℕ) : ℤ) * 1 + 105) - ((3 * 42 : ℕ) : ℤ) = 672 by norm_num,
    θ504_672] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 1 + 105 * 1) ((-Z84 ^ (63 : ℤ)) ^ (1 : ℤ)) : L) = mono 105 (Z84 ^ (21 : ℤ)) :=
    mono_ext (by norm_num [c2]) (by rw [Z63_eq, neg_neg, zpow_one])
  have m2 : (mono (3 * (42 : ℕ) * c2 1 + 105 * 1) ((-Z84 ^ (21 : ℤ)) ^ (1 : ℤ)) : L) = -mono 105 (Z84 ^ (21 : ℤ)) := by
    rw [neg_mono_g]; exact mono_ext (by norm_num [c2]) (by rw [zpow_one])
  have hkey : (mono 105 (Z84 ^ (21 : ℤ)) : L) * mono (((3 * 42 : ℕ) : ℤ) - (7 * ((42 : ℕ) : ℤ) * 1 + 105))
      (-(Z84 ^ (21 : ℤ))⁻¹) * mono (-168) (-1) = mono (-336) 1 := by
    rw [mono_mul, mono_mul]
    exact mono_ext (by norm_num) (by field_simp [c21_ne, Z_ne])
  rw [m1, m2, Z63_eq]
  linear_combination (mono 105 (Z84 ^ (21 : ℤ)) : L) * hp + 2 * θ h504 336 1 * hkey

lemma brk2 :
    mono (3 * (42 : ℕ) * c2 2 + 105 * 2) ((-Z84 ^ (63 : ℤ)) ^ (2 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 2 + 105) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 2 + 105 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 2 + 105) (Z84 ^ (63 : ℤ)) =
      0 := by
  have hp := pair_plus (h3qe hqG) (7 * (42 : ℕ) * 2 + 105) c21_ne
  rw [negsq21, θ504, show (((3 * 42 : ℕ) : ℤ) + 2 * (7 * ((42 : ℕ) : ℤ) * 2 + 105)) = 1512 by norm_num,
    θ504_qpow3] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 2 + 105 * 2) ((-Z84 ^ (63 : ℤ)) ^ (2 : ℤ)) : L) =
      mono (3 * (42 : ℕ) * c2 2 + 105 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) :=
    mono_ext rfl (by rw [Z63_eq, neg_neg]; simp only [zpow_two]; ring)
  rw [m1, Z63_eq]
  linear_combination (mono (3 * (42 : ℕ) * c2 2 + 105 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) : L) * hp

/-- **the `g`-side at `(x*, y*)`**: `J̄ g = 2 j(Q²;Q³)(A(Q^{14}) + Q^{−2}A(Q⁴))`. -/
theorem gNum_xstar :
    gNum hqG 105 (Z84 ^ (63 : ℤ)) 105 (Z84 ^ (21 : ℤ)) =
      2 * θ h504 336 1 * (Av (h120 hqG) 2352 1 0 (-1) + mono (-336) 1 * Av (h120 hqG) 672 1 0 (-1)) := by
  have ex0 : eX (qe := 42) 105 0 105 = 2352 := by norm_num [eX]
  have ex1 : eX (qe := 42) 105 1 105 = 672 := by norm_num [eX]
  have ex2 : eX (qe := 42) 105 2 105 = -1008 := by norm_num [eX]
  have ey0 : eY (qe := 42) 105 0 105 = 2352 := by norm_num [eY]
  have ey1 : eY (qe := 42) 105 1 105 = 672 := by norm_num [eY]
  have ey2 : eY (qe := 42) 105 2 105 = -1008 := by norm_num [eY]
  have cx1 : cX (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
    unfold cX; simp only [Z_neg']; zsimp; exact Z_eq_one (by norm_num)
  have cy1 : cY (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
    unfold cY; simp only [Z_neg']; zsimp; exact Z_eq_one (by norm_num)
  unfold gNum g1 g2
  rw [ex0, ex1, ex2, ey0, ey1, ey2, cx1, cy1]
  linear_combination Av (h120 hqG) 2352 1 0 (-1) * brk0 + Av (h120 hqG) 672 1 0 (-1) * brk1 +
    Av (h120 hqG) (-1008) 1 0 (-1) * brk2

end MTC
