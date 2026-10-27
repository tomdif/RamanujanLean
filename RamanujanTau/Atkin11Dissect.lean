/-
# The 11-dissection of Euler's product

With `q = t^{d'}`, `Q = q¹¹`, `J_a = θ(Q^a; Q¹¹)` and `E(q) = Σ (−1)^k q^{k(3k−1)/2}`:

  `E(q) = E(q¹²¹)·(J₄/J₂ − q·J₂/J₁ − q²·J₅/J₃ + q⁵ + q⁷·J₃/J₄ − q¹⁵·J₁/J₅)`.

Proof: split the pentagonal series into its eleven `k mod 11` branches (`θ_dissect`). Move each branch
to a canonical argument by quasi-periodicity or reflection. Then pair the branches; each pair is the left
side of the quintuple product identity `quint_theta` at `z = Q^a`.
-/
import RamanujanTau.ALQuint
import RamanujanTau.ALThetaCore11

set_option autoImplicit false

namespace ALz11
open ALz HahnSeries

lemma θ_congrN {A B : ℕ} (h : A = B) (hA : 1 ≤ A) (hB : 1 ≤ B) (e : ℤ) (c : ℂ) : θ hA e c = θ hB e c := by
  subst h; rfl

section Dissect
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 11 * d) {d' : ℕ} (hd' : d = 11 * d') (h3 : 1 ≤ 3 * N)
  (hE : 1 ≤ 3 * d')

/-- the branch `θ(Q^x; Q³³)`, `Q = t^d`. -/
noncomputable def Pt (h3 : 1 ≤ 3 * N) (d : ℕ) (x : ℤ) : L := θ h3 ((d : ℤ) * x) 1

/-- the `ρ`-th pentagonal branch `(−1)^ρ q^{ρ(3ρ+1)/2} θ(Q^{16−3ρ}; Q³³)`. -/
noncomputable def dTerm (h3 : 1 ≤ 3 * N) (d d' : ℕ) (ρ : ℕ) : L :=
  mono ((d' : ℤ) * (3 * c2 (-(ρ : ℤ)) - ρ)) ((-1) ^ ρ) * Pt h3 d (16 - 3 * ρ)

lemma mono_to_pow (d' : ℕ) {A : ℤ} (c : ℂ) (k : ℕ) (hA : A = d' * k) : mono A c = C c * (mono d' 1) ^ k := by
  subst hA
  rw [mono, single_pow, one_pow, HahnSeries.C_apply, single_mul_single, zero_add, mul_one, nsmul_eq_mul, mul_comm]

include hd in
lemma Pt_refl (x : ℤ) : Pt h3 d (33 - x) = Pt h3 d x := by
  have h := θ_reflect h3 ((d : ℤ) * x) (one_ne_zero (α := ℂ))
  rw [inv_one] at h
  rw [Pt, Pt, ← h]; congr 1; rw [hd]; push_cast; ring

include hd in
lemma Pt_shift (x : ℤ) : Pt h3 d x = mono (d * x) (-1) * Pt h3 d (x + 33) := by
  have h := θ_qshift h3 ((d : ℤ) * x) (one_ne_zero (α := ℂ)) 1
  rw [show ((d : ℤ) * x + ((3 * N : ℕ) : ℤ) * 1) = d * (x + 33) by rw [hd]; push_cast; ring] at h
  rw [Pt, Pt, h, ← mul_assoc, mono_mul]
  rw [show ((d : ℤ) * x + (-(((3 * N : ℕ) : ℤ) * c2 (1 + 1)) - d * x * 1 + ((3 * N : ℕ) : ℤ) * 1)) = 0 by
    rw [show c2 (1 + 1) = 1 by decide]; ring]
  rw [show ((-1 : ℂ) * ((-1) ^ (1 : ℤ) * 1 ^ (-1 : ℤ))) = 1 by norm_num]
  exact (one_mul _).symm

include hd hd' in
/-- one pentagonal branch, in canonical form. -/
lemma dis_term (ρ : ℕ) :
    mono (((3 * d' : ℕ) : ℤ) * c2 (-(ρ : ℤ)) - (d' : ℤ) * (ρ : ℤ)) ((-1) ^ (-(ρ : ℤ)) * (1 : ℂ) ^ (-(ρ : ℤ))) *
        θ (hN' hE 11 (by norm_num)) (((3 * d' : ℕ) : ℤ) * c2 ((11 : ℕ) : ℤ) - ((3 * d' : ℕ) : ℤ) * ((11 : ℕ) : ℤ) * (ρ : ℤ)
          + ((11 : ℕ) : ℤ) * (d' : ℤ)) ((-1) ^ (11 + 1) * (1 : ℂ) ^ 11)
      = dTerm h3 d d' ρ := by
  unfold dTerm
  rw [Pt, θ_congrN (show 3 * d' * 11 * 11 = 3 * N by rw [hd, hd']; ring) _ h3]
  rw [show c2 ((11 : ℕ) : ℤ) = 55 by decide, show ((-1 : ℂ) ^ (11 + 1) * (1 : ℂ) ^ 11) = 1 by norm_num, one_zpow, mul_one,
    zpow_neg, show ((-1 : ℂ) ^ (ρ : ℤ))⁻¹ = (-1) ^ ρ by rw [zpow_natCast, ← inv_pow, inv_neg, inv_one]]
  congr 2
  · push_cast; ring
  · rw [hd']; push_cast; ring

end Dissect

section Terms
variable {N : ℕ} {d : ℕ} (hd : N = 11 * d) {d' : ℕ} (hd' : d = 11 * d') (h3 : 1 ≤ 3 * N)
include hd hd'

lemma dTerm_0 : dTerm h3 d d' 0 = C 1 * (mono d' 1) ^ 0 * Pt h3 d 17 := by
  unfold dTerm
  rw [show (3 * c2 (-((0 : ℕ) : ℤ)) - ((0 : ℕ) : ℤ)) = 0 by decide,
    show (16 : ℤ) - 3 * ((0 : ℕ) : ℤ) = 16 by norm_num]
  rw [show (16 : ℤ) = 33 - 17 by norm_num, Pt_refl hd h3 17, mono_to_pow d' _ 0 (by push_cast; ring)]
  norm_num

lemma dTerm_1 : dTerm h3 d d' 1 = C (-1) * (mono d' 1) ^ 2 * Pt h3 d 20 := by
  unfold dTerm
  rw [show (3 * c2 (-((1 : ℕ) : ℤ)) - ((1 : ℕ) : ℤ)) = 2 by decide,
    show (16 : ℤ) - 3 * ((1 : ℕ) : ℤ) = 13 by norm_num]
  rw [show (13 : ℤ) = 33 - 20 by norm_num, Pt_refl hd h3 20, mono_to_pow d' _ 2 (by push_cast; ring)]
  norm_num

lemma dTerm_2 : dTerm h3 d d' 2 = C 1 * (mono d' 1) ^ 7 * Pt h3 d 23 := by
  unfold dTerm
  rw [show (3 * c2 (-((2 : ℕ) : ℤ)) - ((2 : ℕ) : ℤ)) = 7 by decide,
    show (16 : ℤ) - 3 * ((2 : ℕ) : ℤ) = 10 by norm_num]
  rw [show (10 : ℤ) = 33 - 23 by norm_num, Pt_refl hd h3 23, mono_to_pow d' _ 7 (by push_cast; ring)]
  norm_num

lemma dTerm_3 : dTerm h3 d d' 3 = C (-1) * (mono d' 1) ^ 15 * Pt h3 d 26 := by
  unfold dTerm
  rw [show (3 * c2 (-((3 : ℕ) : ℤ)) - ((3 : ℕ) : ℤ)) = 15 by decide,
    show (16 : ℤ) - 3 * ((3 : ℕ) : ℤ) = 7 by norm_num]
  rw [show (7 : ℤ) = 33 - 26 by norm_num, Pt_refl hd h3 26, mono_to_pow d' _ 15 (by push_cast; ring)]
  norm_num

lemma dTerm_4 : dTerm h3 d d' 4 = C (-1) * (mono d' 1) ^ 70 * Pt h3 d 37 := by
  unfold dTerm
  rw [show (3 * c2 (-((4 : ℕ) : ℤ)) - ((4 : ℕ) : ℤ)) = 26 by decide,
    show (16 : ℤ) - 3 * ((4 : ℕ) : ℤ) = 4 by norm_num]
  rw [Pt_shift hd h3 (4), show (4 : ℤ) + 33 = 37 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 70 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_5 : dTerm h3 d d' 5 = C 1 * (mono d' 1) ^ 51 * Pt h3 d 34 := by
  unfold dTerm
  rw [show (3 * c2 (-((5 : ℕ) : ℤ)) - ((5 : ℕ) : ℤ)) = 40 by decide,
    show (16 : ℤ) - 3 * ((5 : ℕ) : ℤ) = 1 by norm_num]
  rw [Pt_shift hd h3 (1), show (1 : ℤ) + 33 = 34 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 51 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_6 : dTerm h3 d d' 6 = C (-1) * (mono d' 1) ^ 35 * Pt h3 d 31 := by
  unfold dTerm
  rw [show (3 * c2 (-((6 : ℕ) : ℤ)) - ((6 : ℕ) : ℤ)) = 57 by decide,
    show (16 : ℤ) - 3 * ((6 : ℕ) : ℤ) = -2 by norm_num]
  rw [Pt_shift hd h3 (-2), show (-2 : ℤ) + 33 = 31 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 35 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_7 : dTerm h3 d d' 7 = C 1 * (mono d' 1) ^ 22 * Pt h3 d 28 := by
  unfold dTerm
  rw [show (3 * c2 (-((7 : ℕ) : ℤ)) - ((7 : ℕ) : ℤ)) = 77 by decide,
    show (16 : ℤ) - 3 * ((7 : ℕ) : ℤ) = -5 by norm_num]
  rw [Pt_shift hd h3 (-5), show (-5 : ℤ) + 33 = 28 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 22 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_8 : dTerm h3 d d' 8 = C (-1) * (mono d' 1) ^ 12 * Pt h3 d 25 := by
  unfold dTerm
  rw [show (3 * c2 (-((8 : ℕ) : ℤ)) - ((8 : ℕ) : ℤ)) = 100 by decide,
    show (16 : ℤ) - 3 * ((8 : ℕ) : ℤ) = -8 by norm_num]
  rw [Pt_shift hd h3 (-8), show (-8 : ℤ) + 33 = 25 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 12 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_9 : dTerm h3 d d' 9 = C 1 * (mono d' 1) ^ 5 * Pt h3 d 11 := by
  unfold dTerm
  rw [show (3 * c2 (-((9 : ℕ) : ℤ)) - ((9 : ℕ) : ℤ)) = 126 by decide,
    show (16 : ℤ) - 3 * ((9 : ℕ) : ℤ) = -11 by norm_num]
  rw [Pt_shift hd h3 (-11), show (-11 : ℤ) + 33 = 22 by norm_num]
  rw [show (22 : ℤ) = 33 - 11 by norm_num, Pt_refl hd h3 11]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 5 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_10 : dTerm h3 d d' 10 = C (-1) * (mono d' 1) ^ 1 * Pt h3 d 14 := by
  unfold dTerm
  rw [show (3 * c2 (-((10 : ℕ) : ℤ)) - ((10 : ℕ) : ℤ)) = 155 by decide,
    show (16 : ℤ) - 3 * ((10 : ℕ) : ℤ) = -14 by norm_num]
  rw [Pt_shift hd h3 (-14), show (-14 : ℤ) + 33 = 19 by norm_num]
  rw [show (19 : ℤ) = 33 - 14 by norm_num, Pt_refl hd h3 14]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 1 (by rw [hd']; push_cast; ring)]
  norm_num

end Terms

section Main
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 11 * d) {d' : ℕ} (hd' : d = 11 * d') (h3 : 1 ≤ 3 * N)
  (hE : 1 ≤ 3 * d')

include hd in
/-- the quintuple product at `z = Q^a`. -/
lemma quint_J (a : ℤ) :
    (Pt h3 d (11 + 3 * a) + mono (d * a) 1 * Pt h3 d (22 + 3 * a)) * Jt hN hd a = Pt h3 d 11 * Jt hN hd (2 * a) := by
  have h := quint_theta hN h3 ((d : ℤ) * a) (one_ne_zero (α := ℂ))
  simp only [one_pow] at h
  rw [show (N : ℤ) + 3 * (d * a) = d * (11 + 3 * a) by rw [hd]; push_cast; ring,
    show 2 * (N : ℤ) + 3 * (d * a) = d * (22 + 3 * a) by rw [hd]; push_cast; ring,
    show (N : ℤ) = d * 11 by rw [hd]; push_cast; ring, show 2 * ((d : ℤ) * a) = d * (2 * a) by ring] at h
  exact h

include hd hd' in
lemma quint_J' (a : ℤ) (k : ℕ) (hk : (11 : ℤ) * a = k) (ha0 : 0 < a) (ha1 : a < 11) :
    Pt h3 d (11 + 3 * a) + (mono d' 1) ^ k * Pt h3 d (22 + 3 * a) = Pt h3 d 11 * Jt hN hd (2 * a) / Jt hN hd a := by
  rw [eq_div_iff (Jt_ne hN hd ha0 ha1), ← quint_J hN hd h3 a,
    mono_to_pow d' (A := (d : ℤ) * a) 1 k (by rw [hd']; push_cast; rw [← hk]; ring), map_one, one_mul]

include hd hd' in
/-- **The 11-dissection of Euler's product.** -/
theorem E_dissect :
    θ hE d' 1 = Pt h3 d 11 * (Jt hN hd 4 / Jt hN hd 2 - mono d' 1 * (Jt hN hd 2 / Jt hN hd 1)
      - (mono d' 1) ^ 2 * (Jt hN hd 5 / Jt hN hd 3) + (mono d' 1) ^ 5 + (mono d' 1) ^ 7 * (Jt hN hd 3 / Jt hN hd 4)
      - (mono d' 1) ^ 15 * (Jt hN hd 1 / Jt hN hd 5)) := by
  rw [θ_dissect hE 11 (by norm_num) (d' : ℤ) one_ne_zero,
    Finset.sum_congr rfl fun (ρ : Fin 11) _ => dis_term hd hd' h3 hE (ρ : ℕ), Fin.sum_univ_eq_sum_range (dTerm h3 d d') 11]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dTerm_0 hd hd' h3, dTerm_1 hd hd' h3, dTerm_2 hd hd' h3, dTerm_3 hd hd' h3, dTerm_4 hd hd' h3,
    dTerm_5 hd hd' h3, dTerm_6 hd hd' h3, dTerm_7 hd hd' h3, dTerm_8 hd hd' h3, dTerm_9 hd hd' h3,
    dTerm_10 hd hd' h3]
  have e1 := quint_J' hN hd hd' h3 1 11 (by norm_num) (by norm_num) (by norm_num)
  have e2 := quint_J' hN hd hd' h3 2 22 (by norm_num) (by norm_num) (by norm_num)
  have e3 := quint_J' hN hd hd' h3 3 33 (by norm_num) (by norm_num) (by norm_num)
  have e4 := quint_J' hN hd hd' h3 4 44 (by norm_num) (by norm_num) (by norm_num)
  have e5 := quint_J' hN hd hd' h3 5 55 (by norm_num) (by norm_num) (by norm_num)
  have j6 : Jt hN hd (2 * 3) = Jt hN hd 5 := by rw [← Jt_refl hN hd 5]; norm_num [Jt]
  have j8 : Jt hN hd (2 * 4) = Jt hN hd 3 := by rw [← Jt_refl hN hd 3]; norm_num [Jt]
  have j10 : Jt hN hd (2 * 5) = Jt hN hd 1 := by rw [← Jt_refl hN hd 1]; norm_num [Jt]
  rw [j6] at e3; rw [j8] at e4; rw [j10] at e5
  rw [show (11 : ℤ) + 3 * 1 = 14 by norm_num, show (22 : ℤ) + 3 * 1 = 25 by norm_num,
    show (2 : ℤ) * 1 = 2 by norm_num] at e1
  rw [show (11 : ℤ) + 3 * 2 = 17 by norm_num, show (22 : ℤ) + 3 * 2 = 28 by norm_num,
    show (2 : ℤ) * 2 = 4 by norm_num] at e2
  rw [show (11 : ℤ) + 3 * 3 = 20 by norm_num, show (22 : ℤ) + 3 * 3 = 31 by norm_num] at e3
  rw [show (11 : ℤ) + 3 * 4 = 23 by norm_num, show (22 : ℤ) + 3 * 4 = 34 by norm_num] at e4
  rw [show (11 : ℤ) + 3 * 5 = 26 by norm_num, show (22 : ℤ) + 3 * 5 = 37 by norm_num] at e5
  simp only [map_one, map_neg, one_mul, neg_mul, pow_zero, mul_one]
  linear_combination (-(mono d' 1)) * e1 + e2 - (mono d' 1) ^ 2 * e3 + (mono d' 1) ^ 7 * e4 - (mono d' 1) ^ 15 * e5

end Main

end ALz11
