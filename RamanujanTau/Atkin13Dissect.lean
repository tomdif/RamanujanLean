/-
# The 13-dissection of Euler's product

With `q = t^{d'}`, `Q = q¹³`, `J_a = θ(Q^a; Q¹³)` and `E(q) = Σ (−1)^k q^{k(3k−1)/2}`:

  `E(q) = E(q¹⁶⁹)·(J₄/J₂ − q·J₆/J₃ − q²·J₂/J₁ + q⁵·J₅/J₄ + q⁷ − q¹²·J₃/J₅ + q²²·J₁/J₆)`.

Proof: split the pentagonal series into its thirteen `k mod 13` branches (`θ_dissect`). Move each branch
to a canonical argument by quasi-periodicity or reflection. Then pair the branches; each pair is the left
side of the quintuple product identity `quint_theta` at `z = Q^a`.
-/
import RamanujanTau.ALQuint
import RamanujanTau.ALThetaCore13

set_option autoImplicit false

namespace ALz13
open ALz HahnSeries

lemma θ_congrN {A B : ℕ} (h : A = B) (hA : 1 ≤ A) (hB : 1 ≤ B) (e : ℤ) (c : ℂ) : θ hA e c = θ hB e c := by
  subst h; rfl

section Dissect
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 13 * d) {d' : ℕ} (hd' : d = 13 * d') (h3 : 1 ≤ 3 * N)
  (hE : 1 ≤ 3 * d')

/-- the branch `θ(Q^x; Q³⁹)`, `Q = t^d`. -/
noncomputable def Pt (h3 : 1 ≤ 3 * N) (d : ℕ) (x : ℤ) : L := θ h3 ((d : ℤ) * x) 1

/-- the `ρ`-th pentagonal branch `(−1)^ρ q^{ρ(3ρ+1)/2} θ(Q^{19−3ρ}; Q³⁹)`. -/
noncomputable def dTerm (h3 : 1 ≤ 3 * N) (d d' : ℕ) (ρ : ℕ) : L :=
  mono ((d' : ℤ) * (3 * c2 (-(ρ : ℤ)) - ρ)) ((-1) ^ ρ) * Pt h3 d (19 - 3 * ρ)

lemma mono_to_pow (d' : ℕ) {A : ℤ} (c : ℂ) (k : ℕ) (hA : A = d' * k) : mono A c = C c * (mono d' 1) ^ k := by
  subst hA
  rw [mono, single_pow, one_pow, HahnSeries.C_apply, single_mul_single, zero_add, mul_one, nsmul_eq_mul, mul_comm]

include hd in
lemma Pt_refl (x : ℤ) : Pt h3 d (39 - x) = Pt h3 d x := by
  have h := θ_reflect h3 ((d : ℤ) * x) (one_ne_zero (α := ℂ))
  rw [inv_one] at h
  rw [Pt, Pt, ← h]; congr 1; rw [hd]; push_cast; ring

include hd in
lemma Pt_shift (x : ℤ) : Pt h3 d x = mono (d * x) (-1) * Pt h3 d (x + 39) := by
  have h := θ_qshift h3 ((d : ℤ) * x) (one_ne_zero (α := ℂ)) 1
  rw [show ((d : ℤ) * x + ((3 * N : ℕ) : ℤ) * 1) = d * (x + 39) by rw [hd]; push_cast; ring] at h
  rw [Pt, Pt, h, ← mul_assoc, mono_mul]
  rw [show ((d : ℤ) * x + (-(((3 * N : ℕ) : ℤ) * c2 (1 + 1)) - d * x * 1 + ((3 * N : ℕ) : ℤ) * 1)) = 0 by
    rw [show c2 (1 + 1) = 1 by decide]; ring]
  rw [show ((-1 : ℂ) * ((-1) ^ (1 : ℤ) * 1 ^ (-1 : ℤ))) = 1 by norm_num]
  exact (one_mul _).symm

include hd hd' in
/-- one pentagonal branch, in canonical form. -/
lemma dis_term (ρ : ℕ) :
    mono (((3 * d' : ℕ) : ℤ) * c2 (-(ρ : ℤ)) - (d' : ℤ) * (ρ : ℤ)) ((-1) ^ (-(ρ : ℤ)) * (1 : ℂ) ^ (-(ρ : ℤ))) *
        θ (hN' hE 13 (by norm_num)) (((3 * d' : ℕ) : ℤ) * c2 ((13 : ℕ) : ℤ) - ((3 * d' : ℕ) : ℤ) * ((13 : ℕ) : ℤ) * (ρ : ℤ)
          + ((13 : ℕ) : ℤ) * (d' : ℤ)) ((-1) ^ (13 + 1) * (1 : ℂ) ^ 13)
      = dTerm h3 d d' ρ := by
  unfold dTerm
  rw [Pt, θ_congrN (show 3 * d' * 13 * 13 = 3 * N by rw [hd, hd']; ring) _ h3]
  rw [show c2 ((13 : ℕ) : ℤ) = 78 by decide, show ((-1 : ℂ) ^ (13 + 1) * (1 : ℂ) ^ 13) = 1 by norm_num, one_zpow, mul_one,
    zpow_neg, show ((-1 : ℂ) ^ (ρ : ℤ))⁻¹ = (-1) ^ ρ by rw [zpow_natCast, ← inv_pow, inv_neg, inv_one]]
  congr 2
  · push_cast; ring
  · rw [hd']; push_cast; ring

end Dissect


section Terms
variable {N : ℕ} {d : ℕ} (hd : N = 13 * d) {d' : ℕ} (hd' : d = 13 * d') (h3 : 1 ≤ 3 * N)
include hd hd'

lemma dTerm_0 : dTerm h3 d d' 0 = C 1 * (mono d' 1) ^ 0 * Pt h3 d 19 := by
  unfold dTerm
  rw [show (3 * c2 (-((0 : ℕ) : ℤ)) - ((0 : ℕ) : ℤ)) = 0 by decide,
    show (19 : ℤ) - 3 * ((0 : ℕ) : ℤ) = 19 by norm_num]
  rw [mono_to_pow d' _ 0 (by push_cast; ring)]
  norm_num

lemma dTerm_1 : dTerm h3 d d' 1 = C (-1) * (mono d' 1) ^ 2 * Pt h3 d 16 := by
  unfold dTerm
  rw [show (3 * c2 (-((1 : ℕ) : ℤ)) - ((1 : ℕ) : ℤ)) = 2 by decide,
    show (19 : ℤ) - 3 * ((1 : ℕ) : ℤ) = 16 by norm_num]
  rw [mono_to_pow d' _ 2 (by push_cast; ring)]
  norm_num

lemma dTerm_2 : dTerm h3 d d' 2 = C 1 * (mono d' 1) ^ 7 * Pt h3 d 13 := by
  unfold dTerm
  rw [show (3 * c2 (-((2 : ℕ) : ℤ)) - ((2 : ℕ) : ℤ)) = 7 by decide,
    show (19 : ℤ) - 3 * ((2 : ℕ) : ℤ) = 13 by norm_num]
  rw [mono_to_pow d' _ 7 (by push_cast; ring)]
  norm_num

lemma dTerm_3 : dTerm h3 d d' 3 = C (-1) * (mono d' 1) ^ 15 * Pt h3 d 29 := by
  unfold dTerm
  rw [show (3 * c2 (-((3 : ℕ) : ℤ)) - ((3 : ℕ) : ℤ)) = 15 by decide,
    show (19 : ℤ) - 3 * ((3 : ℕ) : ℤ) = 10 by norm_num]
  rw [show (10 : ℤ) = 39 - 29 by norm_num, Pt_refl hd h3 29, mono_to_pow d' _ 15 (by push_cast; ring)]
  norm_num

lemma dTerm_4 : dTerm h3 d d' 4 = C 1 * (mono d' 1) ^ 26 * Pt h3 d 32 := by
  unfold dTerm
  rw [show (3 * c2 (-((4 : ℕ) : ℤ)) - ((4 : ℕ) : ℤ)) = 26 by decide,
    show (19 : ℤ) - 3 * ((4 : ℕ) : ℤ) = 7 by norm_num]
  rw [show (7 : ℤ) = 39 - 32 by norm_num, Pt_refl hd h3 32, mono_to_pow d' _ 26 (by push_cast; ring)]
  norm_num

lemma dTerm_5 : dTerm h3 d d' 5 = C (-1) * (mono d' 1) ^ 40 * Pt h3 d 35 := by
  unfold dTerm
  rw [show (3 * c2 (-((5 : ℕ) : ℤ)) - ((5 : ℕ) : ℤ)) = 40 by decide,
    show (19 : ℤ) - 3 * ((5 : ℕ) : ℤ) = 4 by norm_num]
  rw [show (4 : ℤ) = 39 - 35 by norm_num, Pt_refl hd h3 35, mono_to_pow d' _ 40 (by push_cast; ring)]
  norm_num

lemma dTerm_6 : dTerm h3 d d' 6 = C 1 * (mono d' 1) ^ 57 * Pt h3 d 38 := by
  unfold dTerm
  rw [show (3 * c2 (-((6 : ℕ) : ℤ)) - ((6 : ℕ) : ℤ)) = 57 by decide,
    show (19 : ℤ) - 3 * ((6 : ℕ) : ℤ) = 1 by norm_num]
  rw [show (1 : ℤ) = 39 - 38 by norm_num, Pt_refl hd h3 38, mono_to_pow d' _ 57 (by push_cast; ring)]
  norm_num

lemma dTerm_7 : dTerm h3 d d' 7 = C (-1) * (mono d' 1) ^ 77 * Pt h3 d 41 := by
  unfold dTerm
  rw [show (3 * c2 (-((7 : ℕ) : ℤ)) - ((7 : ℕ) : ℤ)) = 77 by decide,
    show (19 : ℤ) - 3 * ((7 : ℕ) : ℤ) = -2 by norm_num]
  rw [show (-2 : ℤ) = 39 - 41 by norm_num, Pt_refl hd h3 41, mono_to_pow d' _ 77 (by push_cast; ring)]
  norm_num

lemma dTerm_8 : dTerm h3 d d' 8 = C 1 * (mono d' 1) ^ 100 * Pt h3 d 44 := by
  unfold dTerm
  rw [show (3 * c2 (-((8 : ℕ) : ℤ)) - ((8 : ℕ) : ℤ)) = 100 by decide,
    show (19 : ℤ) - 3 * ((8 : ℕ) : ℤ) = -5 by norm_num]
  rw [show (-5 : ℤ) = 39 - 44 by norm_num, Pt_refl hd h3 44, mono_to_pow d' _ 100 (by push_cast; ring)]
  norm_num

lemma dTerm_9 : dTerm h3 d d' 9 = C 1 * (mono d' 1) ^ 22 * Pt h3 d 31 := by
  unfold dTerm
  rw [show (3 * c2 (-((9 : ℕ) : ℤ)) - ((9 : ℕ) : ℤ)) = 126 by decide,
    show (19 : ℤ) - 3 * ((9 : ℕ) : ℤ) = -8 by norm_num]
  rw [Pt_shift hd h3 (-8), show (-8 : ℤ) + 39 = 31 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 22 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_10 : dTerm h3 d d' 10 = C (-1) * (mono d' 1) ^ 12 * Pt h3 d 28 := by
  unfold dTerm
  rw [show (3 * c2 (-((10 : ℕ) : ℤ)) - ((10 : ℕ) : ℤ)) = 155 by decide,
    show (19 : ℤ) - 3 * ((10 : ℕ) : ℤ) = -11 by norm_num]
  rw [Pt_shift hd h3 (-11), show (-11 : ℤ) + 39 = 28 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 12 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_11 : dTerm h3 d d' 11 = C 1 * (mono d' 1) ^ 5 * Pt h3 d 25 := by
  unfold dTerm
  rw [show (3 * c2 (-((11 : ℕ) : ℤ)) - ((11 : ℕ) : ℤ)) = 187 by decide,
    show (19 : ℤ) - 3 * ((11 : ℕ) : ℤ) = -14 by norm_num]
  rw [Pt_shift hd h3 (-14), show (-14 : ℤ) + 39 = 25 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 5 (by rw [hd']; push_cast; ring)]
  norm_num

lemma dTerm_12 : dTerm h3 d d' 12 = C (-1) * (mono d' 1) ^ 1 * Pt h3 d 22 := by
  unfold dTerm
  rw [show (3 * c2 (-((12 : ℕ) : ℤ)) - ((12 : ℕ) : ℤ)) = 222 by decide,
    show (19 : ℤ) - 3 * ((12 : ℕ) : ℤ) = -17 by norm_num]
  rw [Pt_shift hd h3 (-17), show (-17 : ℤ) + 39 = 22 by norm_num]
  rw [← mul_assoc, mono_mul, mono_to_pow d' _ 1 (by rw [hd']; push_cast; ring)]
  norm_num

end Terms

section Main
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 13 * d) {d' : ℕ} (hd' : d = 13 * d') (h3 : 1 ≤ 3 * N)
  (hE : 1 ≤ 3 * d')

include hd in
/-- the quintuple product at `z = Q^a`. -/
lemma quint_J (a : ℤ) :
    (Pt h3 d (13 + 3 * a) + mono (d * a) 1 * Pt h3 d (26 + 3 * a)) * Jt hN hd a = Pt h3 d 13 * Jt hN hd (2 * a) := by
  have h := quint_theta hN h3 ((d : ℤ) * a) (one_ne_zero (α := ℂ))
  simp only [one_pow] at h
  rw [show (N : ℤ) + 3 * (d * a) = d * (13 + 3 * a) by rw [hd]; push_cast; ring,
    show 2 * (N : ℤ) + 3 * (d * a) = d * (26 + 3 * a) by rw [hd]; push_cast; ring,
    show (N : ℤ) = d * 13 by rw [hd]; push_cast; ring, show 2 * ((d : ℤ) * a) = d * (2 * a) by ring] at h
  exact h

include hd hd' in
lemma quint_J' (a : ℤ) (k : ℕ) (hk : (13 : ℤ) * a = k) (ha0 : 0 < a) (ha1 : a < 13) :
    Pt h3 d (13 + 3 * a) + (mono d' 1) ^ k * Pt h3 d (26 + 3 * a) = Pt h3 d 13 * Jt hN hd (2 * a) / Jt hN hd a := by
  rw [eq_div_iff (Jt_ne hN hd ha0 ha1), ← quint_J hN hd h3 a,
    mono_to_pow d' (A := (d : ℤ) * a) 1 k (by rw [hd']; push_cast; rw [← hk]; ring), map_one, one_mul]

include hd hd' in
/-- **The 13-dissection of Euler's product.** -/
theorem E_dissect :
    θ hE d' 1 = Pt h3 d 13 * (Jt hN hd 4 / Jt hN hd 2 - mono d' 1 * (Jt hN hd 6 / Jt hN hd 3)
      - (mono d' 1) ^ 2 * (Jt hN hd 2 / Jt hN hd 1) + (mono d' 1) ^ 5 * (Jt hN hd 5 / Jt hN hd 4) + (mono d' 1) ^ 7
      - (mono d' 1) ^ 12 * (Jt hN hd 3 / Jt hN hd 5) + (mono d' 1) ^ 22 * (Jt hN hd 1 / Jt hN hd 6)) := by
  rw [θ_dissect hE 13 (by norm_num) (d' : ℤ) one_ne_zero,
    Finset.sum_congr rfl fun (ρ : Fin 13) _ => dis_term hd hd' h3 hE (ρ : ℕ), Fin.sum_univ_eq_sum_range (dTerm h3 d d') 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dTerm_0 hd hd' h3, dTerm_1 hd hd' h3, dTerm_2 hd hd' h3, dTerm_3 hd hd' h3, dTerm_4 hd hd' h3, dTerm_5 hd hd' h3, dTerm_6 hd hd' h3, dTerm_7 hd hd' h3, dTerm_8 hd hd' h3, dTerm_9 hd hd' h3, dTerm_10 hd hd' h3, dTerm_11 hd hd' h3, dTerm_12 hd hd' h3]
  have e1 := quint_J' hN hd hd' h3 1 13 (by norm_num) (by norm_num) (by norm_num)
  have e2 := quint_J' hN hd hd' h3 2 26 (by norm_num) (by norm_num) (by norm_num)
  have e3 := quint_J' hN hd hd' h3 3 39 (by norm_num) (by norm_num) (by norm_num)
  have e4 := quint_J' hN hd hd' h3 4 52 (by norm_num) (by norm_num) (by norm_num)
  have e5 := quint_J' hN hd hd' h3 5 65 (by norm_num) (by norm_num) (by norm_num)
  have e6 := quint_J' hN hd hd' h3 6 78 (by norm_num) (by norm_num) (by norm_num)
  have j8 : Jt hN hd (2 * 4) = Jt hN hd 5 := by rw [← Jt_refl hN hd 5]; norm_num [Jt]
  have j10 : Jt hN hd (2 * 5) = Jt hN hd 3 := by rw [← Jt_refl hN hd 3]; norm_num [Jt]
  have j12 : Jt hN hd (2 * 6) = Jt hN hd 1 := by rw [← Jt_refl hN hd 1]; norm_num [Jt]
  rw [j8] at e4; rw [j10] at e5; rw [j12] at e6
  rw [show (13 : ℤ) + 3 * 1 = 16 by norm_num, show (26 : ℤ) + 3 * 1 = 29 by norm_num, show (2 : ℤ) * 1 = 2 by norm_num] at e1
  rw [show (13 : ℤ) + 3 * 2 = 19 by norm_num, show (26 : ℤ) + 3 * 2 = 32 by norm_num, show (2 : ℤ) * 2 = 4 by norm_num] at e2
  rw [show (13 : ℤ) + 3 * 3 = 22 by norm_num, show (26 : ℤ) + 3 * 3 = 35 by norm_num, show (2 : ℤ) * 3 = 6 by norm_num] at e3
  rw [show (13 : ℤ) + 3 * 4 = 25 by norm_num, show (26 : ℤ) + 3 * 4 = 38 by norm_num] at e4
  rw [show (13 : ℤ) + 3 * 5 = 28 by norm_num, show (26 : ℤ) + 3 * 5 = 41 by norm_num] at e5
  rw [show (13 : ℤ) + 3 * 6 = 31 by norm_num, show (26 : ℤ) + 3 * 6 = 44 by norm_num] at e6
  simp only [map_one, map_neg, one_mul, neg_mul, pow_zero, mul_one]
  linear_combination e2 - (mono d' 1) ^ 2 * e1 - (mono d' 1) * e3 + (mono d' 1) ^ 5 * e4 - (mono d' 1) ^ 12 * e5
    + (mono d' 1) ^ 22 * e6

end Main

end ALz13
