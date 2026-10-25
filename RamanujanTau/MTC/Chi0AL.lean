/-
# The χ₀ endgame: Appell–Lerch normalization at the seven HM points

With `q = t^{36}` (`Q = t⁶`) the g-parts of HM Theorem 0.3 at the seven χ₀ points involve the Appell–Lerch
numerators `B e = A(−t^e, −1)` in base `t^{360}` (`Bv`). They satisfy
* `Bv_qs`: `B(e + 360) = J̄ + t^e B(e)`;
* `Bv_inv`: `B(−e) = −t^e B(e)`,
so every one of the 28 values reduces to `B_ρ`, `ρ ∈ {6, 24, 66, 84, 96, 114, 156, 174}` (`Q`-classes
`1, 4, 11, 14, 16, 19, 26, 29`).
-/
import RamanujanTau.MTC.Chi0Bridge
import RamanujanTau.MTC.Endgame1

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

lemma hN360 : 1 ≤ 10 * 36 := by norm_num

/-- `A(−t^e, −1)` in base `t^{360}`. -/
noncomputable def Bv (e : ℤ) : L := Av hN360 e (-1) 0 (-1)

/-- `J̄ = j(−1; t^{360})`. -/
noncomputable def Jb6 : L := θ hN360 0 (-1)

lemma lamOK_B {e : ℤ} (he : e % 360 ≠ 0) : LamOK (10 * 36) e (-1) 0 (-1) := fun r ⟨h1, _⟩ => by
  apply he
  unfold wE at h1
  push_cast at h1
  rw [show e = 360 * (1 - r) by linarith]
  simp

lemma Bv_qs {e : ℤ} (he : e % 360 ≠ 0) : Bv (e + 360) = Jb6 + mono e 1 * Bv e := by
  have h := Av_qshift hN360 (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) (lamOK_B he)
  unfold Bv Jb6
  rw [show ((10 * 36 : ℕ) : ℤ) = 360 by norm_num] at h
  rw [show (mono e (-1) : L) = -mono e 1 by simp [mono]] at h
  linear_combination h

lemma Bv_inv {e : ℤ} (he : e % 360 ≠ 0) : Bv (-e) = -mono e 1 * Bv e := by
  have h := Av_inv' hN360 (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) (lamOK_B he)
  unfold Bv
  rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num, neg_zero] at h
  rw [h, mono_mul]
  congr 1
  exact congrArg Neg.neg (mono_ext (by ring) (by norm_num))

/-! ## Normalizing the 28 g-terms -/

/-- `j(−t^e; t^{72})`. -/
noncomputable def th72 (e : ℤ) : L := θ (H232.h2qe H232.hq36) e (-1)

lemma th72_qs (e s : ℤ) : th72 (e + 72 * s) = mono (-(72 * c2 (s + 1)) - e * s + 72 * s) 1 * th72 e := by
  have h := θ_qshift (H232.h2qe H232.hq36) e (by norm_num : (-1 : ℂ) ≠ 0) s
  unfold th72
  rw [show (((2 * 36 : ℕ) : ℤ)) = 72 by norm_num] at h
  rw [h]
  congr 1
  refine mono_ext rfl ?_
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one, ← mul_zpow]; norm_num

lemma th72_refl (e : ℤ) : th72 (72 - e) = th72 e := by
  have h := θ_reflect (H232.h2qe H232.hq36) e (by norm_num : (-1 : ℂ) ≠ 0)
  unfold th72
  rw [show (((2 * 36 : ℕ) : ℤ)) = 72 by norm_num, show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h
  exact h

lemma mono3 (a b c : ℤ) (x y z : ℂ) (X Y : L) :
    mono a x * (mono b y * X) * (mono c z * Y) = mono (a + b + c) (x * y * z) * (X * Y) := by
  rw [show mono a x * (mono b y * X) * (mono c z * Y) = (mono a x * mono b y * mono c z) * (X * Y) by ring,
    mono_mul, mono_mul]

lemma mono2 (a b : ℤ) (x y : ℂ) (X Y : L) :
    mono a x * (mono b y * X) * Y = mono (a + b) (x * y) * (X * Y) := by
  rw [show mono a x * (mono b y * X) * Y = (mono a x * mono b y) * (X * Y) by ring, mono_mul]

lemma mono_neg1 (e : ℤ) : -(mono e 1 : L) = mono e (-1) := by simp [mono]


lemma thn42 : th72 42 = mono (0) 1 * th72 30 := by
  have h := th72_qs 42 (0)
  rw [show (42 : ℤ) + 72 * (0) = 42 by norm_num] at h
  rw [h]
  rw [show (42 : ℤ) = 72 - 30 by norm_num, th72_refl]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma thn150 : th72 150 = mono (-84) 1 * th72 6 := by
  have h := th72_qs 6 (2)
  rw [show (6 : ℤ) + 72 * (2) = 150 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 6) (mono_ext (by norm_num [c2]) rfl)


lemma thn96 : th72 96 = mono (-24) 1 * th72 24 := by
  have h := th72_qs 24 (1)
  rw [show (24 : ℤ) + 72 * (1) = 96 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 24) (mono_ext (by norm_num [c2]) rfl)


lemma thn78 : th72 78 = mono (-6) 1 * th72 6 := by
  have h := th72_qs 6 (1)
  rw [show (6 : ℤ) + 72 * (1) = 78 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 6) (mono_ext (by norm_num [c2]) rfl)


lemma thn204 : th72 204 = mono (-192) 1 * th72 12 := by
  have h := th72_qs 60 (2)
  rw [show (60 : ℤ) + 72 * (2) = 204 by norm_num] at h
  rw [h]
  rw [show (60 : ℤ) = 72 - 12 by norm_num, th72_refl]
  exact congrArg (· * th72 12) (mono_ext (by norm_num [c2]) rfl)


lemma thn186 : th72 186 = mono (-156) 1 * th72 30 := by
  have h := th72_qs 42 (2)
  rw [show (42 : ℤ) + 72 * (2) = 186 by norm_num] at h
  rw [h]
  rw [show (42 : ℤ) = 72 - 30 by norm_num, th72_refl]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma thn66 : th72 66 = mono (0) 1 * th72 6 := by
  have h := th72_qs 66 (0)
  rw [show (66 : ℤ) + 72 * (0) = 66 by norm_num] at h
  rw [h]
  rw [show (66 : ℤ) = 72 - 6 by norm_num, th72_refl]
  exact congrArg (· * th72 6) (mono_ext (by norm_num [c2]) rfl)


lemma thn174 : th72 174 = mono (-132) 1 * th72 30 := by
  have h := th72_qs 30 (2)
  rw [show (30 : ℤ) + 72 * (2) = 174 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma thn132 : th72 132 = mono (-60) 1 * th72 12 := by
  have h := th72_qs 60 (1)
  rw [show (60 : ℤ) + 72 * (1) = 132 by norm_num] at h
  rw [h]
  rw [show (60 : ℤ) = 72 - 12 by norm_num, th72_refl]
  exact congrArg (· * th72 12) (mono_ext (by norm_num [c2]) rfl)


lemma thn102 : th72 102 = mono (-30) 1 * th72 30 := by
  have h := th72_qs 30 (1)
  rw [show (30 : ℤ) + 72 * (1) = 102 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma thn240 : th72 240 = mono (-288) 1 * th72 24 := by
  have h := th72_qs 24 (3)
  rw [show (24 : ℤ) + 72 * (3) = 240 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 24) (mono_ext (by norm_num [c2]) rfl)


lemma thn210 : th72 210 = mono (-204) 1 * th72 6 := by
  have h := th72_qs 66 (2)
  rw [show (66 : ℤ) + 72 * (2) = 210 by norm_num] at h
  rw [h]
  rw [show (66 : ℤ) = 72 - 6 by norm_num, th72_refl]
  exact congrArg (· * th72 6) (mono_ext (by norm_num [c2]) rfl)


lemma thn120 : th72 120 = mono (-48) 1 * th72 24 := by
  have h := th72_qs 48 (1)
  rw [show (48 : ℤ) + 72 * (1) = 120 by norm_num] at h
  rw [h]
  rw [show (48 : ℤ) = 72 - 24 by norm_num, th72_refl]
  exact congrArg (· * th72 24) (mono_ext (by norm_num [c2]) rfl)


lemma thn114 : th72 114 = mono (-42) 1 * th72 30 := by
  have h := th72_qs 42 (1)
  rw [show (42 : ℤ) + 72 * (1) = 114 by norm_num] at h
  rw [h]
  rw [show (42 : ℤ) = 72 - 30 by norm_num, th72_refl]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma thn228 : th72 228 = mono (-252) 1 * th72 12 := by
  have h := th72_qs 12 (3)
  rw [show (12 : ℤ) + 72 * (3) = 228 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 12) (mono_ext (by norm_num [c2]) rfl)


lemma thn222 : th72 222 = mono (-234) 1 * th72 6 := by
  have h := th72_qs 6 (3)
  rw [show (6 : ℤ) + 72 * (3) = 222 by norm_num] at h
  rw [h]
  exact congrArg (· * th72 6) (mono_ext (by norm_num [c2]) rfl)


lemma thn258 : th72 258 = mono (-342) 1 * th72 30 := by
  have h := th72_qs 42 (3)
  rw [show (42 : ℤ) + 72 * (3) = 258 by norm_num] at h
  rw [h]
  rw [show (42 : ℤ) = 72 - 30 by norm_num, th72_refl]
  exact congrArg (· * th72 30) (mono_ext (by norm_num [c2]) rfl)


lemma gN0 : H232.g1 H232.hq36 (42) (-1) (0) (42) (-1) = mono (0) (1) * (th72 30 * Bv 174) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 42) (-1) : L) = th72 42 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 42 0 42) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (174) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn42]
  skip
  rw [mono2]
  refine congrArg (· * (th72 30 * Bv 174)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN1 : H232.g2 H232.hq36 (42) (-1) (0) (42) (-1) = mono (0) (1) * (th72 30 * Bv 174) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 42) (-1) : L) = th72 42 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 42 0 42) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (174) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn42]
  skip
  rw [mono2]
  refine congrArg (· * (th72 30 * Bv 174)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN2 : H232.g1 H232.hq36 (42) (-1) (1) (42) (-1) = mono (-36) (-1) * (th72 6 * Bv 6) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 42) (-1) : L) = th72 150 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 42 1 42) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-6) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn150]
  rw [show (-6 : ℤ) = -6 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 6 * Bv 6)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN3 : H232.g2 H232.hq36 (42) (-1) (1) (42) (-1) = mono (-36) (-1) * (th72 6 * Bv 6) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 42) (-1) : L) = th72 150 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 42 1 42) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-6) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn150]
  rw [show (-6 : ℤ) = -6 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 6 * Bv 6)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN4 : H232.g1 H232.hq36 (78) (-1) (0) (96) (-1) = mono (-24) (1) * (th72 24 * Bv 84) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 96) (-1) : L) = th72 96 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 78 0 96) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (84) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn96]
  skip
  rw [mono2]
  refine congrArg (· * (th72 24 * Bv 84)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN5 : H232.g2 H232.hq36 (78) (-1) (0) (96) (-1) = mono (-6) (1) * (th72 6 * Bv 174) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 78) (-1) : L) = th72 78 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 78 0 96) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (174) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn78]
  skip
  rw [mono2]
  refine congrArg (· * (th72 6 * Bv 174)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN6 : H232.g1 H232.hq36 (78) (-1) (1) (96) (-1) = mono (-18) (-1) * (th72 12 * Bv 96) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 96) (-1) : L) = th72 204 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 78 1 96) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-96) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn204]
  rw [show (-96 : ℤ) = -96 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 12 * Bv 96)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN7 : H232.g2 H232.hq36 (78) (-1) (1) (96) (-1) = mono (-54) (-1) * (th72 30 * Bv 6) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 78) (-1) : L) = th72 186 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 78 1 96) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-6) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn186]
  rw [show (-6 : ℤ) = -6 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 30 * Bv 6)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN8 : H232.g1 H232.hq36 (78) (-1) (0) (66) (-1) = mono (0) (1) * (th72 6 * Bv 174) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 66) (-1) : L) = th72 66 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 78 0 66) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (174) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn66]
  skip
  rw [mono2]
  refine congrArg (· * (th72 6 * Bv 174)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN9 : H232.g2 H232.hq36 (78) (-1) (0) (66) (-1) = mono (-6) (1) * (th72 6 * Bv 114) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 78) (-1) : L) = th72 78 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 78 0 66) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (114) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn78]
  skip
  rw [mono2]
  refine congrArg (· * (th72 6 * Bv 114)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN10 : H232.g1 H232.hq36 (78) (-1) (1) (66) (-1) = mono (-48) (-1) * (th72 30 * Bv 6) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 66) (-1) : L) = th72 174 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 78 1 66) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-6) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn174]
  rw [show (-6 : ℤ) = -6 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 30 * Bv 6)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN11 : H232.g2 H232.hq36 (78) (-1) (1) (66) (-1) = mono (-24) (-1) * (th72 30 * Bv 66) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 78) (-1) : L) = th72 186 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 78 1 66) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-66) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn186]
  rw [show (-66 : ℤ) = -66 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 30 * Bv 66)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN12 : H232.g1 H232.hq36 (102) (-1) (0) (132) (-1) = mono (-60) (1) * (th72 12 * Bv 24) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 132) (-1) : L) = th72 132 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 102 0 132) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (24) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn132]
  skip
  rw [mono2]
  refine congrArg (· * (th72 12 * Bv 24)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN13 : H232.g2 H232.hq36 (102) (-1) (0) (132) (-1) = mono (-30) (1) * (th72 30 * Bv 174) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 102) (-1) : L) = th72 102 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 102 0 132) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (174) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn102]
  skip
  rw [mono2]
  refine congrArg (· * (th72 30 * Bv 174)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN14 : H232.g1 H232.hq36 (102) (-1) (1) (132) (-1) = mono (-30) (-1) * (th72 24 * Bv 156) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 132) (-1) : L) = th72 240 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 102 1 132) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-156) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn240]
  rw [show (-156 : ℤ) = -156 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 24 * Bv 156)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN15 : H232.g2 H232.hq36 (102) (-1) (1) (132) (-1) = mono (-66) (-1) * (th72 6 * Bv 6) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 102) (-1) : L) = th72 210 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 102 1 132) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-6) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn210]
  rw [show (-6 : ℤ) = -6 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 6 * Bv 6)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN16 : H232.g1 H232.hq36 (114) (-1) (0) (120) (-1) = mono (-48) (1) * (th72 24 * Bv 84) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 120) (-1) : L) = th72 120 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 114 0 120) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (84) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn120]
  skip
  rw [mono2]
  refine congrArg (· * (th72 24 * Bv 84)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN17 : H232.g2 H232.hq36 (114) (-1) (0) (120) (-1) = mono (-42) (1) * (th72 30 * Bv 114) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 114) (-1) : L) = th72 114 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 114 0 120) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (114) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn114]
  skip
  rw [mono2]
  refine congrArg (· * (th72 30 * Bv 114)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN18 : H232.g1 H232.hq36 (114) (-1) (1) (120) (-1) = mono (-42) (-1) * (th72 12 * Bv 96) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 120) (-1) : L) = th72 228 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 114 1 120) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-96) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn228]
  rw [show (-96 : ℤ) = -96 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 12 * Bv 96)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN19 : H232.g2 H232.hq36 (114) (-1) (1) (120) (-1) = mono (-48) (-1) * (th72 6 * Bv 66) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 114) (-1) : L) = th72 222 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 114 1 120) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-66) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn222]
  rw [show (-66 : ℤ) = -66 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 6 * Bv 66)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN20 : H232.g1 H232.hq36 (114) (-1) (0) (96) (-1) = mono (-24) (1) * (th72 24 * Bv 156) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 96) (-1) : L) = th72 96 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 114 0 96) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (156) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn96]
  skip
  rw [mono2]
  refine congrArg (· * (th72 24 * Bv 156)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN21 : H232.g2 H232.hq36 (114) (-1) (0) (96) (-1) = mono (-42) (1) * (th72 30 * Bv 66) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 114) (-1) : L) = th72 114 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 114 0 96) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (66) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn114]
  skip
  rw [mono2]
  refine congrArg (· * (th72 30 * Bv 66)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN22 : H232.g1 H232.hq36 (114) (-1) (1) (96) (-1) = mono (-54) (-1) * (th72 12 * Bv 24) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 96) (-1) : L) = th72 204 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 114 1 96) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-24) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn204]
  rw [show (-24 : ℤ) = -24 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 12 * Bv 24)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN23 : H232.g2 H232.hq36 (114) (-1) (1) (96) (-1) = mono (-24) (-1) * (th72 6 * Bv 114) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 114) (-1) : L) = th72 222 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 114 1 96) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-114) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn222]
  rw [show (-114 : ℤ) = -114 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 6 * Bv 114)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN24 : H232.g1 H232.hq36 (150) (-1) (0) (150) (-1) = mono (-84) (1) * (th72 6 * Bv 66) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 150) (-1) : L) = th72 150 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 150 0 150) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (66) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn150]
  skip
  rw [mono2]
  refine congrArg (· * (th72 6 * Bv 66)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN25 : H232.g2 H232.hq36 (150) (-1) (0) (150) (-1) = mono (-84) (1) * (th72 6 * Bv 66) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 0 + 150) (-1) : L) = th72 150 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 150 0 150) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (66) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn150]
  skip
  rw [mono2]
  refine congrArg (· * (th72 6 * Bv 66)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN26 : H232.g1 H232.hq36 (150) (-1) (1) (150) (-1) = mono (-78) (-1) * (th72 30 * Bv 114) := by
  unfold H232.g1
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 150) (-1) : L) = th72 258 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eX (qe := 36) 150 1 150) (H232.cX (-1) (-1)) 0 (-1) : L) = Bv (-114) by
      unfold Bv H232.eX H232.cX; norm_num]
  rw [thn258]
  rw [show (-114 : ℤ) = -114 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 30 * Bv 114)) (mono_ext ?_ ?_) <;> norm_num [c2]


lemma gN27 : H232.g2 H232.hq36 (150) (-1) (1) (150) (-1) = mono (-78) (-1) * (th72 30 * Bv 114) := by
  unfold H232.g2
  rw [show (θ (H232.h2qe H232.hq36) (3 * ((36 : ℕ) : ℤ) * 1 + 150) (-1) : L) = th72 258 by unfold th72; norm_num,
    show (Av (H232.h10 H232.hq36) (H232.eY (qe := 36) 150 1 150) (H232.cY (-1) (-1)) 0 (-1) : L) = Bv (-114) by
      unfold Bv H232.eY H232.cY; norm_num]
  rw [thn258]
  rw [show (-114 : ℤ) = -114 by norm_num, Bv_inv (by norm_num)]
  rw [mono_neg1, mono3]
  refine congrArg (· * (th72 30 * Bv 114)) (mono_ext ?_ ?_) <;> norm_num [c2]

/-! ## The HM side assembled -/

/-- `t`. -/
noncomputable def tt : L := mono 1 1

lemma monoT (E : ℤ) : (mono E 1 : L) = tt ^ E := by
  unfold tt; rw [mono_zpow]; exact mono_ext (by ring) (by simp)

lemma tt_ne : tt ≠ 0 := by unfold tt; simp [mono]

lemma monoTn (E : ℤ) : (mono E (-1) : L) = -tt ^ E := by rw [← monoT, mono_neg1]

/-- pentagonal 2-dissection: `(Q;Q)_∞ = j(−t^{30};t^{72}) − t⁶ j(−t⁶;t^{72})`. -/
def eEO : ℤ ⊕ ℤ ≃ ℤ where
  toFun x := Sum.elim (fun m : ℤ => 2 * m) (fun m : ℤ => 2 * m + 1) x
  invFun k := if k % 2 = 0 then Sum.inl (k / 2) else Sum.inr (k / 2)
  left_inv x := by
    rcases x with m | m
    · simp only [Sum.elim_inl]; rw [if_pos (by omega)]; congr 1; omega
    · simp only [Sum.elim_inr]; rw [if_neg (by omega)]; congr 1; omega
  right_inv k := by
    by_cases h : k % 2 = 0
    · simp only [h, if_true, Sum.elim_inl]; omega
    · simp only [h, if_false, Sum.elim_inr]; omega

lemma qdis : ιN h6 MockTheta5.JTP.qfacInf = th72 30 - mono 6 1 * th72 6 := by
  rw [← J6_eq, θ]
  have hsp := hs_split (thF h18 12 1) (thF (H232.h2qe H232.hq36) 42 (-1))
    ((-mono 12 1 : L) • thF (H232.h2qe H232.hq36) 78 (-1)) eEO
    (fun m => by
      simp only [thF, monoFam_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inl]
      refine mono_ext ?_ ?_
      · unfold thE; have h1 := two_c2 (2 * m); have h2 := two_c2 m; push_cast; nlinarith
      · unfold thC; rw [one_zpow, mul_one]; rw [two_mul, zpow_add₀ (by norm_num)])
    (fun m => by
      simp only [thF, monoFam_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
        HahnSeries.of_symm_smul_of_eq_mul]
      rw [neg_mul, mono_mul, neg_mono]
      refine mono_ext ?_ ?_
      · unfold thE; have h1 := two_c2 (2 * m + 1); have h2 := two_c2 m; push_cast; nlinarith
      · unfold thC; rw [one_zpow, mul_one, one_mul, neg_one_zpow_sq, zpow_add₀ (by norm_num), zpow_one,
          zpow_mul]; norm_num)
  rw [hsp, hs_eq (_ • _), SummableFamily.hsum_smul, ← hs_eq]
  have e1 : hs (thF (H232.h2qe H232.hq36) 42 (-1)) = th72 30 := by
    show th72 42 = th72 30
    rw [thn42, show (mono 0 1 : L) = 1 from rfl, one_mul]
  have e2 : hs (thF (H232.h2qe H232.hq36) 78 (-1)) = mono (-6) 1 * th72 6 := thn78
  rw [e1, e2, ← mul_assoc, mono_neg1, mono_mul,
    show (mono (12 + -6) (-1 * 1) : L) = -mono 6 1 by rw [mono_neg1]; exact mono_ext (by norm_num) (by norm_num)]
  ring


lemma hp7_7 : Jb6 * ev (H232.fS H232.hq36 42 (-1)) 42 (-1) =
    H232.g1 H232.hq36 42 (-1) 0 42 (-1) + H232.g1 H232.hq36 42 (-1) 1 42 (-1) +
      (H232.g2 H232.hq36 42 (-1) 0 42 (-1) + H232.g2 H232.hq36 42 (-1) 1 42 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 42 (-1) 42 (-1) := by
  have h := H232.hm03_77
  unfold H232.gNum at h
  exact h


lemma hp16_13 : Jb6 * ev (H232.fS H232.hq36 78 (-1)) 96 (-1) =
    H232.g1 H232.hq36 78 (-1) 0 96 (-1) + H232.g1 H232.hq36 78 (-1) 1 96 (-1) +
      (H232.g2 H232.hq36 78 (-1) 0 96 (-1) + H232.g2 H232.hq36 78 (-1) 1 96 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 78 (-1) 96 (-1) := by
  have h := H232.hm03_16_13
  unfold H232.gNum at h
  exact h


lemma hp11_13 : Jb6 * ev (H232.fS H232.hq36 78 (-1)) 66 (-1) =
    H232.g1 H232.hq36 78 (-1) 0 66 (-1) + H232.g1 H232.hq36 78 (-1) 1 66 (-1) +
      (H232.g2 H232.hq36 78 (-1) 0 66 (-1) + H232.g2 H232.hq36 78 (-1) 1 66 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 78 (-1) 66 (-1) := by
  have h := H232.hm03_11_13
  unfold H232.gNum at h
  exact h


lemma hp22_17 : Jb6 * ev (H232.fS H232.hq36 102 (-1)) 132 (-1) =
    H232.g1 H232.hq36 102 (-1) 0 132 (-1) + H232.g1 H232.hq36 102 (-1) 1 132 (-1) +
      (H232.g2 H232.hq36 102 (-1) 0 132 (-1) + H232.g2 H232.hq36 102 (-1) 1 132 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 102 (-1) 132 (-1) := by
  have h := H232.hm03_22_17
  unfold H232.gNum at h
  exact h


lemma hp20_19 : Jb6 * ev (H232.fS H232.hq36 114 (-1)) 120 (-1) =
    H232.g1 H232.hq36 114 (-1) 0 120 (-1) + H232.g1 H232.hq36 114 (-1) 1 120 (-1) +
      (H232.g2 H232.hq36 114 (-1) 0 120 (-1) + H232.g2 H232.hq36 114 (-1) 1 120 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 114 (-1) 120 (-1) := by
  have h := H232.hm03_20_19
  unfold H232.gNum at h
  exact h


lemma hp16_19 : Jb6 * ev (H232.fS H232.hq36 114 (-1)) 96 (-1) =
    H232.g1 H232.hq36 114 (-1) 0 96 (-1) + H232.g1 H232.hq36 114 (-1) 1 96 (-1) +
      (H232.g2 H232.hq36 114 (-1) 0 96 (-1) + H232.g2 H232.hq36 114 (-1) 1 96 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 114 (-1) 96 (-1) := by
  have h := H232.hm03_16_19
  unfold H232.gNum at h
  exact h


lemma hp25_25 : Jb6 * ev (H232.fS H232.hq36 150 (-1)) 150 (-1) =
    H232.g1 H232.hq36 150 (-1) 0 150 (-1) + H232.g1 H232.hq36 150 (-1) 1 150 (-1) +
      (H232.g2 H232.hq36 150 (-1) 0 150 (-1) + H232.g2 H232.hq36 150 (-1) 1 150 (-1)) +
      kap (H232.h5 H232.hq36) * H232.thV H232.hq36 150 (-1) 150 (-1) := by
  have h := H232.hm03_25_25
  unfold H232.gNum at h
  exact h
/-- the HM theta parts at the seven points, with their Hecke-side weights. -/
noncomputable def TVsum : L :=
  (-1 : L) * tt ^ (0 : ℤ) * H232.thV H232.hq36 42 (-1) 42 (-1) +
    (1 : L) * tt ^ (12 : ℤ) * H232.thV H232.hq36 78 (-1) 96 (-1) +
    (2 : L) * tt ^ (6 : ℤ) * H232.thV H232.hq36 78 (-1) 66 (-1) +
    (-1 : L) * tt ^ (30 : ℤ) * H232.thV H232.hq36 102 (-1) 132 (-1) +
    (-1 : L) * tt ^ (36 : ℤ) * H232.thV H232.hq36 114 (-1) 120 (-1) +
    (-1 : L) * tt ^ (24 : ℤ) * H232.thV H232.hq36 114 (-1) 96 (-1) +
    (1 : L) * tt ^ (72 : ℤ) * H232.thV H232.hq36 150 (-1) 150 (-1)

/-- **the HM side**: `J̄ ((Q;Q)_∞ χ₀ − 2(Q;Q)_∞) = −3 (Q;Q)_∞ (B₁₇₄ + t⁻⁴² B₆ + t⁻¹⁸ B₆₆ + t⁻⁶ B₁₁₄) + κ Σ θ_{2,1}`. -/
theorem hm_side : Jb6 * (ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) - 2 * ιN h6 MockTheta5.JTP.qfacInf) =
    -3 * ιN h6 MockTheta5.JTP.qfacInf * (Bv 174 + tt ^ (-42 : ℤ) * Bv 6 + tt ^ (-18 : ℤ) * Bv 66 + tt ^ (-6 : ℤ) * Bv 114) +
      kap (H232.h5 H232.hq36) * TVsum := by
  rw [chi0_hecke_HM]
  have h0 := hp7_7
  rw [gN0, gN2, gN1, gN3] at h0
  have h1 := hp16_13
  rw [gN4, gN6, gN5, gN7] at h1
  have h2 := hp11_13
  rw [gN8, gN10, gN9, gN11] at h2
  have h3 := hp22_17
  rw [gN12, gN14, gN13, gN15] at h3
  have h4 := hp20_19
  rw [gN16, gN18, gN17, gN19] at h4
  have h5 := hp16_19
  rw [gN20, gN22, gN21, gN23] at h5
  have h6 := hp25_25
  rw [gN24, gN26, gN25, gN27] at h6
  rw [qdis]
  unfold TVsum
  simp only [monoT, monoTn] at *
  have htt : tt ≠ 0 := by unfold tt; simp [mono]
  linear_combination (norm := (field_simp; ring)) (-1 : L) * tt ^ (0 : ℤ) * h0 + (1 : L) * tt ^ (12 : ℤ) * h1 + (2 : L) * tt ^ (6 : ℤ) * h2 + (-1 : L) * tt ^ (30 : ℤ) * h3 + (-1 : L) * tt ^ (36 : ℤ) * h4 + (-1 : L) * tt ^ (24 : ℤ) * h5 + (1 : L) * tt ^ (72 : ℤ) * h6

end MTC.Chi0L
