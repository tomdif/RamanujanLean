/-
# Fixed-point interval arithmetic with outward rounding (kernel-evaluable)

An interval `I : Iv` is a pair of integers; it denotes `[I.lo / S, I.hi / S]` with `S = 2^192`.
Every operation rounds outward. `Iv.mem x I` is the real semantics, and each operation has a soundness lemma.
All operations are on `ℤ`/`ℕ`, so `decide +kernel` evaluates them with GMP-accelerated arithmetic.
-/
import Mathlib
import RamanujanTau.JensenThreshold.Tail.Defs

set_option autoImplicit false

namespace JensenThreshold.Tail


lemma S_pos : (0 : ℤ) < S := by unfold S; positivity
lemma S_posR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos


/-- real semantics. -/
def Iv.mem (x : ℝ) (I : Iv) : Prop := (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S


lemma fdS_le (a : ℤ) : ((fdS a : ℤ) : ℝ) ≤ (a : ℝ) / S := by
  rw [le_div_iff₀ S_posR]
  have := Int.ediv_mul_le a (b := S) S_pos.ne'
  exact_mod_cast this

lemma le_cdS (a : ℤ) : (a : ℝ) / S ≤ ((cdS a : ℤ) : ℝ) := by
  rw [div_le_iff₀ S_posR]
  have := Int.ediv_mul_le (-a) (b := S) S_pos.ne'
  have h : a ≤ cdS a * S := by unfold cdS; linarith
  exact_mod_cast h


lemma fdv_le (a : ℤ) {b : ℤ} (hb : 0 < b) : ((fdv a b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have := Int.ediv_mul_le a (b := b) hb.ne'
  exact_mod_cast this

lemma le_cdv (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ ((cdv a b : ℤ) : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have := Int.ediv_mul_le (-a) (b := b) hb.ne'
  have h : a ≤ cdv a b * b := by unfold cdv; linarith
  exact_mod_cast h


@[inherit_doc] notation:50 x:51 " ∈ᵢ " I:51 => Iv.mem x I

open Iv

variable {x y : ℝ} {I J : Iv}

lemma mem_add (hx : x ∈ᵢ I) (hy : y ∈ᵢ J) : (x + y) ∈ᵢ (I + J) := by
  show (x + y) ∈ᵢ (Iv.add I J)
  unfold Iv.mem at *; simp only [Iv.add, Int.cast_add, add_div]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma mem_neg (hx : x ∈ᵢ I) : (-x) ∈ᵢ (-I) := by
  show (-x) ∈ᵢ (Iv.neg I)
  unfold Iv.mem at *; simp only [Iv.neg, Int.cast_neg, neg_div]
  constructor <;> linarith [hx.1, hx.2]

lemma mem_sub (hx : x ∈ᵢ I) (hy : y ∈ᵢ J) : (x - y) ∈ᵢ (I - J) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

lemma min_mul_le {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have h2 : min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have h3 : min (b * c) (b * d) ≤ b * y ∧ b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  constructor
  · calc min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ min (a * y) (b * y) :=
          min_le_min h2.1 h3.1
      _ ≤ x * y := h1.1
  · calc x * y ≤ max (a * y) (b * y) := h1.2
      _ ≤ _ := max_le_max h2.2 h3.2

lemma mem_mul (hx : x ∈ᵢ I) (hy : y ∈ᵢ J) : (x * y) ∈ᵢ (I * J) := by
  show (x * y) ∈ᵢ (Iv.mul I J)
  unfold Iv.mem at *
  obtain ⟨h1, h2⟩ := min_mul_le hx.1 hx.2 hy.1 hy.2
  have hS := S_posR
  have e : ∀ p q : ℤ, (p : ℝ) / S * ((q : ℝ) / S) = ((p * q : ℤ) : ℝ) / S / S := by
    intro p q; push_cast; field_simp
  simp only [e] at h1 h2
  simp only [Iv.mul]
  set L := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  set H := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  have eL : ((L : ℤ) : ℝ) / S / S = min (min (((I.lo * J.lo : ℤ) : ℝ) / S / S) (((I.lo * J.hi : ℤ) : ℝ) / S / S))
      (min (((I.hi * J.lo : ℤ) : ℝ) / S / S) (((I.hi * J.hi : ℤ) : ℝ) / S / S)) := by
    simp only [L, Int.cast_min]
    rw [min_div_div_right hS.le, min_div_div_right hS.le, min_div_div_right hS.le,
      min_div_div_right hS.le, min_div_div_right hS.le, min_div_div_right hS.le]
  have eH : ((H : ℤ) : ℝ) / S / S = max (max (((I.lo * J.lo : ℤ) : ℝ) / S / S) (((I.lo * J.hi : ℤ) : ℝ) / S / S))
      (max (((I.hi * J.lo : ℤ) : ℝ) / S / S) (((I.hi * J.hi : ℤ) : ℝ) / S / S)) := by
    simp only [H, Int.cast_max]
    rw [max_div_div_right hS.le, max_div_div_right hS.le, max_div_div_right hS.le,
      max_div_div_right hS.le, max_div_div_right hS.le, max_div_div_right hS.le]
  constructor
  · refine le_trans ?_ (eL ▸ h1)
    exact div_le_div_of_nonneg_right (fdS_le L) hS.le
  · refine le_trans (eH ▸ h2) ?_
    exact div_le_div_of_nonneg_right (le_cdS H) hS.le

lemma mem_ofFrac (p q : ℤ) (hq : 0 < q) : ((p : ℝ) / q) ∈ᵢ (Iv.ofFrac p q) := by
  unfold Iv.mem Iv.ofFrac
  have hS := S_posR
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have e : ((p * S : ℤ) : ℝ) / q / S = (p : ℝ) / q := by push_cast; field_simp
  constructor
  · rw [← e]; exact div_le_div_of_nonneg_right (fdv_le _ hq) hS.le
  · rw [← e]; exact div_le_div_of_nonneg_right (le_cdv _ hq) hS.le

lemma mem_ofInt (p : ℤ) : ((p : ℝ)) ∈ᵢ (Iv.ofInt p) := by
  unfold Iv.mem Iv.ofInt
  have hS := S_posR
  have e : ((p * S : ℤ) : ℝ) / S = p := by push_cast; field_simp
  rw [e]; exact ⟨le_rfl, le_rfl⟩

lemma mem_one : (1 : ℝ) ∈ᵢ (Iv.ofInt 1) := by simpa using mem_ofInt 1

lemma mem_inv (hx : x ∈ᵢ I) (hI : 0 < I.lo) : (x⁻¹) ∈ᵢ I.inv := by
  unfold Iv.mem at *
  unfold Iv.inv
  have hS := S_posR
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hlo hS) hx.1
  have hhi : (0 : ℝ) < I.hi := by
    have := le_trans hx.1 hx.2
    have : (0:ℝ) < I.hi / S := lt_of_lt_of_le (div_pos hlo hS) this
    exact (div_pos_iff_of_pos_right hS).mp this
  have hhiZ : (0 : ℤ) < I.hi := by exact_mod_cast hhi
  have e : ∀ q : ℝ, 0 < q → ((S * S : ℤ) : ℝ) / q / S = (q / S)⁻¹ := by
    intro q hq; push_cast; field_simp
  constructor
  · calc ((fdv (S * S) I.hi : ℤ) : ℝ) / S ≤ ((S * S : ℤ) : ℝ) / I.hi / S :=
          div_le_div_of_nonneg_right (fdv_le _ hhiZ) hS.le
      _ = ((I.hi : ℝ) / S)⁻¹ := e _ hhi
      _ ≤ x⁻¹ := inv_anti₀ hxpos hx.2
  · calc x⁻¹ ≤ ((I.lo : ℝ) / S)⁻¹ := inv_anti₀ (div_pos hlo hS) hx.1
      _ = ((S * S : ℤ) : ℝ) / I.lo / S := (e _ hlo).symm
      _ ≤ ((cdv (S * S) I.lo : ℤ) : ℝ) / S := div_le_div_of_nonneg_right (le_cdv _ hI) hS.le

lemma mem_sqrt (hx : x ∈ᵢ I) (hI : 0 ≤ I.lo) : (Real.sqrt x) ∈ᵢ I.sqrt := by
  unfold Iv.mem at *
  unfold Iv.sqrt
  have hS := S_posR
  have hSnat : ((S.toNat : ℕ) : ℝ) = (S : ℝ) := by
    have : (S.toNat : ℤ) = S := Int.toNat_of_nonneg S_pos.le
    exact_mod_cast this
  have hlo : ((I.lo.toNat : ℕ) : ℝ) = (I.lo : ℝ) := by
    have : (I.lo.toNat : ℤ) = I.lo := Int.toNat_of_nonneg hI
    exact_mod_cast this
  have hx0 : 0 ≤ x := le_trans (div_nonneg (by exact_mod_cast hI) hS.le) hx.1
  have hhi0 : (0 : ℤ) ≤ I.hi := by
    have : (0:ℝ) ≤ I.hi / S := le_trans hx0 hx.2
    have : (0:ℝ) ≤ I.hi := by
      rcases (div_nonneg_iff.mp this) with h | h
      · exact h.1
      · exact absurd h.2 (not_le.mpr hS)
    exact_mod_cast this
  have hhi : ((I.hi.toNat : ℕ) : ℝ) = (I.hi : ℝ) := by
    have : (I.hi.toNat : ℤ) = I.hi := Int.toNat_of_nonneg hhi0
    exact_mod_cast this
  constructor
  · -- lower: r = sqrt(lo·S) floor, r/S ≤ sqrt(lo/S)
    set m := I.lo.toNat * S.toNat
    have hr : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    have hm : (m : ℝ) = (I.lo : ℝ) * S := by simp [m, hlo, hSnat]
    have key : (((Nat.sqrt m : ℕ) : ℤ) : ℝ) / S ≤ Real.sqrt ((I.lo : ℝ) / S) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      rw [div_pow, div_le_div_iff₀ (by positivity) hS]
      push_cast
      nlinarith [hr, hm]
    exact le_trans key (Real.sqrt_le_sqrt hx.1)
  · set m := I.hi.toNat * S.toNat
    have hr : (m : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' m
    have hm : (m : ℝ) = (I.hi : ℝ) * S := by simp [m, hhi, hSnat]
    have key : Real.sqrt ((I.hi : ℝ) / S) ≤ (((Nat.sqrt m : ℕ) : ℤ) + 1 : ℤ) / (S : ℝ) := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [div_pow, le_div_iff₀ (by positivity)]
      have h1 : (I.hi : ℝ) / S * S ^ 2 = (I.hi : ℝ) * S := by field_simp
      rw [h1]
      push_cast
      push_cast at hr
      nlinarith [hr, hm]
    exact le_trans (Real.sqrt_le_sqrt hx.2) key

lemma mem_pow (hx : x ∈ᵢ I) (k : ℕ) : (x ^ k) ∈ᵢ (I.pow k) := by
  induction k with
  | zero => simpa [Iv.pow] using mem_one
  | succ k ih => rw [pow_succ]; exact mem_mul ih hx

lemma mem_hull_left (hx : x ∈ᵢ I) (J : Iv) : x ∈ᵢ (Iv.hull I J) := by
  unfold Iv.mem Iv.hull at *
  have hS := S_posR
  constructor
  · refine le_trans ?_ hx.1
    exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) hS.le
  · refine le_trans hx.2 ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hS.le

lemma mem_hull_right (hx : x ∈ᵢ J) (I : Iv) : x ∈ᵢ (Iv.hull I J) := by
  unfold Iv.mem Iv.hull at *
  have hS := S_posR
  constructor
  · refine le_trans ?_ hx.1
    exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) hS.le
  · refine le_trans hx.2 ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hS.le

lemma abs_le_absHi (hx : x ∈ᵢ I) : |x| ≤ (Iv.absHi I : ℝ) / S := by
  unfold Iv.mem Iv.absHi at *
  have hS := S_posR
  rw [abs_le]
  constructor
  · have : (-(max (-I.lo) I.hi : ℤ) : ℝ) / S ≤ (I.lo : ℝ) / S :=
      div_le_div_of_nonneg_right (by exact_mod_cast (show -(max (-I.lo) I.hi) ≤ I.lo by
        have := le_max_left (-I.lo) I.hi; omega)) hS.le
    rw [neg_div] at this; push_cast at this ⊢; linarith [hx.1]
  · exact le_trans hx.2 (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hS.le)

lemma mem_symm {r : ℤ} (hx : |x| ≤ (r : ℝ) / S) : x ∈ᵢ (Iv.symm r) := by
  unfold Iv.mem Iv.symm
  rw [abs_le] at hx
  push_cast; rw [neg_div]; exact hx

/-- sign checks. -/
lemma pos_of_mem (hx : x ∈ᵢ I) (h : 0 < I.lo) : 0 < x :=
  lt_of_lt_of_le (div_pos (by exact_mod_cast h) S_posR) hx.1

lemma neg_of_mem (hx : x ∈ᵢ I) (h : I.hi < 0) : x < 0 :=
  lt_of_le_of_lt hx.2 (div_neg_of_neg_of_pos (by exact_mod_cast h) S_posR)

lemma nonpos_of_mem (hx : x ∈ᵢ I) (h : I.hi ≤ 0) : x ≤ 0 :=
  le_trans hx.2 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) S_posR.le)

lemma le_hi (hx : x ∈ᵢ I) : x ≤ (I.hi : ℝ) / S := hx.2
lemma lo_le (hx : x ∈ᵢ I) : (I.lo : ℝ) / S ≤ x := hx.1

end JensenThreshold.Tail
