/-
# Local masses L1–L6 under `[DeligneBound]`

`Tl p e N = Σ_{i,j≤N} |γ_p(e;i,j)|` (columns `L`), `TlV p e N` (derivative columns `L'`). With `X = 1/p`,
`λ = λ(p)`, uniformly in the truncation `N`:

* **L1** `Tl_zero_le`: `Tl p 0 N ≤ 1 + 65540 X²` (exact first-order cancellation `γ(1,0) = λ²X²/(2(1+X))`);
* **L2** `Tl_one_le`: `Tl p 1 N ≤ |λ| + 65536 X` (`γ(1,0) = α(p) = −λ/2`);
* **L3** `Tl_le`: `Tl p e N ≤ 16384 (e+1)^6`;
* **L4** `TlV_zero_le`: `TlV p 0 N ≤ λ² X log p / 2 + 65540 X`;
* **L5** `TlV_one_le`: `TlV p 1 N ≤ log p (|λ|/2 + 65536 X)`;
* **L6** `TlV_le`: `TlV p e N ≤ 16384 log p (e+1)^6`.
-/
import RamanujanTau.QFProof5.Conv

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset RamanujanTau.QFProof RamanujanTau.QFProof2 RamanujanTau.QFProof3 RamanujanTau.QFProof4
open RamanujanTau.SelbergCoeffs (alpha abs_alpha_le_one alpha_one alpha_prime)
open RamanujanTau.HafnerBridge (lam rhoP rhoP')

/-! ### Kernel sums -/

lemma sq_add_le (a b : ℕ) : ((((a + b : ℕ) : ℝ) + 1) ^ 2) ≤ ((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2 := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h : ((a + b : ℕ) : ℝ) + 1 ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) := by push_cast; nlinarith
  rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h 2

lemma sum_mul_self_le (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) (N : ℕ) {M : ℝ} (hM : ∑ k ∈ Icc 0 N, F k ≤ M) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b ≤ M ^ 2 := by
  rw [← sum_mul_sum]
  have h0 : 0 ≤ ∑ k ∈ Icc 0 N, F k := sum_nonneg fun _ _ => hF _
  rw [← sq]; exact pow_le_pow_left₀ h0 hM 2

section Kernel

variable (K : ℕ → ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) {κ : ℝ} (hκ : 0 ≤ κ)
include hp hκ

lemma ksum0 (hKb : ∀ n, |K p n 0| ≤ κ * (((n : ℝ) + 1) ^ 2 * Xp p ^ (n - 0))) (N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 0| ≤ 256 * κ := by
  have hX := Xp_pos hp
  have hwX : (p : ℝ) / 2 * Xp p = 1 / 2 := by
    have := Xp_mul_p hp; linear_combination this / 2
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k
  have hpt : ∀ a b : ℕ, ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 0| ≤ κ * (F a * F b) := by
    intro a b
    have h1 := hKb (a + b)
    rw [Nat.sub_zero] at h1
    have h2 : ((p : ℝ) / 2) ^ (a + b) * (κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * Xp p ^ (a + b))) =
        κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (a + b)) := by
      rw [← hwX, mul_pow]; ring
    calc ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 0|
        ≤ ((p : ℝ) / 2) ^ (a + b) * (κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * Xp p ^ (a + b))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (a + b)) := h2
      _ ≤ κ * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (1 / 2 : ℝ) ^ (a + b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sq_add_le a b) (by positivity)) hκ
      _ = κ * (F a * F b) := by simp only [F]; rw [pow_add]; ring
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ * 16 ^ 2 := mul_le_mul_of_nonneg_left
        (sum_mul_self_le F (fun k => by positivity) N (sum_sq_le (by norm_num) le_rfl N)) hκ
    _ = 256 * κ := by ring

lemma ksum1 (hKb : ∀ n, |K p n 1| ≤ κ * (((n : ℝ) + 1) ^ 2 * Xp p ^ (n - 1)))
    (hK0 : K p 0 1 = 0) (N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 1| ≤ 256 * κ * p := by
  have hX := Xp_pos hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hwX : (p : ℝ) / 2 * Xp p = 1 / 2 := by
    have := Xp_mul_p hp; linear_combination this / 2
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k
  have hpt : ∀ a b : ℕ, ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 1| ≤ κ * p * (F a * F b) := by
    intro a b
    have hF : 0 ≤ κ * p * (F a * F b) := by positivity
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · rw [h0, hK0]; simpa using hF
    have h1 := hKb (a + b)
    have hXn : Xp p ^ (a + b - 1) = p * Xp p ^ (a + b) := by
      obtain ⟨m, hm⟩ : ∃ m, a + b = m + 1 := ⟨a + b - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ]
      linear_combination (-(Xp p ^ m)) * Xp_mul_p hp
    rw [hXn] at h1
    calc ((p : ℝ) / 2) ^ (a + b) * |K p (a + b) 1|
        ≤ ((p : ℝ) / 2) ^ (a + b) * (κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (p * Xp p ^ (a + b)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ * p * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (a + b)) := by
          rw [← hwX, mul_pow]; ring
      _ ≤ κ * p * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (1 / 2 : ℝ) ^ (a + b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sq_add_le a b) (by positivity))
            (by positivity)
      _ = κ * p * (F a * F b) := by simp only [F]; rw [pow_add]; ring
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ * p * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ * p * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ * p * 16 ^ 2 := mul_le_mul_of_nonneg_left
        (sum_mul_self_le F (fun k => by positivity) N (sum_sq_le (by norm_num) le_rfl N)) (by positivity)
    _ = 256 * κ * p := by ring

lemma ksumG (e : ℕ) (hKb : ∀ n, |K p n e| ≤ κ * (((n : ℝ) + 1) ^ 2 * Xp p ^ (n - e)))
    (hK0 : ∀ n, n < e → K p n e = 0) (N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, (1 : ℝ) ^ (a + b) * |K p (a + b) e| ≤ 256 * κ * ((e : ℝ) + 1) ^ 6 := by
  have hX := Xp_pos hp
  have hX1 : Xp p ≤ 1 := by linarith [Xp_le_half hp]
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * Xp p ^ (k - e)
  have hpt : ∀ a b : ℕ, (1 : ℝ) ^ (a + b) * |K p (a + b) e| ≤ κ * (F a * F b) := by
    intro a b
    rw [one_pow, one_mul]
    have hF : 0 ≤ κ * (F a * F b) := by positivity
    rcases lt_or_ge (a + b) e with hlt | hge
    · rw [hK0 _ hlt]; simpa using hF
    have h1 := hKb (a + b)
    have hXn : Xp p ^ (a + b - e) ≤ Xp p ^ (a - e) * Xp p ^ (b - e) := by
      rw [← pow_add]; exact pow_le_pow_of_le_one hX.le hX1 (by omega)
    calc |K p (a + b) e| ≤ κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * Xp p ^ (a + b - e)) := h1
      _ ≤ κ * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (Xp p ^ (a - e) * Xp p ^ (b - e))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (sq_add_le a b) hXn (by positivity) (by positivity)) hκ
      _ = κ * (F a * F b) := by simp only [F]; ring
  have hS := sum_sq_shift_le hX.le (Xp_le_half hp) e N
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ * (16 * ((e : ℝ) + 1) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_mul_self_le F (fun k => by positivity) N hS) hκ
    _ = 256 * κ * ((e : ℝ) + 1) ^ 6 := by ring

end Kernel

section Deligne

variable [DeligneBound]

/-- `wmass ≤ 64 M` from a kernel bound `M`. -/
lemma wmass_le' (K : ℕ → ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) {w : ℝ} (hw : 0 ≤ w) (hwX : w * Xp p ≤ 1 / 2)
    (e N : ℕ) {M : ℝ} (hM : ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * |K p (a + b) e| ≤ M) :
    ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, w ^ (i + j) * |γK K p e i j| ≤ 64 * M := by
  have h := wmass_le K p hw e N
  have hB := sumFi_le hp hw hwX N
  have hB0 : 0 ≤ ∑ k ∈ Icc 0 N, w ^ k * |Fi (p ^ k)| := sum_nonneg fun _ _ => by positivity
  have hA0 : 0 ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * |K p (a + b) e| :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  have hB2 : (∑ k ∈ Icc 0 N, w ^ k * |Fi (p ^ k)|) ^ 2 ≤ 64 := by nlinarith
  refine h.trans ?_
  calc _ ≤ M * 64 := mul_le_mul hM hB2 (by positivity) (hA0.trans hM)
    _ = 64 * M := by ring

/-! ### The lowest terms -/

lemma Icc01 : Icc 0 1 = ({0, 1} : Finset ℕ) := by ext x; simp only [mem_Icc, mem_insert, mem_singleton]; omega

lemma γK_00 (K : ℕ → ℕ → ℕ → ℝ) (p e : ℕ) : γK K p e 0 0 = K p 0 e := by
  simp [γK, alpha_one, Fi_one]

lemma γK_10 (K : ℕ → ℕ → ℕ → ℝ) (p e : ℕ) :
    γK K p e 1 0 = K p 0 e * Fi p + alpha p * K p 1 e := by
  unfold γK
  rw [Icc01, sum_pair (by norm_num)]
  simp [alpha_one, Fi_one]

lemma Fi_prime {p : ℕ} (hp : p.Prime) : Fi p = lam p ^ 2 * Xp p / 2 := by
  rw [Fi_apply, recF_gRm_prime hp, ← lam_prime_eq hp]; unfold Xp; ring

lemma alpha_prime' {p : ℕ} (hp : p.Prime) : alpha p = -lam p / 2 := by
  rw [alpha_prime hp, lam_prime_eq hp]

lemma Lc_10 {p : ℕ} (hp : p.Prime) : Lc p 1 0 = Xp p * rhoP p 1 := by simp [Lc]
lemma Lc_11 (p : ℕ) : Lc p 1 1 = 1 := by simp [Lc, RamanujanTau.HafnerBridge.lam_one]
lemma Lv_11 (p : ℕ) : Lv p 1 1 = Real.log p / 2 := by
  simp [Lv, RamanujanTau.HafnerBridge.lam_one]; ring

lemma abs_γl_010 {p : ℕ} (hp : p.Prime) : |γl p 0 1 0| ≤ 2 * Xp p ^ 2 := by
  have hX := Xp_pos hp
  have hl := lam_sq_le hp
  rw [← γK_Lc, γK_10, Lc_zero_zero hp, Lc_10 hp, rhoP_one hp, Fi_prime hp, alpha_prime' hp]
  have hXp : (p : ℝ)⁻¹ = Xp p := rfl
  rw [hXp]
  have h1X : 0 < 1 + Xp p := by linarith
  have e : 1 * (lam p ^ 2 * Xp p / 2) + -lam p / 2 * (Xp p * (lam p / (1 + Xp p))) =
      lam p ^ 2 * Xp p ^ 2 / (2 * (1 + Xp p)) := by field_simp; ring
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Xp p), mul_nonneg (sq_nonneg (Xp p)) (sq_nonneg (lam p))]

lemma abs_γl_110 {p : ℕ} (hp : p.Prime) : |γl p 1 1 0| = |lam p| / 2 := by
  rw [← γK_Lc, γK_10, Lc_11, alpha_prime' hp]
  simp [Lc, abs_div, abs_neg]

lemma abs_γLv_010 {p : ℕ} (hp : p.Prime) :
    |γK Lv p 0 1 0| ≤ lam p ^ 2 * Xp p * Real.log p / 4 + 2 * Xp p := by
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  have hl := lam_sq_le hp
  have hlog := log_p_nonneg hp
  have hXl := Xp_log_le_one hp
  rw [γK_10, Lv_zero_zero' hp, alpha_prime' hp]
  have hLv : Lv p 1 0 = Xp p * (-(1 / 2) * Real.log p * rhoP p 1 + rhoP' p 1) := by simp [Lv]
  have hr' : rhoP' p 1 = (p : ℝ)⁻¹ * Real.log p * lam p * lam (p ^ 0) / (1 + (p : ℝ)⁻¹) ^ 2 :=
    rhoP'_succ hp 0
  rw [hLv, rhoP_one hp, hr']
  simp only [pow_zero, RamanujanTau.HafnerBridge.lam_one, mul_one]
  have hXp : (p : ℝ)⁻¹ = Xp p := rfl
  rw [hXp]
  set X := Xp p
  set L := lam p
  set l := Real.log p
  have h1X : 0 < 1 + X := by linarith
  have e : 0 * Fi p + -L / 2 * (X * (-(1 / 2) * l * (L / (1 + X)) + X * l * L / (1 + X) ^ 2)) =
      L ^ 2 * X * l / (4 * (1 + X)) - L ^ 2 * X ^ 2 * l / (2 * (1 + X) ^ 2) := by
    field_simp; ring
  rw [e]
  have t1 : 0 ≤ L ^ 2 * X * l / (4 * (1 + X)) := by positivity
  have t2 : 0 ≤ L ^ 2 * X ^ 2 * l / (2 * (1 + X) ^ 2) := by positivity
  have u1 : L ^ 2 * X * l / (4 * (1 + X)) ≤ L ^ 2 * X * l / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ L ^ 2 * X * l := by positivity
    nlinarith
  have u2 : L ^ 2 * X ^ 2 * l / (2 * (1 + X) ^ 2) ≤ 2 * X := by
    rw [div_le_iff₀ (by positivity)]
    have : L ^ 2 * X ^ 2 * l ≤ 4 * X * (X * l) := by
      have : L ^ 2 * X ^ 2 * l = L ^ 2 * (X * (X * l)) := by ring
      rw [this]
      have : 0 ≤ X * (X * l) := by positivity
      nlinarith
    have : 4 * X * (X * l) ≤ 4 * X := by nlinarith
    nlinarith [sq_nonneg X]
  rw [abs_le]; constructor <;> linarith

lemma abs_γLv_110 {p : ℕ} (hp : p.Prime) : |γK Lv p 1 1 0| = |lam p| * Real.log p / 4 := by
  rw [γK_10, Lv_11, alpha_prime' hp]
  have hlog := log_p_nonneg hp
  simp only [Lv, Nat.lt_irrefl, zero_lt_one, if_true, zero_mul, zero_add]
  rw [abs_mul, abs_div, abs_neg, abs_div, abs_of_nonneg hlog]; norm_num; ring

/-! ### L1–L6 -/

lemma wp_ge_one {p : ℕ} (hp : p.Prime) : (1 : ℝ) ≤ (p : ℝ) / 2 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

lemma wp_X {p : ℕ} (hp : p.Prime) : (p : ℝ) / 2 * Xp p ≤ 1 / 2 := by
  have := Xp_mul_p hp; linarith

lemma inv_wp_sq {p : ℕ} (hp : p.Prime) : (((p : ℝ) / 2) ^ 2)⁻¹ = 4 * Xp p ^ 2 := by
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold Xp; field_simp; ring

/-- **L1.** -/
theorem Tl_zero_le {p : ℕ} (hp : p.Prime) (N : ℕ) : Tl p 0 N ≤ 1 + 65540 * Xp p ^ 2 := by
  have hX := Xp_pos hp
  have hs := split_low (fun i j => |γl p 0 i j|) (fun _ _ => abs_nonneg _) (wp_ge_one hp) N
  have hw := wmass_le' Lc hp (by have := wp_ge_one hp; linarith) (wp_X hp) 0 N
    (ksum0 Lc hp zero_le_one (fun n => by rw [one_mul]; exact abs_Lc_le hp n 0) N)
  rw [γK_Lc] at hw
  rw [inv_wp_sq hp] at hs
  have h00 : |γl p 0 0 0| = 1 := by rw [← γK_Lc, γK_00, Lc_zero_zero hp, abs_one]
  have h10 := abs_γl_010 hp
  have h01 : |γl p 0 0 1| ≤ 2 * Xp p ^ 2 := by rw [← γK_Lc, γK_symm, γK_Lc]; exact h10
  unfold Tl
  have : 4 * Xp p ^ 2 * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ((p : ℝ) / 2) ^ (i + j) * |γl p 0 i j| ≤
      4 * Xp p ^ 2 * (64 * (256 * 1)) := mul_le_mul_of_nonneg_left hw (by positivity)
  linarith

/-- **L2.** -/
theorem Tl_one_le {p : ℕ} (hp : p.Prime) (N : ℕ) : Tl p 1 N ≤ |lam p| + 65536 * Xp p := by
  have hX := Xp_pos hp
  have hs := split_low (fun i j => |γl p 1 i j|) (fun _ _ => abs_nonneg _) (wp_ge_one hp) N
  have hw := wmass_le' Lc hp (by have := wp_ge_one hp; linarith) (wp_X hp) 1 N
    (ksum1 Lc hp zero_le_one (fun n => by rw [one_mul]; exact abs_Lc_le hp n 1) (Lc_lt one_pos) N)
  rw [γK_Lc] at hw
  rw [inv_wp_sq hp] at hs
  have h00 : |γl p 1 0 0| = 0 := by rw [← γK_Lc, γK_00, Lc_lt one_pos, abs_zero]
  have h10 := abs_γl_110 hp
  have h01 : |γl p 1 0 1| = |lam p| / 2 := by rw [← γK_Lc, γK_symm, γK_Lc]; exact h10
  unfold Tl
  have hXp : 4 * Xp p ^ 2 * (64 * (256 * 1 * (p : ℝ))) = 65536 * Xp p := by
    have := Xp_mul_p hp; linear_combination (65536 * Xp p) * this
  have : 4 * Xp p ^ 2 * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ((p : ℝ) / 2) ^ (i + j) * |γl p 1 i j| ≤
      4 * Xp p ^ 2 * (64 * (256 * 1 * (p : ℝ))) := mul_le_mul_of_nonneg_left hw (by positivity)
  linarith

/-- **L3.** -/
theorem Tl_le {p : ℕ} (hp : p.Prime) (e N : ℕ) : Tl p e N ≤ 16384 * ((e : ℝ) + 1) ^ 6 := by
  have hw := wmass_le' Lc hp zero_le_one (by linarith [Xp_pos hp, Xp_le_half hp]) e N
    (ksumG Lc hp zero_le_one e (fun n => by rw [one_mul]; exact abs_Lc_le hp n e) (fun n hn => Lc_lt hn) N)
  rw [γK_Lc] at hw
  simp only [one_pow, one_mul] at hw
  unfold Tl
  linarith

/-- **L4.** -/
theorem TlV_zero_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    TlV p 0 N ≤ lam p ^ 2 * Xp p * Real.log p / 2 + 65540 * Xp p := by
  have hX := Xp_pos hp
  have hlog := log_p_nonneg hp
  have hs := split_low (fun i j => |γK Lv p 0 i j|) (fun _ _ => abs_nonneg _) (wp_ge_one hp) N
  have hw := wmass_le' Lv hp (by have := wp_ge_one hp; linarith) (wp_X hp) 0 N
    (ksum0 Lv hp hlog (fun n => abs_Lv_le hp n 0) N)
  rw [inv_wp_sq hp] at hs
  have h00 : |γK Lv p 0 0 0| = 0 := by rw [γK_00, Lv_zero_zero' hp, abs_zero]
  have h10 := abs_γLv_010 hp
  have h01 : |γK Lv p 0 0 1| ≤ lam p ^ 2 * Xp p * Real.log p / 4 + 2 * Xp p := by
    rw [γK_symm]; exact h10
  unfold TlV
  have : 4 * Xp p ^ 2 * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ((p : ℝ) / 2) ^ (i + j) * |γK Lv p 0 i j| ≤
      4 * Xp p ^ 2 * (64 * (256 * Real.log p)) := mul_le_mul_of_nonneg_left hw (by positivity)
  have hXl := Xp_log_le_one hp
  have : 4 * Xp p ^ 2 * (64 * (256 * Real.log p)) ≤ 65536 * Xp p := by
    have : 4 * Xp p ^ 2 * (64 * (256 * Real.log p)) = 65536 * Xp p * (Xp p * Real.log p) := by ring
    rw [this]; nlinarith
  linarith

/-- **L5.** -/
theorem TlV_one_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    TlV p 1 N ≤ Real.log p * (|lam p| / 2 + 65536 * Xp p) := by
  have hX := Xp_pos hp
  have hlog := log_p_nonneg hp
  have hs := split_low (fun i j => |γK Lv p 1 i j|) (fun _ _ => abs_nonneg _) (wp_ge_one hp) N
  have hw := wmass_le' Lv hp (by have := wp_ge_one hp; linarith) (wp_X hp) 1 N
    (ksum1 Lv hp hlog (fun n => abs_Lv_le hp n 1) (Lv_lt one_pos) N)
  rw [inv_wp_sq hp] at hs
  have h00 : |γK Lv p 1 0 0| = 0 := by rw [γK_00, Lv_lt one_pos, abs_zero]
  have h10 := abs_γLv_110 hp
  have h01 : |γK Lv p 1 0 1| = |lam p| * Real.log p / 4 := by rw [γK_symm]; exact h10
  unfold TlV
  have hXp : 4 * Xp p ^ 2 * (64 * (256 * Real.log p * (p : ℝ))) = 65536 * Xp p * Real.log p := by
    have := Xp_mul_p hp; linear_combination (65536 * Xp p * Real.log p) * this
  have : 4 * Xp p ^ 2 * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ((p : ℝ) / 2) ^ (i + j) * |γK Lv p 1 i j| ≤
      4 * Xp p ^ 2 * (64 * (256 * Real.log p * (p : ℝ))) := mul_le_mul_of_nonneg_left hw (by positivity)
  nlinarith

/-- **L6.** -/
theorem TlV_le {p : ℕ} (hp : p.Prime) (e N : ℕ) :
    TlV p e N ≤ 16384 * Real.log p * ((e : ℝ) + 1) ^ 6 := by
  have hw := wmass_le' Lv hp zero_le_one (by linarith [Xp_pos hp, Xp_le_half hp]) e N
    (ksumG Lv hp (log_p_nonneg hp) e (fun n => abs_Lv_le hp n e) (fun n hn => Lv_lt hn) N)
  simp only [one_pow, one_mul] at hw
  unfold TlV
  linarith

end Deligne

end RamanujanTau.QFProof5
