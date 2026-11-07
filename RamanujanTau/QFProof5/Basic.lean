/-
# Pointwise local bounds under `[DeligneBound]`

With `X = 1/p`:

* `abs_lam_pp_le`: `|λ(p^j)| ≤ j+1` (Chebyshev, `VoronoiPointwise.cheb_bound`);
* `abs_rhoP_le`: `|ρ_p(n)| ≤ n+1`; `abs_rhoP'_le`: `|ρ'_p(n)| ≤ n log p`;
* `abs_Lc_le`: `|L_p(n,e)| ≤ (n+1)² X^{n−e}`; `abs_Lv_le`: `|L'_p(n,e)| ≤ log p (n+1)² X^{n−e}`;
* `abs_Fi_le`: `|Fi(p^k)| ≤ (k+1)(k+2)/2 · X^k`;
* `abs_Wc_le`: `|W_p(e)| ≤ X^e`; `abs_wd_le`: `|wd_p(e)| ≤ 8(e+1) X^e`.
-/
import RamanujanTau.QFProof4.GammaMultV
import RamanujanTau.VoronoiPointwise.DeligneTau
import RamanujanTau.QFProof5.Sums

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset RamanujanTau.QFProof RamanujanTau.QFProof2 RamanujanTau.QFProof3 RamanujanTau.QFProof4
open RamanujanTau.HafnerBridge (lam rhoP rhoP')

lemma lam_prime_eq {p : ℕ} (hp : p.Prime) : lam p = RamanujanTau.EdgeNonvanishing.lam p := by
  have h := lam_pp hp 1
  rw [pow_one] at h
  rw [h]; rfl

lemma Xp_pos {p : ℕ} (hp : p.Prime) : 0 < Xp p := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact inv_pos.2 this

lemma Xp_le_half {p : ℕ} (hp : p.Prime) : Xp p ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold Xp
  rw [inv_le_comm₀ (by linarith) (by norm_num), one_div, inv_inv]; exact this

lemma Xp_mul_p {p : ℕ} (hp : p.Prime) : Xp p * p = 1 := by
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold Xp; field_simp

lemma log_le_p {p : ℕ} (hp : p.Prime) : Real.log p ≤ p := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have := Real.log_le_sub_one_of_pos this
  linarith

lemma Xp_log_le_one {p : ℕ} (hp : p.Prime) : Xp p * Real.log p ≤ 1 := by
  have h := log_le_p hp
  have hX := Xp_pos hp
  have := mul_le_mul_of_nonneg_left h hX.le
  rw [Xp_mul_p hp] at this
  exact this

lemma log_p_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log p :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

section Deligne

variable [DeligneBound]

lemma lam_sq_le {p : ℕ} (hp : p.Prime) : lam p ^ 2 ≤ 4 := by
  rw [lam_prime_eq hp]; exact RamanujanTau.SelbergCoeffs.lam_sq_le_four hp

lemma abs_lam_pp_le {p : ℕ} (hp : p.Prime) (j : ℕ) : |lam (p ^ j)| ≤ (j : ℝ) + 1 :=
  RamanujanTau.VoronoiPointwise.cheb_bound (fun k => lam (p ^ k)) (lam p) (lam_sq_le hp)
    (lamp_zero p) (by simp only [pow_one]) (fun k => by
      have := lamp_rec hp k; rw [pow_one] at this; exact this) j

lemma abs_lam_le_two {p : ℕ} (hp : p.Prime) : |lam p| ≤ 2 := by
  have := abs_lam_pp_le hp 1
  rw [pow_one] at this; norm_num at this; linarith

lemma abs_rhoP_le {p : ℕ} (hp : p.Prime) (n : ℕ) : |rhoP p n| ≤ (n : ℝ) + 1 := by
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  have h1X : 0 < 1 + (p : ℝ)⁻¹ := one_add_X_pos p
  rcases n with _ | n
  · rw [rhoP_zero hp]; simp
  rcases n with _ | a
  · rw [rhoP_one hp, abs_div, abs_of_pos h1X, div_le_iff₀ h1X]
    have := abs_lam_le_two hp
    have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := hX.le
    push_cast; nlinarith
  · rw [rhoP_add_two hp, abs_div, abs_of_pos h1X, div_le_iff₀ h1X]
    have h1 := abs_lam_pp_le hp (a + 2)
    have h2 := abs_lam_pp_le hp a
    have hXp : (p : ℝ)⁻¹ = Xp p := rfl
    rw [hXp] at h1X ⊢
    have : |lam (p ^ (a + 2)) - Xp p * lam (p ^ a)| ≤ |lam (p ^ (a + 2))| + Xp p * |lam (p ^ a)| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos hX]
    push_cast at h1 ⊢
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith

lemma abs_rhoP'_le {p : ℕ} (hp : p.Prime) (n : ℕ) : |rhoP' p n| ≤ (n : ℝ) * Real.log p := by
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  have hl := log_p_nonneg hp
  rcases n with _ | a
  · rw [rhoP'_zero hp]; simp
  rw [rhoP'_succ hp]
  have hXp : (p : ℝ)⁻¹ = Xp p := rfl
  rw [hXp]
  have h1X : 1 ≤ (1 + Xp p) ^ 2 := by nlinarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + Xp p) ^ 2), div_le_iff₀ (by positivity)]
  have hl1 := abs_lam_le_two hp
  have hl2 := abs_lam_pp_le hp a
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos hX, abs_of_nonneg hl]
  have e1 : |lam p| * |lam (p ^ a)| ≤ 2 * ((a : ℝ) + 1) :=
    mul_le_mul hl1 hl2 (abs_nonneg _) (by norm_num)
  have e2 : Xp p * Real.log p * |lam p| * |lam (p ^ a)| ≤ Xp p * Real.log p * (2 * ((a : ℝ) + 1)) := by
    rw [mul_assoc (Xp p * Real.log p)]
    exact mul_le_mul_of_nonneg_left e1 (by positivity)
  push_cast
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have e3 : Xp p * Real.log p * (2 * ((a : ℝ) + 1)) ≤ ((a : ℝ) + 1) * Real.log p := by
    have : 2 * Xp p ≤ 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * Xp p)
      (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * Real.log p)]
  have e4 : ((a : ℝ) + 1) * Real.log p ≤ ((a : ℝ) + 1) * Real.log p * (1 + Xp p) ^ 2 := by
    have : 0 ≤ ((a : ℝ) + 1) * Real.log p := by positivity
    nlinarith
  linarith

lemma Lc_lt {p n e : ℕ} (h : n < e) : Lc p n e = 0 := by simp [Lc, h]
lemma Lv_lt {p n e : ℕ} (h : n < e) : Lv p n e = 0 := by simp [Lv, h]

lemma abs_Lc_le {p : ℕ} (hp : p.Prime) (n e : ℕ) :
    |Lc p n e| ≤ ((n : ℝ) + 1) ^ 2 * Xp p ^ (n - e) := by
  have hX := Xp_pos hp
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hXe : 0 < Xp p ^ (n - e) := pow_pos hX _
  unfold Lc
  split_ifs with h1 h2
  · simp; positivity
  · subst h2
    rw [abs_mul, abs_of_pos (pow_pos hX _), Nat.sub_zero, mul_comm]
    exact mul_le_mul_of_nonneg_right ((abs_rhoP_le hp n).trans hsq) (pow_pos hX _).le
  · rw [abs_mul, abs_of_pos hXe, mul_comm]
    refine mul_le_mul_of_nonneg_right ((abs_lam_pp_le hp (n - e)).trans ?_) hXe.le
    refine le_trans ?_ hsq
    have : ((n - e : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n e
    linarith

lemma abs_Lv_le {p : ℕ} (hp : p.Prime) (n e : ℕ) :
    |Lv p n e| ≤ Real.log p * (((n : ℝ) + 1) ^ 2 * Xp p ^ (n - e)) := by
  have hX := Xp_pos hp
  have hl := log_p_nonneg hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXe : 0 < Xp p ^ (n - e) := pow_pos hX _
  unfold Lv
  split_ifs with h1 h2
  · simp; positivity
  · subst h2
    rw [abs_mul, abs_of_pos (pow_pos hX _), Nat.sub_zero]
    have hr := abs_rhoP_le hp n
    have hr' := abs_rhoP'_le hp n
    have : |-(1 / 2) * (n : ℝ) * Real.log p * rhoP p n + rhoP' p n| ≤
        Real.log p * ((n : ℝ) + 1) ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg hn0]
      norm_num
      have : (1 / 2 : ℝ) * n * Real.log p * |rhoP p n| ≤ (1 / 2 : ℝ) * n * Real.log p * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      nlinarith [mul_nonneg hl (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2 + n / 2 + 1)]
    calc Xp p ^ n * |-(1 / 2) * (n : ℝ) * Real.log p * rhoP p n + rhoP' p n|
        ≤ Xp p ^ n * (Real.log p * ((n : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left this (pow_pos hX _).le
      _ = _ := by ring
  · push Not at h1
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hXe, abs_of_nonneg hl]
    have he : (1 : ℝ) ≤ e := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h2
    have hen : (e : ℝ) ≤ n := by exact_mod_cast h1
    have h3 : |(e : ℝ) - n / 2| ≤ (n : ℝ) + 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |lam (p ^ (n - e))| ≤ (n : ℝ) + 1 := by
      refine (abs_lam_pp_le hp (n - e)).trans ?_
      have : ((n - e : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n e
      linarith
    have h5 : |(e : ℝ) - n / 2| * |lam (p ^ (n - e))| ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [sq]; exact mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
    calc |(e : ℝ) - n / 2| * Real.log p * (Xp p ^ (n - e) * |lam (p ^ (n - e))|)
        = Real.log p * Xp p ^ (n - e) * (|(e : ℝ) - n / 2| * |lam (p ^ (n - e))|) := by ring
      _ ≤ Real.log p * Xp p ^ (n - e) * ((n : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring

lemma abs_Fi_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |Fi (p ^ k)| ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * Xp p ^ k := by
  have hX := Xp_pos hp
  rw [Fi_apply, abs_div, Nat.cast_pow,
    abs_of_pos (pow_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p) k)]
  have hXk : Xp p ^ k = 1 / (p : ℝ) ^ k := by unfold Xp; rw [inv_pow, one_div]
  rw [hXk, mul_one_div]
  exact div_le_div_of_nonneg_right (abs_recF_gRm_ppow hp k) (pow_pos (by exact_mod_cast hp.pos) k).le

lemma qq_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ qq (lam p) (Xp p) ∧ qq (lam p) (Xp p) ≤ (1 + Xp p) ^ 2 := by
  have hX := Xp_pos hp
  have hl := lam_sq_le hp
  unfold qq
  constructor
  · nlinarith [sq_nonneg (1 - Xp p)]
  · nlinarith [sq_nonneg (lam p)]

lemma abs_Wc_le {p : ℕ} (hp : p.Prime) (e : ℕ) : |Wc (lam p) (Xp p) e| ≤ Xp p ^ e := by
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  obtain ⟨hq0, hq1⟩ := qq_bounds hp
  match e with
  | 0 => simp [Wc]
  | 1 =>
    simp only [Wc, pow_one]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  | (f + 2) =>
    simp only [Wc]
    have h1 : 0 ≤ (1 - Xp p) * qq (lam p) (Xp p) / (1 + Xp p) :=
      div_nonneg (mul_nonneg (by linarith) hq0) (by positivity)
    have h2 : (1 - Xp p) * qq (lam p) (Xp p) / (1 + Xp p) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ 1 - Xp p), sq_nonneg (Xp p)]
    rw [abs_of_nonneg (mul_nonneg (pow_pos hX _).le h1)]
    calc Xp p ^ (f + 2) * ((1 - Xp p) * qq (lam p) (Xp p) / (1 + Xp p))
        ≤ Xp p ^ (f + 2) * 1 := mul_le_mul_of_nonneg_left h2 (pow_pos hX _).le
      _ = _ := mul_one _

lemma abs_wd_le {p : ℕ} (hp : p.Prime) (e : ℕ) :
    |wd (lam p) (Xp p) e| ≤ 8 * ((e : ℝ) + 1) * Xp p ^ e := by
  have hX := Xp_pos hp
  have hX2 := Xp_le_half hp
  have hl := lam_sq_le hp
  obtain ⟨hq0, hq1⟩ := qq_bounds hp
  have hqd : |qd (lam p) (Xp p)| ≤ 7 := by
    unfold qd; rw [abs_le]; constructor <;> nlinarith [sq_nonneg (lam p)]
  set q := qq (lam p) (Xp p)
  set X := Xp p
  have h1X : 1 ≤ 1 + X := by linarith
  have hq1' : q / (1 + X) ^ 2 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hq0' : 0 ≤ q / (1 + X) ^ 2 := by positivity
  match e with
  | 0 => simp [wd]
  | 1 =>
    simp only [wd]
    have a1 : |X * qd (lam p) X / (1 + X) ^ 2| ≤ 7 * X := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos (by positivity : (0 : ℝ) < (1 + X) ^ 2),
        div_le_iff₀ (by positivity)]
      have : 1 ≤ (1 + X) ^ 2 := by nlinarith
      nlinarith
    have a2 : |2 * X * q / (1 + X) ^ 3| ≤ 2 * X := by
      have : 2 * X * q / (1 + X) ^ 3 = 2 * X * (q / (1 + X) ^ 2) / (1 + X) := by
        field_simp
      rw [this, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      have : 2 * X * (q / (1 + X) ^ 2) ≤ 2 * X * 1 := mul_le_mul_of_nonneg_left hq1' (by positivity)
      nlinarith
    have a3 : |q / (1 + X) ^ 2 + X * qd (lam p) X / (1 + X) ^ 2 - 2 * X * q / (1 + X) ^ 3| ≤ 1 + 9 * X := by
      refine (abs_sub _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) a2).trans ?_
      rw [abs_of_nonneg hq0']
      linarith
    rw [abs_mul, abs_neg, abs_of_pos hX]
    calc X * |q / (1 + X) ^ 2 + X * qd (lam p) X / (1 + X) ^ 2 - 2 * X * q / (1 + X) ^ 3|
        ≤ X * (1 + 9 * X) := mul_le_mul_of_nonneg_left a3 hX.le
      _ ≤ 8 * (((1 : ℕ) : ℝ) + 1) * X ^ 1 := by push_cast; nlinarith
  | (f + 2) =>
    simp only [wd]
    have hcc0 : 0 ≤ cc (lam p) X := div_nonneg (mul_nonneg (by linarith) hq0) (by linarith)
    have hcc1 : cc (lam p) X ≤ 1 := by
      unfold cc; rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ 1 - X), sq_nonneg X]
    have hccd : |ccd (lam p) X| ≤ 12 := by
      unfold ccd
      have b1 : |(-q + (1 - X) * qd (lam p) X) / (1 + X)| ≤ 9 := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + X), div_le_iff₀ (by linarith)]
        have : |(-q + (1 - X) * qd (lam p) X)| ≤ q + (1 - X) * 7 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_of_nonneg hq0, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - X)]
          have : (1 - X) * |qd (lam p) X| ≤ (1 - X) * 7 := mul_le_mul_of_nonneg_left hqd (by linarith)
          linarith
        nlinarith
      have b2 : |(1 - X) * q / (1 + X) ^ 2| ≤ 3 := by
        rw [abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) hq0) (by positivity)),
          div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ 1 - X)]
      refine (abs_sub _ _).trans ?_
      linarith
    have hXf : 0 < X ^ (f + 2) := pow_pos hX _
    rw [abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hXf, abs_of_nonneg hcc0, abs_of_pos (pow_pos hX _)]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (f : ℝ) + 2)]
    have c1 : ((f : ℝ) + 2) * X ^ (f + 2) * cc (lam p) X ≤ ((f : ℝ) + 2) * X ^ (f + 2) :=
      by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (f : ℝ) + 2) hXf.le]
    have c2 : X ^ (f + 3) * |ccd (lam p) X| ≤ X ^ (f + 2) * 6 := by
      rw [pow_succ]
      have : X * |ccd (lam p) X| ≤ 6 := by nlinarith [abs_nonneg (ccd (lam p) X)]
      nlinarith
    nlinarith

end Deligne

end RamanujanTau.QFProof5
