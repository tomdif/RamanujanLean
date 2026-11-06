/-
# The local derivative identity for the actual `ρ_p`, `ρ'_p` (unconditional)

`dloc_sym`: `Σ_{e≤min(a,b)} [log p·wd_e L(a,e)L(b,e) + W_e (L'(a,e)L(b,e) + L(a,e)L'(b,e))]
  = X^{max} (−½|a−b| log p ρ_p(|a−b|) + ρ'_p(|a−b|))`,

with `L'(a,0) = X^a(−½a log p ρ_p(a) + ρ'_p(a))`, `L'(a,e) = (e − a/2) log p X^{a−e} λ(p^{a−e})`.
-/
import RamanujanTau.QFProof3.Decomp
import RamanujanTau.QFProof3.DChol
import RamanujanTau.QFProof2.RhoDeriv

set_option autoImplicit false

namespace RamanujanTau.QFProof3

open Finset RamanujanTau.HafnerBridge RamanujanTau.QFProof RamanujanTau.QFProof2

/-- `|a − b|` on `ℕ`. -/
def dist' (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

/-- The derivative columns `L'`. -/
noncomputable def Lv (p a e : ℕ) : ℝ :=
  if a < e then 0 else if e = 0 then
    Xp p ^ a * (-(1 / 2) * (a : ℝ) * Real.log p * rhoP p a + rhoP' p a)
  else ((e : ℝ) - a / 2) * Real.log p * (Xp p ^ (a - e) * lam (p ^ (a - e)))

/-- The local derivative kernel. -/
noncomputable def kd (p a b : ℕ) : ℝ :=
  Xp p ^ (max a b) * (-(1 / 2) * (dist' a b : ℝ) * Real.log p * rhoP p (dist' a b) + rhoP' p (dist' a b))

lemma rd_muP {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Real.log p * rd (lam p) (Xp p) (muP p) n = rhoP' p n := by
  rcases n with _ | a
  · simp [rd, muP, rhoP'_zero hp]
  · rw [rhoP'_succ hp, rd, muP_succ]; ring

lemma Lv_zero_zero (p : ℕ) {hp : p.Prime} : Lv p 0 0 = 0 := by
  simp [Lv, rhoP'_zero hp]

lemma dloc {p : ℕ} (hp : p.Prime) (a n : ℕ) :
    ∑ e ∈ Icc 0 a, (Real.log p * wd (lam p) (Xp p) e * Lc p a e * Lc p (a + n) e +
      Wc (lam p) (Xp p) e * (Lv p a e * Lc p (a + n) e + Lc p a e * Lv p (a + n) e)) =
      Xp p ^ (a + n) * (-(1 / 2) * (n : ℝ) * Real.log p * rhoP p n + rhoP' p n) := by
  have h1 := dchol_loc (l := lam p) (X := Xp p) (μ := muP p) (by simp [muP]) (by simp [muP, lam_one])
    (muP_rec hp) (one_add_X_pos p).ne' n a
  have h2 := chol_rhoP hp n a
  simp only [rr_muP hp] at h1
  have hI : Icc 0 a = range (a + 1) := by ext; simp only [mem_Icc, mem_range]; omega
  rw [hI, sum_range_succ']
  set S1 := ∑ i ∈ range a, (wd (lam p) (Xp p) (a - i) + ((a : ℝ) - 2 * i) * Wc (lam p) (Xp p) (a - i)) *
        Xp p ^ (n + 2 * i) * muP p (i + 1) * muP p (i + n + 1) with hS1
  set S2 := ∑ i ∈ range a, Wc (lam p) ((p : ℝ)⁻¹) (a - i) * ((p : ℝ)⁻¹) ^ (n + 2 * i) *
        lam (p ^ i) * lam (p ^ (i + n)) with hS2
  have hsum : ∑ e ∈ range a, (Real.log p * wd (lam p) (Xp p) (e + 1) * Lc p a (e + 1) * Lc p (a + n) (e + 1) +
      Wc (lam p) (Xp p) (e + 1) * (Lv p a (e + 1) * Lc p (a + n) (e + 1) + Lc p a (e + 1) * Lv p (a + n) (e + 1))) =
      Real.log p * S1 - (1 / 2) * (n : ℝ) * Real.log p * S2 := by
    rw [hS1, hS2, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hia : i < a := mem_range.1 hi
    rw [show a - 1 - i + 1 = a - i by omega]
    have e1 : ¬ a < a - i := by omega
    have e2 : ¬ a + n < a - i := by omega
    have e3 : a - i ≠ 0 := by omega
    simp only [Lc, Lv, e1, e2, e3, if_false]
    rw [show a - (a - i) = i by omega, show a + n - (a - i) = i + n by omega, muP_succ,
      show i + n + 1 = (i + n) + 1 by ring, muP_succ]
    rw [Nat.cast_sub hia.le]
    push_cast
    rw [show n + 2 * i = i + (i + n) by ring, pow_add]
    ring
  have h0 : Real.log p * wd (lam p) (Xp p) 0 * Lc p a 0 * Lc p (a + n) 0 +
      Wc (lam p) (Xp p) 0 * (Lv p a 0 * Lc p (a + n) 0 + Lc p a 0 * Lv p (a + n) 0) =
      Xp p ^ (2 * a + n) * ((Real.log p * rd (lam p) (Xp p) (muP p) a - (a : ℝ) * Real.log p * rhoP p a) *
        rhoP p (a + n) + rhoP p a * (Real.log p * rd (lam p) (Xp p) (muP p) (a + n))) -
      (1 / 2) * (n : ℝ) * Real.log p * (Xp p ^ (2 * a + n) * rhoP p a * rhoP p (a + n)) := by
    simp only [Lc, Lv, Nat.not_lt_zero, if_false, if_true, Wc, wd, rd_muP hp]
    rw [show 2 * a + n = a + (a + n) by ring, pow_add]
    push_cast
    ring
  rw [hsum, h0, ← rd_muP hp n]
  have hX : Xp p = (p : ℝ)⁻¹ := rfl
  rw [hX] at h1 ⊢
  linear_combination (-Real.log p) * h1 + (1 / 2) * (n : ℝ) * Real.log p * h2

lemma dloc_le {p : ℕ} (hp : p.Prime) {a b : ℕ} (hab : a ≤ b) :
    ∑ e ∈ Icc 0 (min a b), (Real.log p * wd (lam p) (Xp p) e * Lc p a e * Lc p b e +
      Wc (lam p) (Xp p) e * (Lv p a e * Lc p b e + Lc p a e * Lv p b e)) = kd p a b := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  rw [min_eq_left hab, dloc hp, kd, max_eq_right hab, dist', if_pos hab, Nat.add_sub_cancel_left]

lemma dloc_sym {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ∑ e ∈ Icc 0 (min a b), (Real.log p * wd (lam p) (Xp p) e * Lc p a e * Lc p b e +
      Wc (lam p) (Xp p) e * (Lv p a e * Lc p b e + Lc p a e * Lv p b e)) = kd p a b := by
  rcases le_total a b with hab | hab
  · exact dloc_le hp hab
  · have := dloc_le hp hab
    have hk : kd p b a = kd p a b := by
      unfold kd dist'
      rw [max_comm]
      rcases eq_or_lt_of_le hab with h | h
      · subst h; rfl
      · rw [if_pos hab, if_neg (by omega)]
    rw [min_comm, ← hk, ← this]
    exact sum_congr rfl fun e _ => by ring

end RamanujanTau.QFProof3
