/-
# Soundness of the `span{J}` arithmetic

`JE.eval f = Σ_r f_r(z)·g_r` and `evY y F = Σ_k V(eval F_k)·y^k`. Every operation of `JArith` is
compatible with these evaluations; the multiplication table `gtab` is Atkin's (from R1 and R2).
`redP` preserves `evY y` whenever `y` is a root of the modular equation.
-/
import RamanujanTau.Atkin11Seed.JArith
import RamanujanTau.Atkin11ModEq

set_option autoImplicit false

namespace Atkin11Seed
open Atkin11 PowerSeries

/-! ### `ℤ[z]` -/

/-- Horner evaluation. -/
noncomputable def evZ (x : PS) : List Int → PS
  | [] => 0
  | a :: f => (a : PS) + x * evZ x f

lemma evZ_nil (x : PS) : evZ x [] = 0 := rfl
lemma evZ_cons (x : PS) (a : Int) (f : List Int) : evZ x (a :: f) = a + x * evZ x f := rfl

lemma evZ_addZ (x : PS) : ∀ f g : List Int, evZ x (addZ f g) = evZ x f + evZ x g
  | [], g => by simp [addZ, evZ]
  | a :: f, [] => by simp [addZ, evZ]
  | a :: f, b :: g => by
    simp only [addZ, evZ_cons, evZ_addZ x f g]; push_cast; ring

lemma evZ_smulZ (x : PS) (c : Int) : ∀ f : List Int, evZ x (smulZ c f) = c * evZ x f
  | [] => by simp [smulZ, evZ]
  | a :: f => by
    have := evZ_smulZ x c f
    simp only [smulZ, List.map_cons] at this ⊢
    rw [evZ_cons, evZ_cons, this]; push_cast; ring

lemma evZ_mulZ (x : PS) : ∀ f g : List Int, evZ x (mulZ f g) = evZ x f * evZ x g
  | [], g => by simp [mulZ, evZ]
  | a :: f, g => by
    rw [mulZ, evZ_addZ, evZ_smulZ, evZ_cons, evZ_mulZ x f g, evZ_cons]; push_cast; ring

lemma evZ_shiftZ (x : PS) (k : ℕ) (f : List Int) : evZ x (shiftZ k f) = x ^ k * evZ x f := by
  induction k with
  | zero => simp [shiftZ]
  | succ k ih =>
    simp only [shiftZ, List.replicate_succ, List.cons_append] at ih ⊢
    rw [evZ_cons, ih]; push_cast; ring

lemma evZ_zero (x : PS) : ∀ f : List Int, zeroZ f = true → evZ x f = 0
  | [], _ => rfl
  | a :: f, h => by
    simp only [zeroZ, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [evZ_cons, h.1, evZ_zero x f h.2]; simp

/-! ### `span{J}` -/

/-- `Σ_r f_r(z) g_r`. -/
noncomputable def JE.eval (f : JE) : PS :=
  evZ z f.c0 + evZ z f.c1 * g2 + evZ z f.c2 * g3 + evZ z f.c3 * g4 + evZ z f.c4 * g6

lemma JE.eval_zero : JE.zero.eval = 0 := by simp [JE.eval, JE.zero, evZ]

lemma JE.eval_add (f g : JE) : (JE.add f g).eval = f.eval + g.eval := by
  simp only [JE.eval, JE.add, evZ_addZ]; ring

lemma JE.eval_smul (c : Int) (f : JE) : (JE.smul c f).eval = c * f.eval := by
  simp only [JE.eval, JE.smul, evZ_smulZ]; ring

lemma JE.eval_zmul (p : List Int) (f : JE) : (JE.zmul p f).eval = evZ z p * f.eval := by
  simp only [JE.eval, JE.zmul, evZ_mulZ]; ring

lemma JE.eval_single (d : ℕ) (p : List Int) : (JE.single d p).eval = evZ z p * gi d := by
  rcases d with _ | _ | _ | _ | d <;> simp [JE.single, JE.eval, evZ, gi]

lemma JE.eval_comp (f : JE) : f.eval = ∑ r ∈ Finset.range 5, evZ z (f.comp r) * gi r := by
  simp [JE.eval, JE.comp, Finset.sum_range_succ, gi]

lemma JE.eval_isZero (f : JE) (h : f.isZero = true) : f.eval = 0 := by
  simp only [JE.isZero, Bool.and_eq_true] at h
  simp [JE.eval, evZ_zero z _ h.1.1.1.1, evZ_zero z _ h.1.1.1.2, evZ_zero z _ h.1.1.2, evZ_zero z _ h.1.2,
    evZ_zero z _ h.2]

/-- **Atkin's multiplication table**. -/
lemma gtab_spec (i r : ℕ) (hi : i < 5) (hr : r < 5) :
    gi i * gi r = ((gtab i r).map fun q => (q.2 : PS) * (z ^ (q.1 / 5) * gi (q.1 % 5))).sum := by
  have h1 := R1
  have h2 := r2_proved
  interval_cases i <;> interval_cases r
  · simp [gtab, gi]
  · simp [gtab, gi]
  · simp [gtab, gi]
  · simp [gtab, gi]
  · simp [gtab, gi]
  · simp [gtab, gi]
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (0) * h1 + (0) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (1) * h1 + (0) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (0) * h1 + (0) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 + g3) * h1 + (-g2 - 1) * h2
  · simp [gtab, gi]
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (1) * h1 + (0) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (0) * h1 + (1) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2) * h1 + (-1) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 ^ 2) * h1 + (-g2) * h2
  · simp [gtab, gi]
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (0) * h1 + (0) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2) * h1 + (-1) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g3) * h1 + (-g2) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 * g3 + 11 * z) * h1 + (-g2 ^ 2) * h2
  · simp [gtab, gi]
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 + g3) * h1 + (-g2 - 1) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 ^ 2) * h1 + (-g2) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 * g3 + 11 * z) * h1 + (-g2 ^ 2) * h2
  · simp only [gtab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceDiv, Nat.reduceMod, gi, g4, g6]
    linear_combination (g2 ^ 2 * g3 + 11 * g2 * z + z) * h1 + (-g2 ^ 3) * h2

lemma mulGr_eval (i r : ℕ) (hi : i < 5) (hr : r < 5) (p : List Int) :
    (mulGr i r p).eval = gi i * (evZ z p * gi r) := by
  have key : ∀ l : List (ℕ × ℤ), (l.foldr (fun q acc => JE.add (JE.single (q.1 % 5) (smulZ q.2 (shiftZ (q.1 / 5) p))) acc)
      JE.zero).eval = evZ z p * (l.map fun q => (q.2 : PS) * (z ^ (q.1 / 5) * gi (q.1 % 5))).sum := by
    intro l
    induction l with
    | nil => simp [JE.eval_zero]
    | cons q l ih =>
      rw [List.foldr_cons, JE.eval_add, ih, JE.eval_single, evZ_smulZ, evZ_shiftZ, List.map_cons, List.sum_cons]
      ring
  rw [mulGr, key, ← gtab_spec i r hi hr]; ring

lemma mulG_eval (i : ℕ) (hi : i < 5) (f : JE) : (mulG i f).eval = gi i * f.eval := by
  rw [mulG, JE.eval_add, JE.eval_add, JE.eval_add, JE.eval_add, mulGr_eval i 0 hi (by norm_num),
    mulGr_eval i 1 hi (by norm_num), mulGr_eval i 2 hi (by norm_num), mulGr_eval i 3 hi (by norm_num),
    mulGr_eval i 4 hi (by norm_num)]
  simp only [JE.eval, gi]; ring

lemma mulJ_eval (f g : JE) : (mulJ f g).eval = f.eval * g.eval := by
  simp only [mulJ, JE.eval_add, JE.eval_zmul, mulG_eval 1 (by norm_num), mulG_eval 2 (by norm_num),
    mulG_eval 3 (by norm_num), mulG_eval 4 (by norm_num)]
  simp only [JE.eval, gi]; ring

/-! ### `span{J}[Y]` -/

/-- `Σ_k V(eval F_k)·y^k`. -/
noncomputable def evY (y : PS) : PY → PS
  | [] => 0
  | a :: f => V a.eval + y * evY y f

lemma evY_nil (y : PS) : evY y [] = 0 := rfl
lemma evY_cons (y : PS) (a : JE) (f : PY) : evY y (a :: f) = V a.eval + y * evY y f := rfl

lemma evY_addY (y : PS) : ∀ f g : PY, evY y (addY f g) = evY y f + evY y g
  | [], g => by simp [addY, evY]
  | a :: f, [] => by simp [addY, evY]
  | a :: f, b :: g => by
    simp only [addY, evY_cons, evY_addY y f g, JE.eval_add, map_add]; ring

lemma evY_smulY (y : PS) (c : Int) : ∀ f : PY, evY y (smulY c f) = c * evY y f
  | [] => by simp [smulY, evY]
  | a :: f => by
    have := evY_smulY y c f
    simp only [smulY, List.map_cons] at this ⊢
    rw [evY_cons, evY_cons, this, JE.eval_smul, map_mul, map_intCast]; ring

lemma evY_map_mulJ (y : PS) (a : JE) : ∀ g : PY, evY y (g.map (mulJ a)) = V a.eval * evY y g
  | [] => by simp [evY]
  | b :: g => by
    rw [List.map_cons, evY_cons, evY_cons, evY_map_mulJ y a g, mulJ_eval, map_mul]; ring

lemma evY_jmulY (y : PS) (e : JE) : ∀ f : PY, evY y (jmulY e f) = V e.eval * evY y f
  | [] => by simp [jmulY, evY]
  | a :: f => by
    have := evY_jmulY y e f
    simp only [jmulY, List.map_cons] at this ⊢
    rw [evY_cons, evY_cons, this, mulJ_eval, map_mul]; ring

lemma evY_mulY (y : PS) : ∀ f g : PY, evY y (mulY f g) = evY y f * evY y g
  | [], g => by simp [mulY, evY]
  | a :: f, g => by
    rw [mulY, evY_addY, evY_map_mulJ, evY_cons, evY_mulY y f g, evY_cons, JE.eval_zero, map_zero]; ring

lemma evY_isZero (y : PS) : ∀ f : PY, isZeroY f = true → evY y f = 0
  | [], _ => rfl
  | a :: f, h => by
    simp only [isZeroY, List.all_cons, Bool.and_eq_true] at h
    rw [evY_cons, JE.eval_isZero a h.1, evY_isZero y f h.2]; simp

/-! ### the reduction modulo the modular equation -/

lemma eJ_eval (j : ℕ) (hj : j < 11) : (eJ (j + 1)).eval = lc (eF (j + 1)) := by
  interval_cases j <;>
    simp [eJ, JE.eval, evZ, lcE1, lcE2, lcE3, lcE4, lcE5, lcE6, lcE7, lcE8, lcE9, lcE10, lcE11, g4] <;> ring

/-- high-degree-first evaluation. -/
noncomputable def evH (y : PS) : List JE → PS
  | [] => 0
  | a :: rest => V a.eval * y ^ rest.length + evH y rest

lemma evH_append (y : PS) (l : List JE) (a : JE) : evH y (l ++ [a]) = y * evH y l + V a.eval := by
  induction l with
  | nil => simp [evH]
  | cons b l ih => rw [List.cons_append, evH, ih, evH, List.length_append]; simp; ring

lemma evY_eq_evH (y : PS) : ∀ f : PY, evY y f = evH y f.reverse
  | [] => rfl
  | a :: f => by
    rw [evY_cons, List.reverse_cons, evH_append, ← evY_eq_evH y f]; ring

lemma stepH_length (t : JE) : ∀ (j : ℕ) (rest : List JE), (stepH t j rest).length = rest.length
  | _, [] => rfl
  | j, a :: rest => by simp [stepH, stepH_length t (j + 1) rest]

lemma evH_stepH (y : PS) (t : JE) : ∀ (j : ℕ) (rest : List JE),
    evH y (stepH t j rest) = evH y rest + V t.eval * ∑ k ∈ Finset.range rest.length,
      (if j + k < 11 then (-1) ^ (j + k) * V (eJ (j + k + 1)).eval else 0) * y ^ (rest.length - 1 - k)
  | _, [] => by simp [stepH, evH]
  | j, a :: rest => by
    rw [stepH, evH, evH_stepH y t (j + 1) rest, stepH_length, evH, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.add_zero, show ∀ k, j + 1 + k = j + (k + 1) from fun k => by ring,
      show ∀ k, rest.length + 1 - 1 - (k + 1) = rest.length - 1 - k from fun k => by omega,
      show rest.length + 1 - 1 - 0 = rest.length from by omega]
    split_ifs with h
    · rw [JE.eval_add, mulJ_eval, JE.eval_smul, map_add, map_mul, map_mul, map_intCast]; push_cast; ring
    · ring

/-- the modular equation as `Y¹¹ = Σ_j (−1)^j V(e_{j+1}) Y^{10−j}`. -/
def IsRoot (y : PS) : Prop := y ^ 11 = ∑ j ∈ Finset.range 11, (-1) ^ j * V (lc (eF (j + 1))) * y ^ (10 - j)

lemma φ_isRoot : IsRoot φ := modeq_proved

lemma evH_redH (y : PS) (hy : IsRoot y) : ∀ (n : ℕ) (h : List JE), evH y (redH n h) = evH y h
  | 0, h => rfl
  | _ + 1, [] => rfl
  | n + 1, t :: rest => by
    rw [redH]
    split_ifs with hl
    · rfl
    rw [evH_redH y hy n, evH_stepH, evH]
    have hsum : ∑ k ∈ Finset.range rest.length,
        (if 0 + k < 11 then (-1) ^ (0 + k) * V (eJ (0 + k + 1)).eval else 0) * y ^ (rest.length - 1 - k)
        = y ^ (rest.length - 11) * y ^ 11 := by
      obtain ⟨m, hm⟩ : ∃ m, rest.length = m + 11 := ⟨rest.length - 11, by omega⟩
      rw [hm, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 11) (by omega : 11 ≤ m + 11)]
      rw [Finset.sum_eq_zero (s := Finset.Ico 11 (m + 11)) (fun k hk => by
        rw [Finset.mem_Ico] at hk; rw [if_neg (by omega), zero_mul]), add_zero, hy,
        show m + 11 - 11 = m by omega, Finset.mul_sum, ← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [if_pos (by omega), zero_add, eJ_eval k hk, show m + 11 - 1 - k = m + (10 - k) by omega, pow_add]
      ring
    rw [hsum, ← pow_add, show rest.length - 11 + 11 = rest.length by omega]
    ring

theorem evY_redP (y : PS) (hy : IsRoot y) (f : PY) : evY y (redP f) = evY y f := by
  rw [redP, evY_eq_evH, List.reverse_reverse, evH_redH y hy, ← evY_eq_evH]

end Atkin11Seed
