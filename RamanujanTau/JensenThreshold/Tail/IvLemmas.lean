/-
# Soundness of the composite interval routines used by `checkBox`
-/
import RamanujanTau.JensenThreshold.Tail.Interval
import RamanujanTau.JensenThreshold.Tail.Model

set_option autoImplicit false

namespace JensenThreshold.Tail

open Iv Finset

lemma mem_zeroI : (0 : ℝ) ∈ᵢ zeroI := by simpa using mem_ofInt 0
lemma mem_oneI : (1 : ℝ) ∈ᵢ oneI := mem_one

lemma mem_between {x y z : ℝ} {I : Iv} (hx : x ∈ᵢ I) (hy : y ∈ᵢ I) (h1 : x ≤ z) (h2 : z ≤ y) : z ∈ᵢ I :=
  ⟨le_trans hx.1 h1, le_trans h2 hy.2⟩

lemma mem_of_bounds {z : ℝ} {I : Iv} (h1 : (I.lo : ℝ) / S ≤ z) (h2 : z ≤ (I.hi : ℝ) / S) : z ∈ᵢ I := ⟨h1, h2⟩

lemma mem_ofFrac' (p q : ℤ) (hq : 0 < q) {x : ℝ} (hx : x = (p : ℝ) / q) : x ∈ᵢ Iv.ofFrac p q := by
  rw [hx]; exact mem_ofFrac p q hq

lemma mem_ofInt' (p : ℤ) {x : ℝ} (hx : x = (p : ℝ)) : x ∈ᵢ Iv.ofInt p := by rw [hx]; exact mem_ofInt p

lemma mem_evalQIv (Q : UWZ) {u ω : ℝ} {Iu Iω : Iv} (hu : u ∈ᵢ Iu) (hω : ω ∈ᵢ Iω) :
    evalQZ Q u ω ∈ᵢ evalQIv Q Iu Iω := by
  induction Q with
  | nil => simpa [evalQZ, evalQIv] using mem_zeroI
  | cons x Q ih =>
    have e : evalQZ (x :: Q) u ω = (x.2.2 : ℝ) * u ^ x.1 * ω ^ x.2.1 + evalQZ Q u ω := by
      simp [evalQZ]
    rw [e]
    exact mem_add (mem_mul (mem_mul (mem_ofInt _) (mem_pow hu _)) (mem_pow hω _)) ih

lemma sum_range_eq_list (n : ℕ) (f : ℕ → ℝ) : ∑ i ∈ range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

lemma mem_sumIv (n : ℕ) {f : ℕ → ℝ} {F : ℕ → Iv} (h : ∀ i < n, f i ∈ᵢ F i) :
    (∑ i ∈ range n, f i) ∈ᵢ sumIv n F := by
  unfold sumIv
  have : ∀ L : List ℕ, (∀ i ∈ L, f i ∈ᵢ F i) →
      (L.map f).sum ∈ᵢ L.foldr (fun i acc => F i + acc) zeroI := by
    intro L
    induction L with
    | nil => intro _; simpa using mem_zeroI
    | cons a L ih =>
      intro hL
      simp only [List.map_cons, List.sum_cons, List.foldr_cons]
      exact mem_add (hL a (by simp)) (ih fun i hi => hL i (by simp [hi]))
  rw [sum_range_eq_list]
  exact this _ fun i hi => h i (List.mem_range.mp hi)

lemma mem_powFact {x : ℝ} {I : Iv} (hx : x ∈ᵢ I) : ∀ i, (x ^ i / (i.factorial : ℝ)) ∈ᵢ powFact I i
  | 0 => by simpa [powFact] using mem_oneI
  | i + 1 => by
    have h := mem_mul (mem_mul (mem_powFact hx i) hx) (mem_ofFrac 1 ((i : ℤ) + 1) (by omega))
    unfold powFact
    convert h using 1
    rw [Nat.factorial_succ]; push_cast; field_simp; ring

lemma mem_prodT {x : ℝ} {I : Iv} (hx : x ∈ᵢ I) :
    ∀ N, (∏ j ∈ range N, (2 * ((j : ℝ) + 1) * x ^ 2)) ∈ᵢ prodT I N
  | 0 => by simpa [prodT] using mem_oneI
  | N + 1 => by
    rw [Finset.prod_range_succ]
    unfold prodT
    refine mem_mul (mem_prodT hx N) (mem_mul (mem_ofInt' _ ?_) (mem_pow hx 2))
    push_cast; ring

lemma prod_two_mul (x : ℝ) (N : ℕ) :
    ∏ j ∈ range N, (2 * ((j : ℝ) + 1) * x ^ 2) = 2 ^ N * (N.factorial : ℝ) * x ^ (2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

lemma mem_c2powI {c sq : ℝ} {C Sq : Iv} (hc : c ∈ᵢ C) (hs : sq ∈ᵢ Sq) (m : ℕ) :
    (c ^ (m / 2) * (if m % 2 = 1 then sq else 1)) ∈ᵢ c2powI C Sq m := by
  unfold c2powI
  refine mem_mul (mem_pow hc _) ?_
  split_ifs
  · exact hs
  · exact mem_oneI

lemma getD_map_range {α : Type} (f : ℕ → α) (n i : ℕ) (z : α) (hi : i < n) :
    ((List.range n).map f).getD i z = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

/-! ## the Leibniz recurrence on interval lists -/

lemma recIv_length (Φ : List Iv) (E0 : Iv) : ∀ k, (recIv Φ E0 k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp [recIv, recIv_length Φ E0 k]

lemma recIv_getD_succ (Φ : List Iv) (E0 : Iv) (k m : ℕ) (hm : m ≤ k) :
    (recIv Φ E0 (k + 1)).getD m zeroI = (recIv Φ E0 k).getD m zeroI := by
  simp only [recIv]
  rw [List.getD_append _ _ _ _ (by rw [recIv_length]; omega)]

lemma recIv_getD_last (Φ : List Iv) (E0 : Iv) (k : ℕ) :
    (recIv Φ E0 (k + 1)).getD (k + 1) zeroI = recStep Φ (recIv Φ E0 k) k := by
  simp only [recIv]
  rw [List.getD_append_right _ _ _ _ (by rw [recIv_length])]
  simp [recIv_length]

/-- if `Φ i t ∈ Φl[i]` for `i ≤ K` and `exp (Φ 0 t) ∈ E0`, then `gs Φ k t ∈ (recIv Φl E0 K)[k]`. -/
theorem mem_recIv (Φ : ℕ → ℝ → ℝ) (Φl : List Iv) (E0 : Iv) (t : ℝ) (K : ℕ)
    (hΦ : ∀ i ≤ K, Φ i t ∈ᵢ Φl.getD i zeroI) (hE : Real.exp (Φ 0 t) ∈ᵢ E0) :
    ∀ k ≤ K, gs Φ k t ∈ᵢ (recIv Φl E0 K).getD k zeroI := by
  induction K with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    simpa [recIv, gs_zero] using hE
  | succ K ih =>
    intro k hk
    have ih' := ih (fun i hi => hΦ i (by omega))
    rcases Nat.lt_or_ge k (K + 1) with h | h
    · rw [recIv_getD_succ _ _ _ _ (by omega)]; exact ih' k (by omega)
    · obtain rfl : k = K + 1 := by omega
      rw [recIv_getD_last, gs_succ]
      unfold recStep
      apply mem_sumIv
      intro i hi
      exact mem_mul (mem_mul (mem_ofInt' _ (by push_cast; rfl)) (ih' (K - i) (by omega)))
        (hΦ (i + 1) (by omega))

end JensenThreshold.Tail
