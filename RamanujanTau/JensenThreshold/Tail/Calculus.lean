/-
# Calculus for the Jensen tail: Taylor bounds along a derivative chain, and the Leibniz chain for `e^φ`

* `taylor_bounds` : if `G 0, G 1, …, G K` is a derivative chain on `[0, ∞)` and `lo ≤ G K ≤ hi` on `[0, X]`, then
  for `x ∈ [0, X]` the Taylor remainder `G 0 x − Σ_{i<K} G i 0 · xⁱ/i!` lies in `[lo, hi] · x^K / K!`.
* `gs φ k` : `gs φ 0 = exp ∘ φ 0`, `gs φ (k+1) = Σ_{i≤k} C(k,i) · gs φ (k−i) · φ (i+1)` (Leibniz).
  `gs_hasDerivAt` : if `φ` is a derivative chain then so is `gs φ`, i.e. `gs φ k = (e^{φ 0})^{(k)}`.
* `gs_scale` : dividing `φ i` by `δ^i` divides `gs φ k` by `δ^k`.
-/
import Mathlib

set_option autoImplicit false

namespace JensenThreshold.Tail

open Finset

/-! ## Taylor polynomials -/

lemma hasDerivAt_taylorPoly (c : ℕ → ℝ) (K : ℕ) (y : ℝ) :
    HasDerivAt (fun y => ∑ i ∈ range (K + 1), c i * y ^ i / (i.factorial : ℝ))
      (∑ i ∈ range K, c (i + 1) * y ^ i / (i.factorial : ℝ)) y := by
  have h : ∀ i ∈ range (K + 1), HasDerivAt (fun y => c i * y ^ i / (i.factorial : ℝ))
      (c i * ((i : ℝ) * y ^ (i - 1)) / (i.factorial : ℝ)) y := by
    intro i _
    exact ((hasDerivAt_pow i y).const_mul (c i)).div_const _
  have hs := HasDerivAt.sum h
  convert hs using 1
  · ext y; simp [Finset.sum_apply]
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.factorial_succ]
    push_cast
    try simp only [Nat.add_sub_cancel]
    field_simp

lemma taylor_lower {X : ℝ} : ∀ (K : ℕ) (G : ℕ → ℝ → ℝ)
    (_hG : ∀ i < K, ∀ t, 0 ≤ t → HasDerivAt (G i) (G (i + 1) t) t) (lo : ℝ)
    (_hb : ∀ t, 0 ≤ t → t ≤ X → lo ≤ G K t) (x : ℝ), 0 ≤ x → x ≤ X →
    lo * x ^ K / (K.factorial : ℝ) ≤ G 0 x - ∑ i ∈ range K, G i 0 * x ^ i / (i.factorial : ℝ) := by
  intro K
  induction K with
  | zero =>
    intro G _ lo hb x hx hxX
    simpa using hb x hx hxX
  | succ K ih =>
    intro G hG lo hb x hx hxX
    set H : ℝ → ℝ := fun y => G 0 y - ∑ i ∈ range (K + 1), G i 0 * y ^ i / (i.factorial : ℝ) -
      lo * y ^ (K + 1) / ((K + 1).factorial : ℝ) with hH
    set H' : ℝ → ℝ := fun y => G 1 y - ∑ i ∈ range K, G (i + 1) 0 * y ^ i / (i.factorial : ℝ) -
      lo * y ^ K / (K.factorial : ℝ) with hH'
    have hder : ∀ y, 0 ≤ y → HasDerivAt H (H' y) y := by
      intro y hy
      have h1 := hG 0 (by omega) y hy
      have h2 := hasDerivAt_taylorPoly (fun i => G i 0) K y
      have h3 : HasDerivAt (fun y => lo * y ^ (K + 1) / ((K + 1).factorial : ℝ))
          (lo * y ^ K / (K.factorial : ℝ)) y := by
        have := ((hasDerivAt_pow (K + 1) y).const_mul lo).div_const ((K + 1).factorial : ℝ)
        convert this using 1
        rw [Nat.factorial_succ]; push_cast; (try simp only [Nat.add_sub_cancel]); field_simp
      exact (h1.sub h2).sub h3
    have hH'nn : ∀ y, 0 ≤ y → y ≤ X → 0 ≤ H' y := by
      intro y hy hyX
      have := ih (fun i => G (i + 1)) (fun i hi t ht => hG (i + 1) (by omega) t ht) lo
        (fun t ht htX => hb t ht htX) y hy hyX
      simp only [hH']
      simp only at this
      linarith
    have hmono : MonotoneOn H (Set.Icc 0 X) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 X)
      · intro y hy; exact (hder y hy.1).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hder y hy.1.le).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hder y hy.1.le).deriv]
        exact hH'nn y hy.1.le hy.2.le
    have h0 : H 0 = 0 := by
      simp only [hH]
      rw [Finset.sum_range_succ']
      simp
    have := hmono ⟨le_rfl, le_trans hx hxX⟩ ⟨hx, hxX⟩ hx
    rw [h0] at this
    simp only [hH] at this
    linarith

theorem taylor_bounds (G : ℕ → ℝ → ℝ) (K : ℕ)
    (hG : ∀ i < K, ∀ t, 0 ≤ t → HasDerivAt (G i) (G (i + 1) t) t) {X lo hi : ℝ}
    (hb : ∀ t, 0 ≤ t → t ≤ X → lo ≤ G K t ∧ G K t ≤ hi) {x : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) :
    lo * x ^ K / (K.factorial : ℝ) ≤ G 0 x - ∑ i ∈ range K, G i 0 * x ^ i / (i.factorial : ℝ) ∧
      G 0 x - ∑ i ∈ range K, G i 0 * x ^ i / (i.factorial : ℝ) ≤ hi * x ^ K / (K.factorial : ℝ) := by
  refine ⟨taylor_lower K G hG lo (fun t h1 h2 => (hb t h1 h2).1) x hx hxX, ?_⟩
  have := taylor_lower K (fun i t => -G i t) (fun i hi t ht => (hG i hi t ht).neg) (-hi)
    (fun t h1 h2 => by simpa using (hb t h1 h2).2) x hx hxX
  simp only [neg_mul, neg_div, Finset.sum_neg_distrib, sub_neg_eq_add] at this
  linarith

/-! ## The Leibniz chain for `e^φ` -/

/-- `gs φ k = (e^{φ 0})^{(k)}` when `φ` is a derivative chain. -/
noncomputable def gs (φ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => Real.exp (φ 0 t)
  | k + 1 => fun t => ∑ i ∈ (range (k + 1)).attach,
      ((k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1) t)
termination_by k => k
decreasing_by omega

lemma gs_zero (φ : ℕ → ℝ → ℝ) (t : ℝ) : gs φ 0 t = Real.exp (φ 0 t) := by rw [gs]

lemma gs_succ (φ : ℕ → ℝ → ℝ) (k : ℕ) (t : ℝ) :
    gs φ (k + 1) t = ∑ i ∈ range (k + 1), (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1) t := by
  rw [gs]
  exact Finset.sum_attach (range (k + 1)) (fun i => (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1) t)

theorem gs_hasDerivAt (φ : ℕ → ℝ → ℝ) (L : ℕ)
    (hφ : ∀ i < L, ∀ t, 0 ≤ t → HasDerivAt (φ i) (φ (i + 1) t) t) :
    ∀ k, k + 1 ≤ L → ∀ t, 0 ≤ t → HasDerivAt (gs φ k) (gs φ (k + 1) t) t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk t ht
    rcases k with _ | k
    · have h := (hφ 0 (by omega) t ht).exp
      have e : (fun t => gs φ 0 t) = fun t => Real.exp (φ 0 t) := funext fun t => gs_zero φ t
      rw [show gs φ 0 = fun t => Real.exp (φ 0 t) from e, gs_succ]
      simpa [gs_zero] using h
    · have hfun : gs φ (k + 1) = fun t => ∑ i ∈ range (k + 1),
          (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1) t := funext fun t => gs_succ φ k t
      rw [hfun]
      have hterm : ∀ i ∈ range (k + 1), HasDerivAt
          (fun t => (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1) t)
          ((k.choose i : ℝ) * gs φ (k - i + 1) t * φ (i + 1) t +
            (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1 + 1) t) t := by
        intro i hi
        simp only [mem_range] at hi
        have hg := ih (k - i) (by omega) (by omega) t ht
        have hp := hφ (i + 1) (by omega) t ht
        have := (hg.const_mul (k.choose i : ℝ)).mul hp
        convert this using 1 <;> ring
      have hs := HasDerivAt.sum hterm
      convert hs using 1
      · ext t; simp [Finset.sum_apply]
      · rw [gs_succ, Finset.sum_add_distrib]
        -- Pascal rearrangement
        rw [Finset.sum_range_succ' _ (k + 1)]
        have e1 : ∀ i ∈ range (k + 1), ((k + 1).choose (i + 1) : ℝ) * gs φ (k + 1 - (i + 1)) t *
            φ (i + 1 + 1) t = (k.choose i : ℝ) * gs φ (k - i) t * φ (i + 1 + 1) t +
            (k.choose (i + 1) : ℝ) * gs φ (k - i) t * φ (i + 1 + 1) t := by
          intro i _
          rw [Nat.choose_succ_succ', show k + 1 - (i + 1) = k - i by omega]; push_cast; ring
        rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
        rw [Finset.sum_range_succ' (fun i => (k.choose i : ℝ) * gs φ (k - i + 1) t * φ (i + 1) t)]
        have e2 : ∀ i ∈ range k, (k.choose (i + 1) : ℝ) * gs φ (k - (i + 1) + 1) t * φ (i + 1 + 1) t =
            (k.choose (i + 1) : ℝ) * gs φ (k - i) t * φ (i + 1 + 1) t := by
          intro i hi; simp only [mem_range] at hi
          rw [show k - (i + 1) + 1 = k - i by omega]
        rw [Finset.sum_congr rfl e2]
        rw [Finset.sum_range_succ (fun i => (k.choose (i + 1) : ℝ) * gs φ (k - i) t * φ (i + 1 + 1) t)]
        simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
          Nat.sub_zero, Nat.cast_one]
        ring

theorem gs_scale (φ : ℕ → ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    ∀ k t, gs (fun i t => φ i t / δ ^ i) k t = gs φ k t / δ ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t
    rcases k with _ | k
    · simp [gs_zero]
    · rw [gs_succ, gs_succ, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [mem_range] at hi
      rw [ih (k - i) (by omega) t]
      have : δ ^ (k + 1) = δ ^ (k - i) * δ ^ (i + 1) := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp

end JensenThreshold.Tail
