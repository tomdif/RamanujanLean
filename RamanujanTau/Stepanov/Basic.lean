/-
# Stepanov's method, part 1: the nonvanishing lemma

For `f ∈ 𝔽_p[X]` that is not a constant times a square, and polynomials `r_j, s_j` of degree `< A`
with `2(A-1) + deg f < p` and `J + deg f ≤ p`,
`∑_{j<J} (r_j + s_j f^{(p-1)/2}) X^{pj} = 0` forces all `r_j = s_j = 0`.

Proof: square `U = -f^c V` to get `f U² = f^p V²`, read it as an identity in `𝔽_p[X][Y]`
(`Y = X^p`, "base-`X^p` digits" are unique when the digits have degree `< p`), then specialise
`Y` at every `y` with `f(y) ≠ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.Stepanov

open Polynomial Finset

section Digits

variable {R : Type*} [CommRing R]

/-- Coefficient extraction for `P(X^q)` when all digits `P.coeff i` have degree `< q`. -/
theorem coeff_eval_X_pow {q : ℕ} (P : R[X][X]) (hP : ∀ i, (P.coeff i).natDegree < q)
    (i t : ℕ) (ht : t < q) : (P.eval (X ^ q)).coeff (q * i + t) = (P.coeff i).coeff t := by
  rw [eval_eq_sum_range, finsetSum_coeff]
  have hterm : ∀ n, ((P.coeff n) * (X ^ q) ^ n).coeff (q * i + t) =
      if n = i then (P.coeff i).coeff t else 0 := by
    intro n
    rw [← pow_mul, coeff_mul_X_pow']
    split_ifs with h1 h2 h2
    · subst h2; congr 1; omega
    · rcases lt_or_gt_of_ne h2 with h3 | h3
      · apply coeff_eq_zero_of_natDegree_lt
        have : q * n + q ≤ q * i := by nlinarith
        have := hP n; omega
      · exfalso; have : q * i + q ≤ q * n := by nlinarith
        omega
    · exfalso; subst h2; omega
    · rfl
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (p := P) (by simp at h; omega)]; simp

/-- Uniqueness of base-`X^q` digits. -/
theorem eq_zero_of_eval_X_pow {q : ℕ} (P : R[X][X]) (hP : ∀ i, (P.coeff i).natDegree < q)
    (h : P.eval (X ^ q) = 0) : P = 0 := by
  ext i t
  simp only [coeff_zero]
  by_cases ht : t < q
  · rw [← coeff_eval_X_pow P hP i t ht, h, coeff_zero]
  · exact coeff_eq_zero_of_natDegree_lt (by have := hP i; omega)

/-- All digits of `P` have degree `≤ d`. -/
def DigitDegLE (P : R[X][X]) (d : ℕ) : Prop := ∀ i, (P.coeff i).natDegree ≤ d

theorem DigitDegLE.mul {P Q : R[X][X]} {a b : ℕ} (hP : DigitDegLE P a) (hQ : DigitDegLE Q b) :
    DigitDegLE (P * Q) (a + b) := by
  intro i
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro x _
  exact (natDegree_mul_le).trans (add_le_add (hP _) (hQ _))

theorem DigitDegLE.sub {P Q : R[X][X]} {a : ℕ} (hP : DigitDegLE P a) (hQ : DigitDegLE Q a) :
    DigitDegLE (P - Q) a := by
  intro i
  rw [coeff_sub]
  exact (natDegree_sub_le _ _).trans (max_le (hP i) (hQ i))

theorem DigitDegLE.mono {P : R[X][X]} {a b : ℕ} (hP : DigitDegLE P a) (h : a ≤ b) :
    DigitDegLE P b := fun i => (hP i).trans h

theorem digitDegLE_C (f : R[X]) : DigitDegLE (C f) f.natDegree := by
  intro i; rw [coeff_C]; split_ifs <;> simp

theorem digitDegLE_map_C (f : R[X]) : DigitDegLE (f.map C) 0 := by
  intro i; rw [coeff_map]; simp

theorem digitDegLE_sum {ι : Type*} (s : Finset ι) (g : ι → R[X]) (k : ι → ℕ) {a : ℕ}
    (hg : ∀ j, (g j).natDegree ≤ a) : DigitDegLE (∑ j ∈ s, C (g j) * X ^ (k j)) a := by
  intro i
  rw [finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [coeff_C_mul_X_pow]; split_ifs
  · exact hg j
  · simp

end Digits

variable {p : ℕ} [hp : Fact p.Prime]

/-- `f` is not a nonzero constant times a square (in the form used by the proof). -/
def NotConstSq (f : (ZMod p)[X]) : Prop :=
  ∀ (a : ZMod p) (u v : (ZMod p)[X]), a ≠ 0 → f * u ^ 2 = C a * v ^ 2 → u = 0

/-- A squarefree nonconstant polynomial is not a constant times a square (infinite descent). -/
theorem notConstSq_of_squarefree {f : (ZMod p)[X]} (hf : Squarefree f) (hdeg : 0 < f.natDegree) :
    NotConstSq f := by
  intro a u
  induction hn : u.natDegree using Nat.strong_induction_on generalizing u with
  | _ n ih =>
  intro v ha h
  by_contra hu
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  have hCa : IsUnit (C a) := isUnit_C.mpr (Ne.isUnit ha)
  -- f ∣ v
  have hfv : f ∣ v := by
    rw [← hf.dvd_pow_iff_dvd two_ne_zero]
    have : f ∣ C a * v ^ 2 := ⟨u ^ 2, h.symm⟩
    exact (hCa.dvd_mul_left).mp this
  obtain ⟨w, rfl⟩ := hfv
  have h2 : u ^ 2 = C a * f * w ^ 2 := by
    apply mul_left_cancel₀ hf0; rw [h]; ring
  have hfu : f ∣ u := by
    rw [← hf.dvd_pow_iff_dvd two_ne_zero, h2]
    exact ⟨C a * w ^ 2, by ring⟩
  obtain ⟨t, rfl⟩ := hfu
  have ht0 : t ≠ 0 := by rintro rfl; simp at hu
  have h3 : f * t ^ 2 = C a * w ^ 2 := by
    apply mul_left_cancel₀ hf0; linear_combination h2
  have hlt : t.natDegree < (f * t).natDegree := by
    rw [natDegree_mul hf0 ht0]; omega
  exact ht0 (ih _ (hn ▸ hlt) t rfl w ha h3)

theorem card_nonroots_ge (f : (ZMod p)[X]) (hf0 : f ≠ 0) :
    p - f.natDegree ≤ #(univ.filter (fun y : ZMod p => f.eval y ≠ 0)) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod p)))
    (fun y => f.eval y = 0)
  have h3 : #(univ.filter (fun y : ZMod p => f.eval y ≠ 0)) =
      #(univ.filter (fun y : ZMod p => ¬ f.eval y = 0)) := rfl
  rw [Finset.card_univ, ZMod.card] at h1
  have h2 : #(univ.filter (fun y : ZMod p => f.eval y = 0)) ≤ f.natDegree := by
    calc #(univ.filter (fun y : ZMod p => f.eval y = 0)) ≤ #f.roots.toFinset := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_filter] at hy
          simp [Multiset.mem_toFinset, mem_roots hf0, hy.2]
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
  omega

/-- **Stepanov's nonvanishing lemma.** -/
theorem stepanov_nonvanish (hp2 : p ≠ 2) (f : (ZMod p)[X]) (hf : NotConstSq f) (hf0 : f ≠ 0)
    {A J : ℕ} (r s : Fin J → (ZMod p)[X]) (hr : ∀ j, (r j).natDegree < A)
    (hs : ∀ j, (s j).natDegree < A) (hA : 2 * (A - 1) + f.natDegree < p)
    (hJ : J + f.natDegree ≤ p)
    (h0 : ∑ j : Fin J, (r j + s j * f ^ ((p - 1) / 2)) * X ^ (p * (j : ℕ)) = 0) :
    ∀ j, r j = 0 ∧ s j = 0 := by
  have hpodd : 2 * ((p - 1) / 2) + 1 = p := by
    have := hp.out.two_le
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  set c := (p - 1) / 2
  set U : (ZMod p)[X] := ∑ j : Fin J, r j * X ^ (p * (j : ℕ))
  set V : (ZMod p)[X] := ∑ j : Fin J, s j * X ^ (p * (j : ℕ))
  have hUV : U = -(f ^ c * V) := by
    rw [eq_neg_iff_add_eq_zero, ← h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsq : f * U ^ 2 = f ^ p * V ^ 2 := by
    calc f * U ^ 2 = f ^ (2 * c + 1) * V ^ 2 := by rw [hUV]; ring
      _ = f ^ p * V ^ 2 := by rw [hpodd]
  -- bivariate lifts
  set rr : (ZMod p)[X][X] := ∑ j : Fin J, C (r j) * X ^ (j : ℕ)
  set ss : (ZMod p)[X][X] := ∑ j : Fin J, C (s j) * X ^ (j : ℕ)
  have hevr : rr.eval (X ^ p) = U := by
    simp only [rr, U, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, ← pow_mul]
  have hevs : ss.eval (X ^ p) = V := by
    simp only [ss, V, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, ← pow_mul]
  have hevf : (f.map C).eval (X ^ p) = f ^ p := by
    rw [eval_map, ← ZMod.expand_card f, coe_expand]
  set P : (ZMod p)[X][X] := C f * rr ^ 2 - f.map C * ss ^ 2
  have hPev : P.eval (X ^ p) = 0 := by
    simp only [P, eval_sub, eval_mul, eval_C, eval_pow, hevr, hevs, hevf, hsq, sub_self]
  have hrd : DigitDegLE rr (A - 1) :=
    digitDegLE_sum _ _ _ (fun j => by have := hr j; omega)
  have hsd : DigitDegLE ss (A - 1) :=
    digitDegLE_sum _ _ _ (fun j => by have := hs j; omega)
  have hPd : DigitDegLE P (f.natDegree + 2 * (A - 1)) := by
    apply DigitDegLE.sub
    · have := (digitDegLE_C f).mul ((hrd.mul hrd))
      simp only [pow_two]; exact this.mono (by omega)
    · have := (digitDegLE_map_C f).mul ((hsd.mul hsd))
      simp only [pow_two]; exact this.mono (by omega)
  have hP0 : P = 0 := eq_zero_of_eval_X_pow P (fun i => by have := hPd i; omega) hPev
  -- specialise Y = y
  have hspec : ∀ y : ZMod p, f.eval y ≠ 0 → rr.eval (C y) = 0 ∧ ss.eval (C y) = 0 := by
    intro y hy
    have h1 : (P.eval (C y)) = 0 := by rw [hP0, eval_zero]
    simp only [P, eval_sub, eval_mul, eval_C, eval_pow, eval_map, eval₂_at_apply] at h1
    have h2 : f * (rr.eval (C y)) ^ 2 = C (f.eval y) * (ss.eval (C y)) ^ 2 := sub_eq_zero.mp h1
    have hr0 := hf _ _ _ hy h2
    refine ⟨hr0, ?_⟩
    rw [hr0] at h2
    have : C (f.eval y) * (ss.eval (C y)) ^ 2 = 0 := by rw [← h2]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (C_eq_zero.mp h) hy
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · subst hJ0; intro j; exact j.elim0
  set Z : Finset (ZMod p)[X] := (univ.filter (fun y : ZMod p => f.eval y ≠ 0)).image C
  have hZ : p - f.natDegree ≤ #Z := by
    rw [Finset.card_image_of_injective _ C_injective]; exact card_nonroots_ge f hf0
  have hdeg : ∀ (g : Fin J → (ZMod p)[X]),
      (∑ j : Fin J, C (g j) * X ^ (j : ℕ) : (ZMod p)[X][X]).natDegree < #Z := by
    intro g
    have : (∑ j : Fin J, C (g j) * X ^ (j : ℕ) : (ZMod p)[X][X]).natDegree ≤ J - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro j _
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  have hcoeff : ∀ (g : Fin J → (ZMod p)[X]) (j : Fin J),
      (∑ i : Fin J, C (g i) * X ^ (i : ℕ) : (ZMod p)[X][X]).coeff j = g j := by
    intro g j
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Fin.val_inj]
    rw [Finset.sum_ite_eq]; simp
  have hrr : rr = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' rr Z _ (hdeg r)
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact (hspec y (Finset.mem_filter.mp hy).2).1
  have hss : ss = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' ss Z _ (hdeg s)
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact (hspec y (Finset.mem_filter.mp hy).2).2
  intro j
  refine ⟨?_, ?_⟩
  · rw [← hcoeff r j]; change rr.coeff j = 0; rw [hrr, coeff_zero]
  · rw [← hcoeff s j]; change ss.coeff j = 0; rw [hss, coeff_zero]

end RamanujanTau.Stepanov
