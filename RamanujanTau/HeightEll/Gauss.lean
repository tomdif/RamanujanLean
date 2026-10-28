/-
# Heights of rational functions and a Gauss-lemma inequality

`ht f = max (deg num f) (deg denom f)` for `f ∈ k(X)`. If `f, g` are the two roots of
`E T² - S T + Q` (`E ≠ 0`), i.e. `E f g = Q` and `E (f + g) = S`, then `ht f + ht g ≤ max deg (E, S, Q)`.
Also: the "quasi-parallelogram" telescoping `h(m+1) + h(m-1) ≤ 2 h(m) + 2 ⇒ h(n) ≤ n²`.
-/
import Mathlib

set_option autoImplicit false

namespace HeightEll

open Polynomial

variable {k : Type*} [Field k]

/-- the height of a rational function. -/
noncomputable def ht (f : RatFunc k) : ℕ := max f.num.natDegree f.denom.natDegree

lemma ht_X : ht (RatFunc.X : RatFunc k) = 1 := by
  simp [ht, RatFunc.num_X, RatFunc.denom_X]

/-- any representation bounds the height. -/
lemma ht_le_of_eq_div {f : RatFunc k} {A B : k[X]} (hB : B ≠ 0)
    (h : f = algebraMap k[X] (RatFunc k) A / algebraMap k[X] (RatFunc k) B) {N : ℕ}
    (hA : A.natDegree ≤ N) (hBN : B.natDegree ≤ N) : ht f ≤ N := by
  have hd : f.denom.natDegree ≤ N :=
    (natDegree_le_of_dvd ((RatFunc.denom_dvd hB).2 ⟨A, h⟩) hB).trans hBN
  by_cases hA0 : A = 0
  · subst hA0
    have : f = 0 := by rw [h]; simp
    subst this; simp [ht, RatFunc.num_zero, RatFunc.denom_zero]
  · have hn : f.num.natDegree ≤ N :=
      (natDegree_le_of_dvd ((RatFunc.num_dvd hA0).2 ⟨B, hB, h⟩) hA0).trans hA
    exact max_le hn hd

/-- the polynomial core of the Gauss argument: `VB ∣ E`. -/
lemma dvd_core {U V A B E : k[X]} (hUV : IsCoprime U V) (hAB : IsCoprime A B)
    (h1 : V * B ∣ E * (U * A)) (h2 : V * B ∣ E * (U * B + A * V)) : V * B ∣ E := by
  set d := V * B
  have hVB : d ∣ E * (V * B) := dvd_mul_left _ _
  have hUB : d ∣ E * (U * B) ^ 2 := by
    have : E * (U * B) ^ 2 = (U * B) * (E * (U * B + A * V)) - (V * B) * (E * (U * A)) := by ring
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  have hAV : d ∣ E * (A * V) ^ 2 := by
    have : E * (A * V) ^ 2 = (A * V) * (E * (U * B + A * V)) - (V * B) * (E * (U * A)) := by ring
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  have hUA : d ∣ E * (U * A) ^ 2 := by
    rw [pow_two, ← mul_assoc]; exact dvd_mul_of_dvd_left h1 _
  have hVB2 : d ∣ E * (V * B) ^ 2 := by
    rw [pow_two, ← mul_assoc]; exact dvd_mul_of_dvd_left hVB _
  obtain ⟨a, b, hab⟩ := (IsCoprime.pow (m := 2) (n := 2) hUV)
  obtain ⟨c, e, hce⟩ := (IsCoprime.pow (m := 2) (n := 2) hAB)
  have hB2 : d ∣ E * B ^ 2 := by
    have : E * B ^ 2 = a * (E * (U * B) ^ 2) + b * (E * (V * B) ^ 2) := by
      linear_combination (-(E * B ^ 2)) * hab
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hUB _) (dvd_mul_of_dvd_right hVB2 _)
  have hA2 : d ∣ E * A ^ 2 := by
    have : E * A ^ 2 = a * (E * (U * A) ^ 2) + b * (E * (A * V) ^ 2) := by
      linear_combination (-(E * A ^ 2)) * hab
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hUA _) (dvd_mul_of_dvd_right hAV _)
  have : E = c * (E * A ^ 2) + e * (E * B ^ 2) := by linear_combination (-E) * hce
  rw [this]; exact dvd_add (dvd_mul_of_dvd_right hA2 _) (dvd_mul_of_dvd_right hB2 _)

lemma natDegree_le_mul_left {P l : k[X]} (hl : l ≠ 0) : P.natDegree ≤ (l * P).natDegree := by
  by_cases hP : P = 0
  · simp [hP]
  · rw [natDegree_mul hl hP]; omega

/-- **Gauss-lemma inequality** for polynomials. -/
theorem core_le {U V A B E S Q : k[X]} (hUV : IsCoprime U V) (hAB : IsCoprime A B) (hV : V ≠ 0)
    (hB : B ≠ 0) (hE : E ≠ 0) (h1 : E * (U * A) = Q * (V * B)) (h2 : E * (U * B + A * V) = S * (V * B))
    {N : ℕ} (hEN : E.natDegree ≤ N) (hSN : S.natDegree ≤ N) (hQN : Q.natDegree ≤ N) :
    max U.natDegree V.natDegree + max A.natDegree B.natDegree ≤ N := by
  have hd : V * B ≠ 0 := mul_ne_zero hV hB
  obtain ⟨l, hl⟩ := dvd_core hUV hAB ⟨Q, by rw [h1, mul_comm]⟩ ⟨S, by rw [h2, mul_comm]⟩
  have hl0 : l ≠ 0 := by rintro rfl; rw [mul_zero] at hl; exact hE hl
  have hQ : Q = l * (U * A) := by
    apply mul_right_cancel₀ hd; rw [← h1, hl]; ring
  have hS : S = l * (U * B + A * V) := by
    apply mul_right_cancel₀ hd; rw [← h2, hl]; ring
  have i1 : V.natDegree + B.natDegree ≤ N := by
    rw [← natDegree_mul hV hB]; exact (natDegree_le_mul_left hl0).trans (by rw [mul_comm, ← hl]; exact hEN)
  have i2 : (U * A).natDegree ≤ N := (natDegree_le_mul_left hl0).trans (hQ ▸ hQN)
  have i3 : (U * B + A * V).natDegree ≤ N := (natDegree_le_mul_left hl0).trans (hS ▸ hSN)
  by_cases hU : U = 0
  · have hVu : IsUnit V := by rw [hU] at hUV; exact isCoprime_zero_left.1 hUV
    have hV0 : V.natDegree = 0 := natDegree_eq_zero_of_isUnit hVu
    by_cases hA0 : A = 0
    · subst hA0; simp [hU] at *; omega
    · have hAV : (A * V).natDegree = A.natDegree + V.natDegree := natDegree_mul hA0 hV
      rw [hU] at i3; simp at i3; simp [hU]; omega
  by_cases hA : A = 0
  · have hBu : IsUnit B := by rw [hA] at hAB; exact isCoprime_zero_left.1 hAB
    have hB0 : B.natDegree = 0 := natDegree_eq_zero_of_isUnit hBu
    have hUB : (U * B).natDegree = U.natDegree + B.natDegree := natDegree_mul hU hB
    rw [hA] at i3; simp at i3; simp [hA]; omega
  have hUA : (U * A).natDegree = U.natDegree + A.natDegree := natDegree_mul hU hA
  have hUB : (U * B).natDegree = U.natDegree + B.natDegree := natDegree_mul hU hB
  have hAV : (A * V).natDegree = A.natDegree + V.natDegree := natDegree_mul hA hV
  have j1 : (U * B).natDegree ≤ max (U * B + A * V).natDegree (A * V).natDegree := by
    have := natDegree_sub_le (U * B + A * V) (A * V); rwa [add_sub_cancel_right] at this
  have j2 : (A * V).natDegree ≤ max (U * B + A * V).natDegree (U * B).natDegree := by
    have := natDegree_sub_le (U * B + A * V) (U * B); rwa [add_sub_cancel_left] at this
  rw [hUB, hAV] at j1 j2
  rw [hUA] at i2
  omega

/-- **Gauss-lemma inequality** for rational functions. -/
theorem ht_add_ht_le {f g : RatFunc k} {E S Q : k[X]} (hE : E ≠ 0)
    (h1 : algebraMap k[X] (RatFunc k) E * (f * g) = algebraMap k[X] (RatFunc k) Q)
    (h2 : algebraMap k[X] (RatFunc k) E * (f + g) = algebraMap k[X] (RatFunc k) S)
    {N : ℕ} (hEN : E.natDegree ≤ N) (hSN : S.natDegree ≤ N) (hQN : Q.natDegree ≤ N) :
    ht f + ht g ≤ N := by
  show max f.num.natDegree f.denom.natDegree + max g.num.natDegree g.denom.natDegree ≤ N
  have hV := RatFunc.denom_ne_zero f
  have hB := RatFunc.denom_ne_zero g
  have cf := RatFunc.isCoprime_num_denom f
  have cg := RatFunc.isCoprime_num_denom g
  have ef : f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
    (RatFunc.num_div_denom f).symm
  have eg : g = algebraMap k[X] (RatFunc k) g.num / algebraMap k[X] (RatFunc k) g.denom :=
    (RatFunc.num_div_denom g).symm
  set U := f.num
  set V := f.denom
  set A := g.num
  set B := g.denom
  clear_value U V A B
  subst ef eg
  have hVi : algebraMap k[X] (RatFunc k) V ≠ 0 := RatFunc.algebraMap_ne_zero hV
  have hBi : algebraMap k[X] (RatFunc k) B ≠ 0 := RatFunc.algebraMap_ne_zero hB
  apply core_le cf cg hV hB hE _ _ hEN hSN hQN
  · apply RatFunc.algebraMap_injective
    simp only [map_mul]
    rw [← h1]; field_simp
  · apply RatFunc.algebraMap_injective
    simp only [map_mul, map_add]
    rw [← h2]; field_simp

/-- **telescoping**: second differences `≤ 2` give `h n ≤ n²`. -/
theorem telescope (h : ℕ → ℕ) (N : ℕ) (h1 : h 1 = 1) (h2 : h 2 ≤ 4)
    (hrec : ∀ m, 2 ≤ m → m + 1 ≤ N → h (m + 1) + h (m - 1) ≤ 2 * h m + 2) :
    ∀ n, 1 ≤ n → n ≤ N → h n ≤ n ^ 2 := by
  have hd : ∀ m, 1 ≤ m → m + 1 ≤ N → h (m + 1) ≤ h m + 2 * m + 1 := by
    intro m hm hmN
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simp [h1] at *; omega
      · have := hrec (m + 1) (by omega) hmN
        have := ih hm' (by omega)
        simp only [Nat.add_sub_cancel] at *
        omega
  intro n hn hnN
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [h1]
    · have := ih hn' (by omega)
      have := hd n hn' hnN
      nlinarith

end HeightEll
