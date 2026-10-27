/-
# Farey sequences by the Stern–Brocot recursion

`sb N (a,b) (c,d)` lists, in increasing order, the reduced fractions strictly between `a/b` and `c/d` with
denominator `≤ N`, assuming `bc − ad = 1`. The recursion inserts the mediant `(a+c)/(b+d)` while `b + d ≤ N`.

* consecutive fractions `a/b < c/d` of `[0/1] ++ sb N (0,1) (1,1) ++ [1/1]` satisfy `bc − ad = 1` and `b + d > N`;
* every reduced `h/k` with `0 ≤ h < k ≤ N` occurs exactly once.
-/
import Mathlib

set_option autoImplicit false

namespace Rademacher.Farey

/-- the Stern–Brocot list (fractions as `(numerator, denominator)`). -/
def sb (N : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | a, b, c, d =>
    if h : 0 < b ∧ 0 < d ∧ b + d ≤ N then
      sb N a b (a + c) (b + d) ++ [(a + c, b + d)] ++ sb N (a + c) (b + d) c d
    else []
termination_by _ b _ d => N + 1 - (b + d)
decreasing_by all_goals omega

lemma sb_eq (N a b c d : ℕ) : sb N a b c d =
    if 0 < b ∧ 0 < d ∧ b + d ≤ N then
      sb N a b (a + c) (b + d) ++ [(a + c, b + d)] ++ sb N (a + c) (b + d) c d
    else [] := by
  rw [sb]; simp only [dite_eq_ite]

/-- every fraction strictly between neighbours has denominator `≥ b + d`. -/
lemma den_ge {a b c d h k : ℕ} (hdet : b * c = a * d + 1) (h1 : a * k < h * b) (h2 : h * d < c * k) :
    b + d ≤ k := by
  -- `k = k(bc − ad) = b(ck − dh) + d(bh − ak)`, both brackets `≥ 1`
  have e : (k : ℤ) = b * ((c : ℤ) * k - d * h) + d * ((b : ℤ) * h - a * k) := by
    have : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
    linear_combination (-(k : ℤ)) * this
  have q2 : (h : ℤ) * d < c * k := by exact_mod_cast h2
  have q1 : (a : ℤ) * k < h * b := by exact_mod_cast h1
  have p1 : (1 : ℤ) ≤ (c : ℤ) * k - d * h := by linarith
  have p2 : (1 : ℤ) ≤ (b : ℤ) * h - a * k := by linarith
  have : (b : ℤ) + d ≤ k := by nlinarith [Int.natCast_nonneg b, Int.natCast_nonneg d]
  exact_mod_cast this

/-- members lie strictly between, have the determinant property, and denominator `≤ N`. -/
lemma mem_sb : ∀ (N a b c d : ℕ), b * c = a * d + 1 → ∀ x ∈ sb N a b c d,
    a * x.2 < x.1 * b ∧ x.1 * d < c * x.2 ∧ 0 < x.2 ∧ x.2 ≤ N ∧ Nat.Coprime x.1 x.2 := by
  intro N a b c d
  induction a, b, c, d using sb.induct N with
  | case1 a b c d hc ih1 ih2 =>
    intro hdet x hx
    rw [sb_eq, if_pos hc] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    have hdet1 : b * (a + c) = a * (b + d) + 1 := by nlinarith
    have hdet2 : (b + d) * c = (a + c) * d + 1 := by nlinarith
    rcases hx with (hx | hx) | hx
    · obtain ⟨q1, q2, q3, q4, q5⟩ := ih1 hdet1 x hx
      refine ⟨q1, ?_, q3, q4, q5⟩
      nlinarith
    · subst hx
      refine ⟨by nlinarith, by nlinarith, by omega, hc.2.2, ?_⟩
      -- `b(a+c) − a(b+d) = 1`
      rw [← Nat.isCoprime_iff_coprime]
      refine ⟨b, -(a : ℤ), ?_⟩
      have : ((b : ℤ) * (a + c)) = a * (b + d) + 1 := by exact_mod_cast hdet1
      push_cast; linarith
    · obtain ⟨q1, q2, q3, q4, q5⟩ := ih2 hdet2 x hx
      exact ⟨by nlinarith, q2, q3, q4, q5⟩
  | case2 a b c d hc =>
    intro hdet x hx
    rw [sb_eq, if_neg hc] at hx
    simp at hx

lemma eq_of_reduced {h k m n : ℕ} (hk : Nat.Coprime h k) (hmn : Nat.Coprime m n) (hk0 : 0 < k) (hn0 : 0 < n)
    (he : h * n = m * k) : h = m ∧ k = n := by
  have h1 : k ∣ n := by
    have : k ∣ h * n := ⟨m, by rw [he]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hk) this)
  have h2 : n ∣ k := by
    have : n ∣ m * k := ⟨h, by rw [← he]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hmn) this)
  have hkn : k = n := Nat.dvd_antisymm h1 h2
  subst hkn
  exact ⟨Nat.eq_of_mul_eq_mul_right hk0 he, rfl⟩

/-- **completeness**. -/
lemma complete : ∀ (N a b c d : ℕ), b * c = a * d + 1 → 0 < b → 0 < d → ∀ h k : ℕ, 0 < k → k ≤ N →
    Nat.Coprime h k → a * k < h * b → h * d < c * k → (h, k) ∈ sb N a b c d := by
  intro N a b c d
  induction a, b, c, d using sb.induct N with
  | case1 a b c d hc ih1 ih2 =>
    intro hdet hb hd h k hk hkN hcop h1 h2
    rw [sb_eq, if_pos hc]
    simp only [List.mem_append, List.mem_singleton]
    have hdet1 : b * (a + c) = a * (b + d) + 1 := by nlinarith
    have hdet2 : (b + d) * c = (a + c) * d + 1 := by nlinarith
    rcases lt_trichotomy (h * (b + d)) ((a + c) * k) with hlt | heq | hgt
    · exact Or.inl (Or.inl (ih1 hdet1 hb (by omega) h k hk hkN hcop h1 hlt))
    · refine Or.inl (Or.inr ?_)
      have hm : Nat.Coprime (a + c) (b + d) := by
        rw [← Nat.isCoprime_iff_coprime]
        refine ⟨b, -(a : ℤ), ?_⟩
        have : ((b : ℤ) * (a + c)) = a * (b + d) + 1 := by exact_mod_cast hdet1
        push_cast; linarith
      obtain ⟨e1, e2⟩ := eq_of_reduced hcop hm hk (by omega) heq
      rw [e1, e2]
    · exact Or.inr (ih2 hdet2 (by omega) hd h k hk hkN hcop hgt h2)
  | case2 a b c d hc =>
    intro hdet hb hd h k hk hkN hcop h1 h2
    exfalso
    have := den_ge hdet h1 h2
    exact hc ⟨hb, hd, by omega⟩

/-- **no repetitions**. -/
lemma nodup : ∀ (N a b c d : ℕ), b * c = a * d + 1 → (sb N a b c d).Nodup := by
  intro N a b c d
  induction a, b, c, d using sb.induct N with
  | case1 a b c d hc ih1 ih2 =>
    intro hdet
    rw [sb_eq, if_pos hc]
    have hdet1 : b * (a + c) = a * (b + d) + 1 := by nlinarith
    have hdet2 : (b + d) * c = (a + c) * d + 1 := by nlinarith
    have m1 := mem_sb N a b (a + c) (b + d) hdet1
    have m2 := mem_sb N (a + c) (b + d) c d hdet2
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨ih1 hdet1, List.nodup_singleton _, ?_⟩, ih2 hdet2, ?_⟩
    · intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst hy hxy
      have := (m1 _ hx).2.1
      simp at this
    · intro x hx y hy hxy
      subst hxy
      have hy2 := (m2 _ hy).1
      rcases List.mem_append.mp hx with hx | hx
      · have := (m1 _ hx).2.1
        omega
      · rw [List.mem_singleton] at hx; subst hx; simp at hy2
  | case2 a b c d hc =>
    intro _
    rw [sb_eq, if_neg hc]; exact List.nodup_nil

/-- the neighbour relation. -/
def Nb (N : ℕ) (x y : ℕ × ℕ) : Prop := x.2 * y.1 = x.1 * y.2 + 1 ∧ N < x.2 + y.2

/-- **the chain property**. -/
lemma chain : ∀ (N a b c d : ℕ), b * c = a * d + 1 → 0 < b → 0 < d →
    List.IsChain (Nb N) ((a, b) :: (sb N a b c d ++ [(c, d)])) := by
  intro N a b c d
  induction a, b, c, d using sb.induct N with
  | case1 a b c d hc ih1 ih2 =>
    intro hdet hb hd
    rw [sb_eq, if_pos hc]
    have hdet1 : b * (a + c) = a * (b + d) + 1 := by nlinarith
    have hdet2 : (b + d) * c = (a + c) * d + 1 := by nlinarith
    have c1 := ih1 hdet1 hb (by omega)
    have c2 := ih2 hdet2 (by omega) hd
    rw [show (a, b) :: (sb N a b (a + c) (b + d) ++ [(a + c, b + d)] ++ sb N (a + c) (b + d) c d ++ [(c, d)]) =
      ((a, b) :: (sb N a b (a + c) (b + d) ++ [(a + c, b + d)])) ++ (sb N (a + c) (b + d) c d ++ [(c, d)]) by simp]
    rw [List.isChain_append]
    refine ⟨c1, c2.tail, ?_⟩
    intro x hx y hy
    simp only [List.getLast?_cons, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.getD_some, Option.mem_def, Option.some.injEq] at hx
    subst hx
    rw [List.isChain_cons] at c2
    exact c2.1 y (by simpa using hy)
  | case2 a b c d hc =>
    intro hdet hb hd
    rw [sb_eq, if_neg hc]
    simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hdet, by omega⟩

end Rademacher.Farey
