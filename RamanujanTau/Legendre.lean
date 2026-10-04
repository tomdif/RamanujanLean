/-
# Legendre's four-triangular-numbers theorem

  `t₄(n) = #{(x₁,x₂,x₃,x₄) ∈ ℕ⁴ : Σ xᵢ(xᵢ+1)/2 = n} = σ(2n+1)`,

so every natural number is a sum of four triangular numbers.

Proof from Jacobi's four-square theorem. A solution of `Σ vᵢ² = 8n+4` has all `vᵢ` even or all odd, since
`v² ≡ v (mod 2)` and `v² ≡ 0, 1 (mod 4)`. Halving the even solutions gives the representations of `2n+1`.
The odd solutions are `vᵢ = ±(2xᵢ+1)` with `Σ xᵢ(xᵢ+1) = 2n`, sixteen for each `x`. So
`16 t₄(n) = r₄(8n+4) − r₄(2n+1) = 8·3σ(2n+1) − 8·σ(2n+1)`.
-/
import RamanujanTau.FourSquares

set_option autoImplicit false

namespace FourSquares
open Finset

/-- the solution set of `Σ vᵢ² = N`, as counted by `r4`. -/
noncomputable def S4 (N : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  (box4 N).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ)

lemma r4_eq_card (N : ℕ) : r4 N = #(S4 N) := rfl

lemma mem_S4 {N : ℕ} {v : ℤ × ℤ × ℤ × ℤ} : v ∈ S4 N ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [S4, box4, mem_filter, mem_product, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have := Int.le_self_sq a; have := Int.le_self_sq (-a); have := Int.le_self_sq b; have := Int.le_self_sq (-b)
    have := Int.le_self_sq c; have := Int.le_self_sq (-c); have := Int.le_self_sq d; have := Int.le_self_sq (-d)
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_nonneg d]

lemma sq_mod_four (v : ℤ) : (v % 2 = 0 ∧ v ^ 2 % 4 = 0) ∨ (v % 2 = 1 ∧ v ^ 2 % 4 = 1) := by
  rcases Int.emod_two_eq_zero_or_one v with h | h
  · left; refine ⟨h, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, v = 2 * k := ⟨v / 2, by omega⟩
    rw [hk, show (2 * k) ^ 2 = 4 * k ^ 2 by ring]; simp
  · right; refine ⟨h, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, v = 2 * k + 1 := ⟨v / 2, by omega⟩
    rw [hk, show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]; omega

/-- the parity dichotomy for `Σ vᵢ² ≡ 0 (mod 4)`. -/
lemma all_even_or_all_odd {v : ℤ × ℤ × ℤ × ℤ} (h : (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2) % 4 = 0) :
    (v.1 % 2 = 0 ∧ v.2.1 % 2 = 0 ∧ v.2.2.1 % 2 = 0 ∧ v.2.2.2 % 2 = 0) ∨
    (v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2.1 % 2 = 1 ∧ v.2.2.2 % 2 = 1) := by
  have h1 := sq_mod_four v.1; have h2 := sq_mod_four v.2.1
  have h3 := sq_mod_four v.2.2.1; have h4 := sq_mod_four v.2.2.2
  omega

/-! ## the even solutions -/

lemma card_even (n : ℕ) :
    #((S4 (8 * n + 4)).filter fun v => v.1 % 2 = 0 ∧ v.2.1 % 2 = 0 ∧ v.2.2.1 % 2 = 0 ∧ v.2.2.2 % 2 = 0)
      = #(S4 (2 * n + 1)) := by
  refine card_bij' (fun v _ => (v.1 / 2, v.2.1 / 2, v.2.2.1 / 2, v.2.2.2 / 2))
    (fun w _ => (2 * w.1, 2 * w.2.1, 2 * w.2.2.1, 2 * w.2.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d⟩ hv
    rw [mem_filter, mem_S4] at hv
    obtain ⟨h, ha, hb, hc, hd⟩ := hv
    dsimp only at h ha hb hc hd
    rw [mem_S4]
    obtain ⟨a', rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ k, c = 2 * k := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    simp only [Int.mul_ediv_cancel_left _ (two_ne_zero)]
    push_cast at h ⊢
    nlinarith
  · rintro ⟨a, b, c, d⟩ hw
    rw [mem_S4] at hw
    rw [mem_filter, mem_S4]
    refine ⟨?_, by simp, by simp, by simp, by simp⟩
    push_cast at hw ⊢
    nlinarith
  · rintro ⟨a, b, c, d⟩ hv
    rw [mem_filter] at hv
    obtain ⟨-, ha, hb, hc, hd⟩ := hv
    dsimp only at ha hb hc hd
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b, c, d⟩ _
    simp only [Int.mul_ediv_cancel_left _ (two_ne_zero)]


/-! ## the odd solutions -/

/-- `{±(2y+1)}`. -/
def pm (y : ℕ) : Finset ℤ := {2 * (y : ℤ) + 1, -(2 * (y : ℤ) + 1)}

lemma card_pm (y : ℕ) : #(pm y) = 2 := by
  rw [pm, card_pair]; omega

lemma mem_pm {v : ℤ} {y : ℕ} : v ∈ pm y ↔ v % 2 = 1 ∧ (v.natAbs - 1) / 2 = y := by
  rw [pm, mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · refine ⟨by omega, ?_⟩
      rw [show (2 * (y : ℤ) + 1) = ((2 * y + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega
    · refine ⟨by omega, ?_⟩
      rw [Int.natAbs_neg, show (2 * (y : ℤ) + 1) = ((2 * y + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
      omega
  · rintro ⟨h1, h2⟩
    rcases Int.natAbs_eq v with h | h
    · left; omega
    · right; omega

lemma sq_of_pm {v : ℤ} {y : ℕ} (h : v ∈ pm y) : v ^ 2 = 4 * ((y : ℤ) * (y + 1)) + 1 := by
  rw [pm, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl <;> ring

/-- the representations `Σ xᵢ(xᵢ+1) = 2n` with `xᵢ ∈ ℕ`. -/
noncomputable def T4 (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)).filter fun x =>
    x.1 * (x.1 + 1) + x.2.1 * (x.2.1 + 1) + x.2.2.1 * (x.2.2.1 + 1) + x.2.2.2 * (x.2.2.2 + 1) = 2 * n

/-- `t₄(n)`: the representations of `n` as an ordered sum of four triangular numbers `x(x+1)/2`. -/
noncomputable def t4 (n : ℕ) : ℕ := #(T4 n)

lemma mem_T4 {n : ℕ} {x : ℕ × ℕ × ℕ × ℕ} :
    x ∈ T4 n ↔ x.1 * (x.1 + 1) + x.2.1 * (x.2.1 + 1) + x.2.2.1 * (x.2.2.1 + 1) + x.2.2.2 * (x.2.2.2 + 1) = 2 * n := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [T4, mem_filter, mem_product, mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_, ?_, ?_⟩, h⟩⟩ <;> nlinarith

lemma card_odd (n : ℕ) :
    #((S4 (8 * n + 4)).filter fun v => v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2.1 % 2 = 1 ∧ v.2.2.2 % 2 = 1)
      = 16 * t4 n := by
  set O := (S4 (8 * n + 4)).filter fun v => v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2.1 % 2 = 1 ∧ v.2.2.2 % 2 = 1
  let f : ℤ × ℤ × ℤ × ℤ → ℕ × ℕ × ℕ × ℕ := fun v =>
    ((v.1.natAbs - 1) / 2, (v.2.1.natAbs - 1) / 2, (v.2.2.1.natAbs - 1) / 2, (v.2.2.2.natAbs - 1) / 2)
  have hmaps : ∀ v ∈ O, f v ∈ T4 n := by
    rintro ⟨a, b, c, d⟩ hv
    rw [mem_filter, mem_S4] at hv
    obtain ⟨h, ha, hb, hc, hd⟩ := hv
    dsimp only at h ha hb hc hd
    rw [mem_T4]
    have ea := sq_of_pm (mem_pm.mpr ⟨ha, rfl⟩)
    have eb := sq_of_pm (mem_pm.mpr ⟨hb, rfl⟩)
    have ec := sq_of_pm (mem_pm.mpr ⟨hc, rfl⟩)
    have ed := sq_of_pm (mem_pm.mpr ⟨hd, rfl⟩)
    simp only [f]
    generalize (a.natAbs - 1) / 2 = ya at ea ⊢
    generalize (b.natAbs - 1) / 2 = yb at eb ⊢
    generalize (c.natAbs - 1) / 2 = yc at ec ⊢
    generalize (d.natAbs - 1) / 2 = yd at ed ⊢
    apply Nat.cast_injective (R := ℤ)
    push_cast at h ⊢
    nlinarith
  rw [card_eq_sum_card_fiberwise (f := f) (t := T4 n) (fun v hv => mem_coe.mpr (hmaps v (mem_coe.mp hv))), t4,
    card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨y1, y2, y3, y4⟩ := y
  rw [mem_T4] at hy
  have hfib : O.filter (fun v => f v = (y1, y2, y3, y4)) = pm y1 ×ˢ pm y2 ×ˢ pm y3 ×ˢ pm y4 := by
    ext ⟨a, b, c, d⟩
    simp only [O, f, mem_filter, mem_S4, mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, ha, hb, hc, hd⟩, h1, h2, h3, h4⟩
      exact ⟨mem_pm.mpr ⟨ha, h1⟩, mem_pm.mpr ⟨hb, h2⟩, mem_pm.mpr ⟨hc, h3⟩, mem_pm.mpr ⟨hd, h4⟩⟩
    · rintro ⟨ha, hb, hc, hd⟩
      have ea := sq_of_pm ha; have eb := sq_of_pm hb; have ec := sq_of_pm hc; have ed := sq_of_pm hd
      obtain ⟨ha1, ha2⟩ := mem_pm.mp ha; obtain ⟨hb1, hb2⟩ := mem_pm.mp hb
      obtain ⟨hc1, hc2⟩ := mem_pm.mp hc; obtain ⟨hd1, hd2⟩ := mem_pm.mp hd
      refine ⟨⟨?_, ha1, hb1, hc1, hd1⟩, ha2, hb2, hc2, hd2⟩
      have hy' : ((y1 * (y1 + 1) + y2 * (y2 + 1) + y3 * (y3 + 1) + y4 * (y4 + 1) : ℕ) : ℤ)
          = ((2 * n : ℕ) : ℤ) := by rw [hy]
      push_cast at hy' ⊢
      rw [ea, eb, ec, ed]; linarith
  rw [hfib, card_product, card_product, card_product, card_pm, card_pm, card_pm, card_pm]


/-! ## divisor sums -/

lemma B_odd {m : ℕ} (hm : Odd m) :
    ∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℤ) = ∑ d ∈ m.divisors, (d : ℤ) := by
  rw [sum_filter]
  refine sum_congr rfl fun d hd => if_pos fun h4 => ?_
  have := Odd.of_dvd_nat hm (Nat.dvd_of_mem_divisors hd)
  obtain ⟨c, hc⟩ := this; obtain ⟨e, he⟩ := h4; omega

lemma oddSigma_odd {m : ℕ} (hm : Odd m) : oddSigma m = ∑ d ∈ m.divisors, (d : ℤ) := by
  rw [oddSigma, filter_true_of_mem fun d hd => Odd.of_dvd_nat hm (Nat.dvd_of_mem_divisors hd)]

lemma B_two_mul {M : ℕ} (hM : 1 ≤ M) :
    ∑ d ∈ (2 * M).divisors.filter (fun d => ¬ 4 ∣ d), (d : ℤ) = 3 * oddSigma M := by
  rw [sum_filter, sum_divisors_two_mul hM]
  have h3 : ∑ d ∈ M.divisors.filter Odd, (if ¬ 4 ∣ d then (d : ℤ) else 0) = oddSigma M := by
    rw [oddSigma]
    refine sum_congr rfl fun d hd => ?_
    rw [mem_filter] at hd
    rw [if_pos (fun h => by
      obtain ⟨c, hc⟩ := hd.2
      have := Nat.dvd_trans (show 2 ∣ 4 by norm_num) h; omega)]
  have h4 : ∑ e ∈ M.divisors, (if ¬ 4 ∣ 2 * e then ((2 * e : ℕ) : ℤ) else 0) = 2 * oddSigma M := by
    rw [oddSigma, sum_filter, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    by_cases ho : Odd e
    · rw [if_pos ho, if_pos (fun h => by
        rw [four_dvd_two_mul_iff] at h
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h))]
      push_cast; ring
    · rw [if_neg ho, if_neg (fun h => h (by
        rw [four_dvd_two_mul_iff]; exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)))]
      ring
  rw [h3, h4]; ring

/-- **Legendre's theorem**: the number of representations of `n` as an ordered sum of four triangular
numbers `x(x+1)/2` (`x ∈ ℕ`) is `σ(2n+1)`. -/
theorem legendre_four_triangular (n : ℕ) : t4 n = ∑ d ∈ (2 * n + 1).divisors, d := by
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  -- split the solutions of `8n+4` by parity
  have hsplit : r4 (8 * n + 4) = r4 (2 * n + 1) + 16 * t4 n := by
    rw [r4_eq_card, r4_eq_card (2 * n + 1), ← card_even, ← card_odd, ← filter_card_add_filter_neg_card_eq_card
      (fun v : ℤ × ℤ × ℤ × ℤ => v.1 % 2 = 0 ∧ v.2.1 % 2 = 0 ∧ v.2.2.1 % 2 = 0 ∧ v.2.2.2 % 2 = 0)]
    congr 2
    refine filter_congr fun v hv => ?_
    rw [mem_S4] at hv
    have h4 : (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2) % 4 = 0 := by rw [hv]; push_cast; omega
    have := all_even_or_all_odd h4
    omega
  have hA := jacobi_four_squares (N := 8 * n + 4) (by omega)
  have hB := jacobi_four_squares (N := 2 * n + 1) (by omega)
  have hA' : (r4 (8 * n + 4) : ℤ) = 8 * (3 * ∑ d ∈ (2 * n + 1).divisors, (d : ℤ)) := by
    rw [hA]; push_cast
    rw [show 8 * n + 4 = 2 * (4 * n + 2) by ring, B_two_mul (by omega),
      show 4 * n + 2 = 2 * (2 * n + 1) by ring, oddSigma_two_mul (by omega), oddSigma_odd hodd]
  have hB' : (r4 (2 * n + 1) : ℤ) = 8 * ∑ d ∈ (2 * n + 1).divisors, (d : ℤ) := by
    rw [hB]; push_cast; rw [B_odd hodd]
  have : (t4 n : ℤ) = ∑ d ∈ (2 * n + 1).divisors, (d : ℤ) := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hsplit
    push_cast at h
    linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  exact this

/-- **every natural number is a sum of four triangular numbers**. -/
theorem sum_four_triangular (n : ℕ) :
    ∃ a b c d : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 + c * (c + 1) / 2 + d * (d + 1) / 2 = n := by
  have h := legendre_four_triangular n
  have hpos : 0 < t4 n := by
    rw [h]
    exact sum_pos (fun d hd => Nat.pos_of_mem_divisors hd) ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  obtain ⟨⟨a, b, c, d⟩, hx⟩ := card_pos.mp hpos
  rw [mem_T4] at hx
  refine ⟨a, b, c, d, ?_⟩
  have ea : a * (a + 1) = 2 * (a * (a + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self a).two_dvd).symm
  have eb : b * (b + 1) = 2 * (b * (b + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self b).two_dvd).symm
  have ec : c * (c + 1) = 2 * (c * (c + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self c).two_dvd).symm
  have ed : d * (d + 1) = 2 * (d * (d + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self d).two_dvd).symm
  dsimp only at hx
  omega

end FourSquares
