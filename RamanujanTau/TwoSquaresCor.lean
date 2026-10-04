/-
# Corollaries of Jacobi's two-square theorem

* **Fermat, with uniqueness**: a prime `p ≡ 1 (mod 4)` has exactly `r₂(p) = 8` representations
  `p = a² + b²` over `ℤ`, i.e. it is a sum of two squares in essentially one way. A prime `p ≡ 3 (mod 4)`
  has none.
* **Gauss's two-triangular count**: `#{(a,b) ∈ ℕ² : a(a+1)/2 + b(b+1)/2 = n} = d₁(4n+1) − d₃(4n+1)`.
-/
import RamanujanTau.TwoSquares
import RamanujanTau.Legendre

set_option autoImplicit false

namespace FourSquares
open Finset

lemma prime_divisors_filter {p : ℕ} (hp : p.Prime) (P : ℕ → Prop) [DecidablePred P] :
    (p.divisors.filter P).card = (if P 1 then 1 else 0) + (if P p then 1 else 0) := by
  rw [Nat.Prime.divisors hp, filter_insert, filter_singleton]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  split_ifs with h1 h2 h2 <;> simp [h1p]

/-- **Fermat's two-square theorem, with uniqueness**: `r₂(p) = 8` for primes `p ≡ 1 (mod 4)`. -/
theorem r2_prime_one_mod_four {p : ℕ} (hp : p.Prime) (h : p % 4 = 1) : r2 p = 8 := by
  have := jacobi_two_squares (N := p) hp.one_lt.le
  rw [prime_divisors_filter hp, prime_divisors_filter hp, if_pos (by norm_num), if_pos h,
    if_neg (by norm_num), if_neg (by omega)] at this
  norm_num at this; exact_mod_cast this

/-- a prime `p ≡ 3 (mod 4)` is not a sum of two squares: `r₂(p) = 0`. -/
theorem r2_prime_three_mod_four {p : ℕ} (hp : p.Prime) (h : p % 4 = 3) : r2 p = 0 := by
  have := jacobi_two_squares (N := p) hp.one_lt.le
  rw [prime_divisors_filter hp, prime_divisors_filter hp, if_pos (by norm_num), if_neg (by omega),
    if_neg (by norm_num), if_pos h] at this
  norm_num at this; exact_mod_cast this

/-! ## Gauss: two triangular numbers -/

noncomputable def S2box (N : ℕ) : Finset (ℤ × ℤ) := (box2 N).filter fun v => v.1 ^ 2 + v.2 ^ 2 = (N : ℤ)

lemma mem_S2box {N : ℕ} {v : ℤ × ℤ} : v ∈ S2box N ↔ v.1 ^ 2 + v.2 ^ 2 = (N : ℤ) := by
  obtain ⟨a, b⟩ := v
  simp only [S2box, box2, mem_filter, mem_product, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have := Int.le_self_sq a; have := Int.le_self_sq (-a); have := Int.le_self_sq b; have := Int.le_self_sq (-b)
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith [sq_nonneg a, sq_nonneg b]

/-- `t₂(n)`: the representations `Σ xᵢ(xᵢ+1) = 2n` with `x ∈ ℕ²`. -/
noncomputable def T2s (n : ℕ) : Finset (ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1)).filter fun x => x.1 * (x.1 + 1) + x.2 * (x.2 + 1) = 2 * n

noncomputable def t2tri (n : ℕ) : ℕ := #(T2s n)

lemma mem_T2s {n : ℕ} {x : ℕ × ℕ} : x ∈ T2s n ↔ x.1 * (x.1 + 1) + x.2 * (x.2 + 1) = 2 * n := by
  obtain ⟨a, b⟩ := x
  simp only [T2s, mem_filter, mem_product, mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩ <;> nlinarith

lemma r2_eight_mul (n : ℕ) : r2 (8 * n + 2) = 4 * t2tri n := by
  rw [show r2 (8 * n + 2) = #(S2box (8 * n + 2)) from rfl]
  let f : ℤ × ℤ → ℕ × ℕ := fun v => ((v.1.natAbs - 1) / 2, (v.2.natAbs - 1) / 2)
  have hodd : ∀ v ∈ S2box (8 * n + 2), v.1 % 2 = 1 ∧ v.2 % 2 = 1 := by
    rintro ⟨a, b⟩ hv
    rw [mem_S2box] at hv
    have h4 : (a ^ 2 + b ^ 2) % 4 = 2 := by rw [hv]; push_cast; omega
    have h1 := sq_mod_four a; have h2 := sq_mod_four b
    dsimp only
    omega
  have hmaps : ∀ v ∈ S2box (8 * n + 2), f v ∈ T2s n := by
    rintro ⟨a, b⟩ hv
    obtain ⟨ha, hb⟩ := hodd _ hv
    rw [mem_S2box] at hv
    dsimp only at ha hb hv
    rw [mem_T2s]
    have ea := sq_of_pm (mem_pm.mpr ⟨ha, rfl⟩)
    have eb := sq_of_pm (mem_pm.mpr ⟨hb, rfl⟩)
    simp only [f]
    generalize (a.natAbs - 1) / 2 = ya at ea ⊢
    generalize (b.natAbs - 1) / 2 = yb at eb ⊢
    apply Nat.cast_injective (R := ℤ)
    push_cast at hv ⊢
    nlinarith
  rw [card_eq_sum_card_fiberwise (f := f) (t := T2s n) (fun v hv => mem_coe.mpr (hmaps v (mem_coe.mp hv))), t2tri,
    card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨y1, y2⟩ := y
  rw [mem_T2s] at hy
  have hfib : (S2box (8 * n + 2)).filter (fun v => f v = (y1, y2)) = pm y1 ×ˢ pm y2 := by
    ext ⟨a, b⟩
    simp only [f, mem_filter, mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨hv, h1, h2⟩
      obtain ⟨ha, hb⟩ := hodd _ hv
      exact ⟨mem_pm.mpr ⟨ha, h1⟩, mem_pm.mpr ⟨hb, h2⟩⟩
    · rintro ⟨ha, hb⟩
      have ea := sq_of_pm ha; have eb := sq_of_pm hb
      obtain ⟨-, ha2⟩ := mem_pm.mp ha; obtain ⟨-, hb2⟩ := mem_pm.mp hb
      refine ⟨?_, ha2, hb2⟩
      rw [mem_S2box]
      have hy' : ((y1 * (y1 + 1) + y2 * (y2 + 1) : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) := by rw [hy]
      push_cast at hy' ⊢
      rw [ea, eb]; linarith
  rw [hfib, card_product, card_pm, card_pm]

lemma odd_divisors_two_mul (M : ℕ) (hM : 1 ≤ M) : (2 * M).divisors.filter Odd = M.divisors.filter Odd := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr h2) h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨dvd_mul_of_dvd_right h1 2, by omega⟩, h2⟩

/-- **Gauss**: the number of ways to write `n` as an ordered sum of two triangular numbers is
`d₁(4n+1) − d₃(4n+1)`. -/
theorem gauss_two_triangular (n : ℕ) :
    (t2tri n : ℤ) = ((4 * n + 1).divisors.filter (fun d => d % 4 = 1)).card
      - ((4 * n + 1).divisors.filter (fun d => d % 4 = 3)).card := by
  have h := jacobi_two_squares (N := 8 * n + 2) (by omega)
  rw [r2_eight_mul, ← chi_sum, show 8 * n + 2 = 2 * (4 * n + 1) by ring, odd_divisors_two_mul _ (by omega),
    chi_sum] at h
  push_cast at h
  linarith

end FourSquares
