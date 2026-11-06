/-
# M3, step 1: the diagonal `bdn = acm` is the ray `(m, n) = (Q₁ r, P₁ r)`

For `a, b, c, d ≥ 1`, `P = ac`, `Q = bd`, `g = (P, Q)`, `P₁ = P/g`, `Q₁ = Q/g` (coprime):

    {(m, n) : n Q = m P} = {(Q₁ r, P₁ r) : r ∈ ℕ},

so the diagonal part of the lag series is a single sum over `r` (`diagS_eq_tsum_ray`):

    diagS a b c d u u' = Σ_r sTerm u u' (Q₁ r, P₁ r).

This is the first line of the paper evaluation (`docs/SELBERG_KEY.md` §3).  Level 1.
-/
import RamanujanTau.SelbergKey.Arith

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.SelbergKeyDiag

open RamanujanTau.SelbergKey

section
variable {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
include ha hb hc hd

lemma gcd_PQ_pos : 0 < Nat.gcd (a * c) (b * d) :=
  Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hc)

lemma P1_mul_g : P1 a b c d * Nat.gcd (a * c) (b * d) = a * c :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

lemma Q1_mul_g : Q1 a b c d * Nat.gcd (a * c) (b * d) = b * d :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

lemma P1_pos : 1 ≤ P1 a b c d := by
  have h := P1_mul_g ha hb hc hd
  rcases Nat.eq_zero_or_pos (P1 a b c d) with h0 | h0
  · rw [h0, zero_mul] at h; have := Nat.mul_pos ha hc; omega
  · exact h0

lemma Q1_pos : 1 ≤ Q1 a b c d := by
  have h := Q1_mul_g ha hb hc hd
  rcases Nat.eq_zero_or_pos (Q1 a b c d) with h0 | h0
  · rw [h0, zero_mul] at h; have := Nat.mul_pos hb hd; omega
  · exact h0

lemma coprime_P1_Q1 : Nat.Coprime (P1 a b c d) (Q1 a b c d) :=
  Nat.coprime_div_gcd_div_gcd (gcd_PQ_pos ha hb hc hd)

/-- The ray points are diagonal. -/
lemma isDiag_ray (r : ℕ) : isDiag a b c d (Q1 a b c d * r, P1 a b c d * r) := by
  unfold isDiag
  have h1 := P1_mul_g ha hb hc hd
  have h2 := Q1_mul_g ha hb hc hd
  simp only
  set g := Nat.gcd (a * c) (b * d)
  calc P1 a b c d * r * b * d = P1 a b c d * r * (b * d) := by ring
    _ = P1 a b c d * r * (Q1 a b c d * g) := by rw [h2]
    _ = Q1 a b c d * r * (P1 a b c d * g) := by ring
    _ = Q1 a b c d * r * (a * c) := by rw [h1]
    _ = Q1 a b c d * r * a * c := by ring

/-- Every diagonal point is on the ray. -/
lemma ray_of_isDiag {p : ℕ × ℕ} (hp : isDiag a b c d p) :
    ∃ r, p = (Q1 a b c d * r, P1 a b c d * r) := by
  unfold isDiag at hp
  have h1 := P1_mul_g ha hb hc hd
  have h2 := Q1_mul_g ha hb hc hd
  have hg := gcd_PQ_pos ha hb hc hd
  set g := Nat.gcd (a * c) (b * d)
  set P := P1 a b c d
  set Q := Q1 a b c d
  have hcop : Nat.Coprime P Q := coprime_P1_Q1 ha hb hc hd
  -- `n Q₁ = m P₁`
  have e : p.2 * Q = p.1 * P := by
    have : p.2 * Q * g = p.1 * P * g := by
      calc p.2 * Q * g = p.2 * (Q * g) := by ring
        _ = p.2 * b * d := by rw [h2]; ring
        _ = p.1 * a * c := hp
        _ = p.1 * (P * g) := by rw [h1]; ring
        _ = p.1 * P * g := by ring
    exact Nat.eq_of_mul_eq_mul_right hg this
  have hQ : Q ∣ p.1 := by
    have : Q ∣ p.1 * P := ⟨p.2, by rw [← e]; ring⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right this
  obtain ⟨r, hr⟩ := hQ
  refine ⟨r, Prod.ext hr ?_⟩
  have hQ1 : 0 < Q := Q1_pos ha hb hc hd
  have : p.2 * Q = P * r * Q := by rw [e, hr]; ring
  exact Nat.eq_of_mul_eq_mul_right hQ1 this

/-- **The diagonal of the lag series is a single sum along the ray** (level 1). -/
theorem diagS_eq_tsum_ray (u u' : ℝ) :
    diagS a b c d u u' = ∑' r : ℕ, sTerm u u' (Q1 a b c d * r, P1 a b c d * r) := by
  have hQ1 := Q1_pos ha hb hc hd
  set f : ℕ → ℕ × ℕ := fun r => (Q1 a b c d * r, P1 a b c d * r) with hf
  have hinj : Function.Injective f := by
    intro r s hrs
    have := congrArg Prod.fst hrs
    simp only [hf] at this
    exact Nat.eq_of_mul_eq_mul_left hQ1 this
  unfold diagS
  rw [← hinj.tsum_eq (f := fun p => if isDiag a b c d p then sTerm u u' p else 0) ?_]
  · refine tsum_congr fun r => ?_
    simp only [hf]
    rw [if_pos (isDiag_ray ha hb hc hd r)]
  · intro p hp
    rw [Function.mem_support] at hp
    by_cases hd' : isDiag a b c d p
    · obtain ⟨r, hr⟩ := ray_of_isDiag ha hb hc hd hd'
      exact ⟨r, hr.symm⟩
    · exact absurd (if_neg hd') hp

end

end RamanujanTau.SelbergKeyDiag
