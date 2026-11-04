import RamanujanTau.HalfHecke.Transfer
import RamanujanTau.HalfHecke.Reindex

/-!
# Arithmetic facts for the `S`-transformation of the coset sum

Petersson's multiplier on the three kinds of `γ` that occur (`S`; `c = Q²`; `c = Q`), the
quadratic-character identities, and the involution `y ↦ −(576y)⁻¹` on `(ZMod Q)ˣ`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex Finset
open RamanujanTau.ThetaLift
open scoped Real

noncomputable section

variable {Q : ℕ} [hQ : Fact Q.Prime]

lemma Q_odd (hQ5 : 5 ≤ Q) : Odd Q := hQ.out.odd_of_ne_two (by omega)

lemma Qsq_int (hQ5 : 5 ≤ Q) : (Q : ℤ) ^ 2 = 24 * (dQ Q : ℤ) + 1 := by
  have := dQ_spec hQ5; exact_mod_cast this.symm

/-- The multiplier of `S`. -/
lemma mult_S : e24 (-3) / ((jacobiSym 0 1 : ℂ) * e24 (petE 0 (-1) 1 0)) = 1 := by
  rw [jacobiSym.one_right]
  have : petE 0 (-1) 1 0 = -3 := by unfold petE; norm_num
  rw [this]; simp [e24_ne_zero]

/-- The multiplier for `c = Q²`. -/
lemma mult_Q2 (hQ5 : 5 ≤ Q) (b b' t : ℤ) (hb : ((-24 * b' : ℤ) : ZMod Q) ≠ 0) :
    e24 (-3) / ((jacobiSym (-24 * b') (Q ^ 2) : ℂ) * e24 (petE (24 * b) (-t) ((Q ^ 2 : ℕ) : ℤ) (-24 * b'))) = 1 := by
  have hj : jacobiSym (-24 * b') (Q ^ 2) = 1 := by
    rw [jacobiSym.pow_right, ← jacobiSym.legendreSym.to_jacobiSym]
    exact legendreSym.sq_one Q hb
  have hQ2 := Qsq_int hQ5
  have he : e24 (petE (24 * b) (-t) ((Q ^ 2 : ℕ) : ℤ) (-24 * b')) = e24 (-3) := by
    apply e24_eq_of_dvd
    unfold petE
    push_cast
    rw [hQ2]
    exact ⟨(b - b') * (24 * dQ Q + 1) - t * b' * ((24 * dQ Q + 1) ^ 2 - 1) - 3 * dQ Q, by ring⟩
  rw [hj, he]; simp [e24_ne_zero]

/-- The multiplier for `c = Q`. -/
lemma mult_Q (hQ5 : 5 ≤ Q) (b b2 t : ℤ) (hb : ((-24 * b2 : ℤ) : ZMod Q) ≠ 0) :
    e24 (-3) / ((jacobiSym (-24 * b2) Q : ℂ) * e24 (petE (24 * b) (-t) (Q : ℤ) (-24 * b2))) =
      chiQ Q ((-24 * b2 : ℤ) : ZMod Q) * e24 (3 * Q - 3) := by
  have hQ2 := Qsq_int hQ5
  have he : e24 (petE (24 * b) (-t) (Q : ℤ) (-24 * b2)) = e24 (-3 * Q) := by
    apply e24_eq_of_dvd
    unfold petE
    rw [hQ2]
    exact ⟨(b - b2) * Q - 24 * t * b2 * (dQ Q), by ring⟩
  rw [he, chiQ_intCast, jacobiSym.legendreSym.to_jacobiSym]
  have hsq := legendreSym.sq_one Q hb
  rw [jacobiSym.legendreSym.to_jacobiSym] at hsq
  have hJ : (jacobiSym (-24 * b2) Q : ℂ) * (jacobiSym (-24 * b2) Q : ℂ) = 1 := by
    rw [← sq]; exact_mod_cast hsq
  have hsplit : e24 (-3) = e24 (-3 * Q) * e24 (3 * Q - 3) := by rw [← e24_add]; congr 1; ring
  have h0 := e24_ne_zero (-3 * Q)
  have hJ0 : (jacobiSym (-24 * b2) Q : ℂ) ≠ 0 := fun h => by rw [h, zero_mul] at hJ; exact zero_ne_one hJ
  rw [hsplit, mul_comm ((jacobiSym (-24 * b2) Q : ℤ) : ℂ), ← div_div, mul_div_cancel_left₀ _ h0,
    div_eq_iff hJ0]
  linear_combination -(e24 (3 * Q - 3)) * hJ

/-- `(−1/Q) e(6(Q−1)/24) = 1`. -/
lemma chi_neg_one_e24 (hQ5 : 5 ≤ Q) : chiQ Q (-1) * e24 (6 * ((Q : ℤ) - 1)) = 1 := by
  have h := chiQ_intCast Q (-1)
  push_cast at h
  rw [h, legendreSym.at_neg_one (by omega)]
  obtain ⟨m, hm⟩ := Q_odd hQ5
  have e : 6 * ((Q : ℤ) - 1) = 12 * (m : ℕ) := by rw [hm]; push_cast; ring
  rw [e, e24_twelve_mul]
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · rw [ZMod.χ₄_nat_one_mod_four (by omega), Even.neg_one_pow ⟨n, hn⟩]; norm_num
  · rw [ZMod.χ₄_nat_three_mod_four (by omega), Odd.neg_one_pow ⟨n, hn⟩]; norm_num

/-! ### The involution on `(ZMod Q)ˣ` -/

lemma n576 (hQ5 : 5 ≤ Q) : (576 : ZMod Q) ≠ 0 := by
  rw [show (576 : ZMod Q) = ((576 : ℕ) : ZMod Q) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have h576 : (576 : ℕ) = 2 ^ 6 * 3 ^ 2 := by norm_num
  rw [h576] at hd
  rcases (Nat.Prime.dvd_mul hQ.out).mp hd with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_two).mp (hQ.out.dvd_of_dvd_pow h2); omega
  · have := (Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_three).mp (hQ.out.dvd_of_dvd_pow h3); omega

lemma sig1_spec (hQ5 : 5 ≤ Q) {y : ZMod Q} (hy : y ≠ 0) : 576 * y * sig Q y = -1 := by
  rw [sig, mul_neg, mul_inv_cancel₀ (mul_ne_zero (n576 hQ5) hy)]

lemma sig1_ne (hQ5 : 5 ≤ Q) {y : ZMod Q} (hy : y ≠ 0) : sig Q y ≠ 0 := by
  intro h; have := sig1_spec hQ5 hy; rw [h, mul_zero] at this
  have h1 : (1 : ZMod Q) = 0 := by linear_combination this
  exact one_ne_zero h1

lemma sig1_sig (hQ5 : 5 ≤ Q) {y : ZMod Q} (hy : y ≠ 0) : sig Q (sig Q y) = y := by
  have h1 := sig1_spec hQ5 hy
  have h2 := sig1_spec hQ5 (sig1_ne hQ5 hy)
  have hu : 576 * sig Q y ≠ 0 := mul_ne_zero (n576 hQ5) (sig1_ne hQ5 hy)
  have : (576 * sig Q y) * sig Q (sig Q y) = (576 * sig Q y) * y := by
    rw [h2]; linear_combination -h1
  exact mul_left_cancel₀ hu this

/-- `χ(y)χ(−(576y)⁻¹) = χ(−1)`. -/
lemma chi_sig (hQ5 : 5 ≤ Q) {y : ZMod Q} (hy : y ≠ 0) : chiQ Q y * chiQ Q (sig Q y) = chiQ Q (-1) := by
  have h1 := sig1_spec hQ5 hy
  have h24 : (24 : ZMod Q) ≠ 0 := fun h => n576 hQ5 (by
    rw [show (576 : ZMod Q) = 24 * 24 by norm_num, h, zero_mul])
  have hc : chiQ Q 576 = 1 := by
    rw [show (576 : ZMod Q) = 24 * 24 by norm_num, map_mul, chiQ_sq Q 24 h24]
  rw [← h1, map_mul, map_mul, hc, one_mul]

lemma sum_sig1 (hQ5 : 5 ≤ Q) (h : ZMod Q → ℂ) :
    ∑ y ∈ univ.filter (fun y : ZMod Q => y ≠ 0), h (sig Q y) =
      ∑ y ∈ univ.filter (fun y : ZMod Q => y ≠ 0), h y := by
  refine Finset.sum_nbij' (sig Q) (sig Q) ?_ ?_ ?_ ?_ ?_
  · intro y hy; have hy : y ≠ 0 := by simpa using hy
    simpa using sig1_ne hQ5 hy
  · intro y hy; have hy : y ≠ 0 := by simpa using hy
    simpa using sig1_ne hQ5 hy
  · intro y hy; have hy : y ≠ 0 := by simpa using hy
    exact sig1_sig hQ5 hy
  · intro y hy; have hy : y ≠ 0 := by simpa using hy
    exact sig1_sig hQ5 hy
  · intro y _; rfl

lemma sum_sig2 (hQ5 : 5 ≤ Q) (h : ZMod (Q ^ 2) → ℂ) :
    ∑ x ∈ univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val), h (sig (Q ^ 2) x) =
      ∑ x ∈ univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val), h x := by
  have hm : (0 : ℕ) < 2 := by norm_num
  have key : ∀ y : ZMod (Q ^ 2), y ∈ (univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val) : Set _) →
      IsUnit y := by
    intro y hy
    have hy : ¬ Q ∣ y.val := by simpa using hy
    exact (isUnit_iff_not_dvd 2 hm y).mpr hy
  have key2 : ∀ y : ZMod (Q ^ 2), IsUnit y →
      y ∈ (univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val) : Set _) := by
    intro y hy
    simpa using (isUnit_iff_not_dvd 2 hm y).mp hy
  refine Finset.sum_nbij' (sig (Q ^ 2)) (sig (Q ^ 2)) ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact key2 _ (sig_unit hQ5 hm (key y hy))
  · intro y hy; exact key2 _ (sig_unit hQ5 hm (key y hy))
  · intro y hy; exact sig_sig hQ5 hm (key y hy)
  · intro y hy; exact sig_sig hQ5 hm (key y hy)
  · intro y _; rfl

end

end RamanujanTau.HalfHecke
