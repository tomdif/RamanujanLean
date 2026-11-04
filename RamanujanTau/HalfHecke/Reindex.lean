import Mathlib

/-!
# Finite reindexing for the coset sums

`ZMod (Q²) = {0} ⊔ Q·(ZMod Q)ˣ ⊔ (ZMod (Q²))ˣ`, and the involutions `x ↦ −(576x)⁻¹` on the units of
`ZMod (Q²)` and of `ZMod Q`, which describe how `S` permutes the cosets of `Γ diag(1,Q²) Γ`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Finset

variable (Q : ℕ) [hQ : Fact Q.Prime]

/-- `x ↦ −(576x)⁻¹`. -/
def sig (n : ℕ) (x : ZMod n) : ZMod n := -(576 * x)⁻¹

/-- `y ↦ Q·y` from `ZMod Q` to `ZMod (Q²)`. -/
def iota (y : ZMod Q) : ZMod (Q ^ 2) := ((Q * y.val : ℕ) : ZMod (Q ^ 2))

section
variable {Q}

lemma iota_val (y : ZMod Q) : (iota Q y).val = Q * y.val := by
  have hQ0 := hQ.out.pos
  haveI : NeZero (Q ^ 2) := ⟨by positivity⟩
  rw [iota, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have := ZMod.val_lt y
  rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left this hQ0

lemma iota_zero : iota Q 0 = 0 := by simp [iota]

lemma isUnit_iff_not_dvd (m : ℕ) (hm : 0 < m) (x : ZMod (Q ^ m)) : IsUnit x ↔ ¬ Q ∣ x.val := by
  haveI : NeZero (Q ^ m) := ⟨pow_ne_zero _ hQ.out.ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd hQ.out]

lemma unit576 (hQ5 : 5 ≤ Q) {m : ℕ} (h : 0 < m) : IsUnit (576 : ZMod (Q ^ m)) := by
  rw [show (576 : ZMod (Q ^ m)) = ((576 : ℕ) : ZMod (Q ^ m)) by norm_num, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff h, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hQ.out]
  intro hd
  have h576 : (576 : ℕ) = 2 ^ 6 * 3 ^ 2 := by norm_num
  rw [h576] at hd
  rcases (Nat.Prime.dvd_mul hQ.out).mp hd with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_two).mp (hQ.out.dvd_of_dvd_pow h2); omega
  · have := (Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_three).mp (hQ.out.dvd_of_dvd_pow h3); omega

lemma sig_spec (hQ5 : 5 ≤ Q) {m : ℕ} (hm : 0 < m) {x : ZMod (Q ^ m)} (hx : IsUnit x) :
    576 * x * sig (Q ^ m) x = -1 := by
  have hu : IsUnit (576 * x) := (unit576 hQ5 hm).mul hx
  rw [sig, mul_neg, ZMod.mul_inv_of_unit _ hu]

lemma sig_unit (hQ5 : 5 ≤ Q) {m : ℕ} (hm : 0 < m) {x : ZMod (Q ^ m)} (hx : IsUnit x) : IsUnit (sig (Q ^ m) x) := by
  have h := sig_spec hQ5 hm hx
  exact IsUnit.of_mul_eq_one (-(576 * x)) (by linear_combination -h)

lemma sig_sig (hQ5 : 5 ≤ Q) {m : ℕ} (hm : 0 < m) {x : ZMod (Q ^ m)} (hx : IsUnit x) :
    sig (Q ^ m) (sig (Q ^ m) x) = x := by
  have h1 := sig_spec hQ5 hm hx
  have h2 := sig_spec hQ5 hm (sig_unit hQ5 hm hx)
  have hu : IsUnit (576 * sig (Q ^ m) x) := (unit576 hQ5 hm).mul (sig_unit hQ5 hm hx)
  obtain ⟨u, hu'⟩ := hu
  have : (576 * sig (Q ^ m) x) * sig (Q ^ m) (sig (Q ^ m) x) = (576 * sig (Q ^ m) x) * x := by
    rw [h2]; linear_combination -h1
  rw [← hu'] at this
  exact (Units.mul_right_inj u).mp this

end

/-- **The split of the `d = Q²` cosets.** -/
theorem sum_split (f : ZMod (Q ^ 2) → ℂ) :
    ∑ x, f x = f 0 + ∑ y ∈ univ.filter (fun y : ZMod Q => y ≠ 0), f (iota Q y)
      + ∑ x ∈ univ.filter (fun x : ZMod (Q ^ 2) => ¬ Q ∣ x.val), f x := by
  have hQ0 := hQ.out.pos
  haveI : NeZero (Q ^ 2) := ⟨by positivity⟩
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x : ZMod (Q ^ 2) => Q ∣ x.val)]
  congr 1
  have hbij : ∑ x ∈ univ.filter (fun x : ZMod (Q ^ 2) => Q ∣ x.val), f x = ∑ y : ZMod Q, f (iota Q y) := by
    refine Finset.sum_nbij' (fun x => ((x.val / Q : ℕ) : ZMod Q)) (iota Q) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact mem_univ _
    · intro y _; simp [iota_val]
    · intro x hx
      have hx : Q ∣ x.val := by simpa using hx
      have hlt : x.val / Q < Q := by
        have h1 := ZMod.val_lt x
        have h2 : x.val < Q * Q := by simpa [pow_two] using h1
        exact Nat.div_lt_of_lt_mul h2
      rw [iota, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel' hx, ZMod.natCast_zmod_val]
    · intro y _
      simp only [iota_val, Nat.mul_div_cancel_left _ hQ0, ZMod.natCast_zmod_val]
    · intro x hx
      congr 1
      have hx : Q ∣ x.val := by simpa using hx
      have hlt : x.val / Q < Q := by
        have h1 := ZMod.val_lt x
        have h2 : x.val < Q * Q := by simpa [pow_two] using h1
        exact Nat.div_lt_of_lt_mul h2
      rw [iota, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel' hx, ZMod.natCast_zmod_val]
  rw [hbij, ← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod Q)), iota_zero]
  congr 2
  ext y; simp

end RamanujanTau.HalfHecke
