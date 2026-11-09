/-
# `q ↦ −q` bookkeeping and `ψ(q)` for the forty identities

* `Ng_Ng`, `Ng_X`, `Ng_S_even` (`f(q^{2k})` is even), `Ng_S5` (`(q ↦ −q) ∘ (q ↦ q⁵) = (q ↦ q⁵) ∘ (q ↦ −q)`).
* `Ng_Pinf_even`: `(q^{2b};q^{2a})_∞` is even; `Ng_E1`: `(−q;−q)_∞ = f(−q²) χ(q)`.
* `Ng_phi`: `φ(−q) = (q;q²)²_∞ f(−q²)`.
* `psi_mul`: `ψ(q) (q;q²)_∞ = (q²;q²)_∞`, with `ψ(q) = f(q,q³) = Σ_{n≥0} q^{n(n+1)/2}` (`ramF 1 3`).
-/
import RamanujanTau.Forty.E03

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf isUnit_Pinf)

lemma Ng_Ng (f : PowerSeries ℤ) : Ng (Ng f) = f := by
  ext n; simp only [Ng, coeff_rescale, ← mul_assoc, ← mul_pow]; norm_num

lemma Ng_X : Ng X = -X := by
  rw [Ng, rescale_X]; simp

lemma coeff_S (a : ℕ) [NeZero a] (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (S a f) = if a ∣ n then coeff (n / a) f else 0 := RankProof.coeff_Ea a _ n f

lemma Ng_S_even (k : ℕ) [NeZero (2 * k)] (f : PowerSeries ℤ) : Ng (S (2 * k) f) = S (2 * k) f := by
  ext n
  rw [Ng, coeff_rescale, coeff_S]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [show 2 * k * m = 2 * (k * m) by ring, pow_mul]; norm_num
  · simp

lemma Ng_S_ev (a : ℕ) [NeZero a] (ha : 2 ∣ a) (f : PowerSeries ℤ) : Ng (S a f) = S a f := by
  ext n
  rw [Ng, coeff_rescale, coeff_S]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := ha.trans h
    rw [pow_mul]; norm_num
  · simp

lemma Ng_S5 (f : PowerSeries ℤ) : Ng (S 5 f) = S 5 (Ng f) := by
  ext n
  rw [Ng, coeff_rescale, coeff_S, coeff_S]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (by norm_num), ← Ng, Ng, coeff_rescale, pow_mul]; norm_num
  · simp

lemma Ng_Pinf_even (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : Ng (Pinf (2 * b) (2 * a)) = Pinf (2 * b) (2 * a) := by
  have h := Ng_S_even 1 (Pinf b a)
  rw [S_Pinf 2 b a hb ha] at h
  exact h

lemma S_one' (f : PowerSeries ℤ) : S 1 f = f := S_one f

lemma Ng_P12 : Ng (Pinf 1 2) = chip 1 := by rw [chip, S_one]

lemma Ng_chip1 : Ng (chip 1) = Pinf 1 2 := by rw [← Ng_P12, Ng_Ng]

lemma E1_split : Pinf 1 1 = Pinf 1 2 * Pinf 2 2 := by
  have h := atom 1 1 2 le_rfl (by norm_num) (by norm_num) le_rfl
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  norm_num at h
  exact h

/-- `(−q;−q)_∞ = (q²;q²)_∞ χ(q)`. -/
lemma Ng_E1 : Ng (Pinf 1 1) = Pinf 2 2 * chip 1 := by
  rw [E1_split, map_mul, Ng_P12, Ng_P22]; ring

/-- `φ(−q) = (q;q²)²_∞ (q²;q²)_∞`. -/
lemma Ng_phi : Ng RamanujanTau.Septic.phi = Pinf 1 2 ^ 2 * Pinf 2 2 := by
  rw [phi_chip, map_mul, map_pow, Ng_chip1, Ng_P22]

/-- `ψ(q) = χ(q) (q⁴;q⁴)_∞`. -/
lemma psi_chip : RamanujanTau.Septic.ramF 1 3 = chip 1 * Pinf 4 4 := by
  rw [RamanujanTau.Septic.ramF_product (by decide) (by decide)]
  change Ng _ = _
  have h := atom 1 2 4 le_rfl (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  norm_num at h
  rw [map_mul, map_mul, ← map_mul, ← h, Ng_P12, show (1 + 3 : ℕ) = 2 * 2 by rfl, Ng_Pinf_even 2 2 (by norm_num) (by norm_num)]

/-- `ψ(q) (q;q²)_∞ = (q²;q²)_∞`. -/
lemma psi_mul : RamanujanTau.Septic.ramF 1 3 * Pinf 1 2 = Pinf 2 2 := by
  have hc := chip_mul 1
  norm_num at hc
  have h := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  norm_num at h
  rw [psi_chip, h]
  linear_combination Pinf 4 4 * hc

end Forty
