/-
# The Tate point at `u = s^k`, `q = s^p` (`1 ≤ k < p`), as series in `K⟦s⟧`

`evB k : ℤ[a]⟦b⟧ → K⟦s⟧`, `a ↦ s^k`, `b ↦ s^{p−k}` (so `u ↦ s^k`, `q = ab ↦ s^p`). These are the
`x`-coordinates of the points of the subgroup `⟨s⟩ ⊂ Tate(s^p)` of order `p`.
`tB m k = θ^m x |_{u = s^k}` satisfies the same differential equations as in `MuSeries`.
-/
import RamanujanTau.TateQuot.Diag
import RamanujanTau.TateQuot.MuQuot

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

local notation "aX" => (Polynomial.X : P)

variable {K : Type*} [Field K]

/-- `ℤ[a] → K⟦s⟧`, `a ↦ s^k`. -/
def φk (K : Type*) [Field K] (k : ℕ) : P →+* PowerSeries K :=
  (Polynomial.aeval (R := ℤ) (X ^ k : PowerSeries K)).toRingHom

/-- `a ↦ s^k`, `b ↦ s^n` (for `n ≥ 1`): `F ↦ Σ_N F_N(s^k) s^{nN}`. -/
def evB (K : Type*) [Field K] (k n : ℕ) : R2 →+* PowerSeries K :=
  diagHom.comp ((rescale (X ^ (n - 1) : PowerSeries K)).comp (PowerSeries.map (φk K k)))

/-- `[s^m] evB F = Σ_N [s^m] (F_N(s^k) · s^{nN})`. -/
lemma coeff_evB (k n : ℕ) (hn : n ≠ 0) (F : R2) (m : ℕ) :
    coeff m (evB K k n F) =
      ∑ N ∈ range (m + 1), coeff m (φk K k (coeff N F) * X ^ (n * N)) := by
  simp only [evB, RingHom.coe_comp, Function.comp_apply, diagHom_apply, coeff_diag,
    coeff_rescale, coeff_map]
  refine sum_congr rfl fun N hN => ?_
  rw [mem_range] at hN
  rw [show n * N = (n - 1) * N + N by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn; simp [Nat.succ_mul]]
  rw [pow_add, ← mul_assoc, coeff_mul_X_pow', if_pos (by omega), ← pow_mul, mul_comm]

lemma rescale_C' {R : Type*} [CommRing R] (r g : R) : rescale r (C g) = C g := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

lemma evB_C (k n : ℕ) (c : P) : evB K k n (C c) = φk K k c := by
  simp only [evB, RingHom.coe_comp, Function.comp_apply, map_C, rescale_C', diagHom_apply, diag_C]

lemma φk_aX (k : ℕ) : φk K k aX = X ^ k := by simp [φk]

lemma φk_apply (k : ℕ) (c : P) : φk K k c = Polynomial.aeval (R := ℤ) (X ^ k : PowerSeries K) c := rfl

lemma φk_intCast (k : ℕ) (c : ℤ) : φk K k (c : P) = (c : PowerSeries K) := by simp [φk]

variable {p : ℕ} [hp : Fact p.Prime]

/-- `evB` of a series in `q = ab`: `f(q) ↦ f(s^p)`. -/
lemma evB_resc {k : ℕ} (hk : k < p) (f : PowerSeries ℤ) :
    evB K k (p - k) (rescale aX (PowerSeries.map (Int.castRingHom P) f)) =
      PowerSeries.expand p hp.out.ne_zero (PowerSeries.map (Int.castRingHom K) f) := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_evB k (p - k) (by omega), coeff_expand]
  have hterm : ∀ N, coeff m (φk K k (coeff N (rescale aX (PowerSeries.map (Int.castRingHom P) f))) *
      X ^ ((p - k) * N)) = if m = p * N then ((coeff N f : ℤ) : K) else 0 := by
    intro N
    rw [coeff_rescale, coeff_map, RingHom.map_mul (φk K k), RingHom.map_pow (φk K k), φk_aX,
      eq_intCast, φk_intCast, ← pow_mul,
      mul_comm, ← mul_assoc, ← pow_add, coeff_X_pow_mul', ← map_intCast (C (R := K)), coeff_C]
    have e : (p - k) * N + k * N = p * N := by
      rw [← add_mul, Nat.sub_add_cancel hk.le]
    rw [e]
    by_cases h : m = p * N
    · subst h; simp
    · rw [if_neg h]
      split_ifs with h1 h2
      · omega
      · rfl
      · rfl
  simp only [hterm]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    simp only [mul_right_inj' hp.out.ne_zero]
    rw [sum_ite_eq, if_pos (by
      have := Nat.le_mul_of_pos_left c hp.out.pos; simp only [mem_range]; omega),
      Nat.mul_div_cancel_left _ hp.out.pos, coeff_map, eq_intCast]
  · refine sum_eq_zero fun N _ => ?_
    rw [if_neg]; rintro rfl; exact hd (dvd_mul_right p N)

/-- `s^k − 1`. -/
def Us (K : Type*) [Field K] (k : ℕ) : PowerSeries K := X ^ k - 1

lemma cc_Us_pow {k : ℕ} (hk : 1 ≤ k) (e : ℕ) : constantCoeff ((Us K k) ^ e) ≠ 0 := by
  rw [map_pow, Us, map_sub, map_pow, constantCoeff_X, zero_pow (by omega), map_one]
  simp

lemma Us_ne {k : ℕ} (hk : 1 ≤ k) : Us K k ≠ 0 := by
  intro h; have := cc_Us_pow (K := K) hk 1; rw [pow_one, h, map_zero] at this; exact this rfl

/-- `θ^m x` at `u = s^k`, `q = s^p`. -/
def tB (K : Type*) [Field K] (p m k : ℕ) : PowerSeries K :=
  evB K k (p - k) (zB m) * ((Us K k) ^ (m + 2))⁻¹

lemma evB_vB (k n : ℕ) : evB K k n vB = Us K k := by
  rw [evB_C]; simp [φk, Us]

lemma evB_zB {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    evB K k (p - k) (zB m) = tB K p m k * Us K k ^ (m + 2) := by
  rw [tB, mul_assoc, PowerSeries.inv_mul_cancel _ (cc_Us_pow hk _), mul_one]

/-- `a₄(s^p)`. -/
def a4s (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime] : PowerSeries K :=
  PowerSeries.expand p hp.out.ne_zero a4K
/-- `a₆(s^p)`. -/
def a6s (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime] : PowerSeries K :=
  PowerSeries.expand p hp.out.ne_zero a6K

lemma evB_a4B {k : ℕ} (hk : k < p) : evB K k (p - k) a4B = a4s K p := evB_resc hk _
lemma evB_a6B {k : ℕ} (hk : k < p) : evB K k (p - k) a6B = a6s K p := evB_resc hk _

theorem tB_weier {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    tB K p 1 k ^ 2 = 4 * tB K p 0 k ^ 3 + tB K p 0 k ^ 2 + 4 * a4s K p * tB K p 0 k +
      4 * a6s K p := by
  have h := congrArg (evB K k (p - k)) EB_v
  simp only [map_add, map_mul, map_pow, map_ofNat, evB_zB hk1, evB_vB, evB_a4B hk,
    evB_a6B hk] at h
  apply mul_right_cancel₀ (pow_ne_zero 6 (Us_ne (K := K) hk1))
  linear_combination h

theorem tB_two {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    tB K p 2 k = 6 * tB K p 0 k ^ 2 + tB K p 0 k + 2 * a4s K p := by
  have h := congrArg (evB K k (p - k)) zB2_eq
  simp only [map_add, map_mul, map_pow, map_ofNat, evB_zB hk1, evB_vB, evB_a4B hk] at h
  apply mul_right_cancel₀ (pow_ne_zero 4 (Us_ne (K := K) hk1))
  linear_combination h

theorem tB_four {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    tB K p 4 k = 120 * tB K p 0 k ^ 3 + 30 * tB K p 0 k ^ 2 + (72 * a4s K p + 1) * tB K p 0 k +
      48 * a6s K p + 2 * a4s K p := by
  have h := congrArg (evB K k (p - k)) zB4_eq
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, evB_zB hk1, evB_vB, evB_a4B hk,
    evB_a6B hk] at h
  apply mul_right_cancel₀ (pow_ne_zero 6 (Us_ne (K := K) hk1))
  linear_combination h

end TateQuot
