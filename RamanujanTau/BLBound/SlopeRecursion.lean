import RamanujanTau.BLBound.RCLift

/-!
# Exact algebra behind the slope recursion

These are the unconditional algebraic parts of `docs/BL_SHARPNESS_PROOF.md` §4.6–4.8, for arbitrary power series.

* `U_bracket_expand`: `U[g, VW]_j = ℓ^j [Ug, W]_j`, for any bracket coefficients.
* `U_serreD`: `U D_K = ℓ ∂_K U - ℓ K U R`, where `(ℓ-1) R = P - ℓ VP`.
* `serreD_sub_theta`, `serreD_mul_flat`: `D_K ≡ θ` mod `ℓ`, and flat `W` commute with `D`.
* `recursion_step`: the step of the recursion, with the consequence of the matrix bound as an explicit hypothesis.
* `serre_filtration`: `∂_K z = (1 - K/W) θz + (K/W) ∂_W z`.
* `bol_product`, `chain_product`: the two products closing the descent from classical weight.

Nothing here states the matrix bound, the slope decomposition, or the classical endpoint. Those are not formalized.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries Igusa BoylanWebb

noncomputable section

section Ring
variable {R : Type*} [CommRing R]

lemma theta_natCast_pow_mul (ℓ r : ℕ) (f : PowerSeries R) :
    theta ((ℓ : PowerSeries R) ^ r * f) = (ℓ : PowerSeries R) ^ r * theta f := by
  have h : (ℓ : PowerSeries R) ^ r = C ((ℓ : R) ^ r) := by rw [map_pow, map_natCast]
  ext n
  rw [h, coeff_theta, coeff_C_mul, coeff_C_mul, coeff_theta]
  ring

lemma U_natCast_pow_mul (ℓ m r : ℕ) (f : PowerSeries R) :
    U ℓ ((m : PowerSeries R) ^ r * f) = (m : PowerSeries R) ^ r * U ℓ f := by
  have h : (m : PowerSeries R) ^ r = C ((m : R) ^ r) := by rw [map_pow, map_natCast]
  rw [h, U_C_mul]

lemma U_add (ℓ : ℕ) (f g : PowerSeries R) : U ℓ (f + g) = U ℓ f + U ℓ g := by
  ext n
  simp [coeff_U]

lemma U_sum {ι : Type*} (ℓ : ℕ) (s : Finset ι) (f : ι → PowerSeries R) :
    U ℓ (∑ i ∈ s, f i) = ∑ i ∈ s, U ℓ (f i) := by
  ext n
  simp [coeff_U]

lemma theta_expand (ℓ : ℕ) (hℓ : ℓ ≠ 0) (b : PowerSeries R) :
    theta (PowerSeries.expand ℓ hℓ b) = (ℓ : PowerSeries R) * PowerSeries.expand ℓ hℓ (theta b) := by
  ext n
  rw [coeff_theta, ← map_natCast (C (R := R)), coeff_C_mul, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hd
  · obtain ⟨t, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ), coeff_theta]
    push_cast
    ring
  · simp

lemma U_theta_iter (ℓ r : ℕ) (f : PowerSeries R) :
    U ℓ (theta^[r] f) = (ℓ : PowerSeries R) ^ r * theta^[r] (U ℓ f) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', U_theta, ih, theta_natCast_pow_mul]
    ring

lemma theta_iter_expand (ℓ : ℕ) (hℓ : ℓ ≠ 0) (n : ℕ) (b : PowerSeries R) :
    theta^[n] (PowerSeries.expand ℓ hℓ b) =
      (ℓ : PowerSeries R) ^ n * PowerSeries.expand ℓ hℓ (theta^[n] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, theta_natCast_pow_mul, theta_expand]
    ring

/-- A bracket with arbitrary coefficients `c`; the Rankin–Cohen bracket is one choice of `c`. -/
def bracket (c : ℕ → R) (j : ℕ) (g W : PowerSeries R) : PowerSeries R :=
  ∑ r ∈ Finset.range (j + 1), C (c r) * (theta^[r] g * theta^[j - r] W)

/-- **`U[g, VW]_j = ℓ^j [Ug, W]_j`**. -/
theorem U_bracket_expand (ℓ : ℕ) (hℓ : ℓ ≠ 0) (c : ℕ → R) (j : ℕ) (g W : PowerSeries R) :
    U ℓ (bracket c j g (PowerSeries.expand ℓ hℓ W)) = (ℓ : PowerSeries R) ^ j * bracket c j (U ℓ g) W := by
  unfold bracket
  rw [U_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hpow : (ℓ : PowerSeries R) ^ j = (ℓ : PowerSeries R) ^ (j - r) * (ℓ : PowerSeries R) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr']
  rw [U_C_mul, theta_iter_expand]
  have : theta^[r] g * ((ℓ : PowerSeries R) ^ (j - r) * PowerSeries.expand ℓ hℓ (theta^[j - r] W)) =
      (ℓ : PowerSeries R) ^ (j - r) * (theta^[r] g * PowerSeries.expand ℓ hℓ (theta^[j - r] W)) := by ring
  rw [this, U_natCast_pow_mul, U_mul_expand, U_theta_iter, hpow]
  ring

/-- The Serre derivative attached to `P`, on weight `K`. -/
def serreP (P : PowerSeries R) (K : R) (f : PowerSeries R) : PowerSeries R := theta f - C K * (P * f)

/-- `D_K = ∂_K - K R`. -/
def serreD (P r : PowerSeries R) (K : R) (f : PowerSeries R) : PowerSeries R :=
  serreP P K f - C K * (r * f)

/-- **`U D_K = ℓ ∂_K U - ℓ K U R`**, when `(ℓ-1) R = P - ℓ VP`. No modularity is used. -/
theorem U_serreD (ℓ : ℕ) (hℓ : ℓ ≠ 0) (P r : PowerSeries R) (K : R)
    (hr : ((ℓ : PowerSeries R) - 1) * r = P - (ℓ : PowerSeries R) * PowerSeries.expand ℓ hℓ P)
    (f : PowerSeries R) :
    U ℓ (serreD P r K f) =
      (ℓ : PowerSeries R) * serreP P K (U ℓ f) - (ℓ : PowerSeries R) * (C K * U ℓ (r * f)) := by
  have hP : U ℓ (P * f) = (ℓ : PowerSeries R) * (P * U ℓ f) + (((ℓ : PowerSeries R) - 1) * U ℓ (r * f)) := by
    have h1 : P * f = ((ℓ : PowerSeries R) - 1) * (r * f) +
        (ℓ : PowerSeries R) * (f * PowerSeries.expand ℓ hℓ P) := by
      linear_combination (-f) * hr
    rw [h1, U_add, U_natCast_mul, U_mul_expand, sub_mul, one_mul, U_sub, U_natCast_mul]
    ring
  unfold serreD serreP
  rw [U_sub, U_sub, U_C_mul, U_C_mul, U_theta, hP]
  ring

/-- `D_K ≡ θ` modulo `ℓ`: `(ℓ-1)(D_K f - θ f) = -ℓ K (P - VP) f`. -/
theorem serreD_sub_theta (ℓ : ℕ) (hℓ : ℓ ≠ 0) (P r : PowerSeries R) (K : R)
    (hr : ((ℓ : PowerSeries R) - 1) * r = P - (ℓ : PowerSeries R) * PowerSeries.expand ℓ hℓ P)
    (f : PowerSeries R) :
    ((ℓ : PowerSeries R) - 1) * (serreD P r K f - theta f) =
      -((ℓ : PowerSeries R) * (C K * ((P - PowerSeries.expand ℓ hℓ P) * f))) := by
  unfold serreD serreP
  linear_combination (-(C K * f)) * hr

/-- A flat `W` of weight `l` commutes with `D`: if `θW = l (P+R) W` then `D_{K+l}(W f) = W D_K f`. -/
theorem serreD_mul_flat (P r : PowerSeries R) (K l : R) (W f : PowerSeries R)
    (hW : theta W = C l * ((P + r) * W)) :
    serreD P r (K + l) (W * f) = W * serreD P r K f := by
  unfold serreD serreP
  rw [theta_mul, hW, map_add]
  ring

/-- **The recursion step.** `π` is any additive map commuting with `U` up to `Ũ`. The consequence of the matrix bound
appears as the hypothesis `hRy`, and is not proved here. -/
theorem recursion_step {N : Type*} [AddCommGroup N] [Module (PowerSeries R) N]
    (ℓ j : ℕ) (hℓ : ℓ ≠ 0) (P r : PowerSeries R) (K : R)
    (hr : ((ℓ : PowerSeries R) - 1) * r = P - (ℓ : PowerSeries R) * PowerSeries.expand ℓ hℓ P)
    (π : PowerSeries R →ₗ[PowerSeries R] N)
    (y y' : PowerSeries R) (hy : U ℓ y = (ℓ : PowerSeries R) ^ (j - 1) * y') (hj : 1 ≤ j)
    (t : PowerSeries R) (hRy : π (U ℓ (r * y)) = ((ℓ : PowerSeries R) ^ j) • π t) :
    π (U ℓ (serreD P r K y)) =
      ((ℓ : PowerSeries R) ^ j) • π (serreP P K y') -
        ((ℓ : PowerSeries R) ^ (j + 1) * C K) • π t := by
  have hpow : (ℓ : PowerSeries R) * (ℓ : PowerSeries R) ^ (j - 1) = (ℓ : PowerSeries R) ^ j := by
    rw [← pow_succ', Nat.sub_add_cancel hj]
  have hserre : serreP P K ((ℓ : PowerSeries R) ^ (j - 1) * y') =
      (ℓ : PowerSeries R) ^ (j - 1) * serreP P K y' := by
    unfold serreP
    rw [theta_natCast_pow_mul]
    ring
  rw [U_serreD ℓ hℓ P r K hr, hy, hserre, ← mul_assoc, hpow]
  have hA : π ((ℓ : PowerSeries R) ^ j * serreP P K y') = ((ℓ : PowerSeries R) ^ j) • π (serreP P K y') := by
    rw [← smul_eq_mul, map_smul]
  have hB : π ((ℓ : PowerSeries R) * (C K * U ℓ (r * y))) =
      ((ℓ : PowerSeries R) * C K) • π (U ℓ (r * y)) := by
    rw [← mul_assoc, ← smul_eq_mul, map_smul]
  rw [map_sub, hA, hB, hRy, smul_smul,
    show (ℓ : PowerSeries R) * C K * (ℓ : PowerSeries R) ^ j = (ℓ : PowerSeries R) ^ (j + 1) * C K by ring]

end Ring

section Field
variable {F : Type*} [Field F]

/-- **`∂_K z = (1 - K/W) θz + (K/W) ∂_W z`**. So modulo the image of `∂_W`, `∂_K` is `θ` times `(W-K)/W`. -/
theorem serre_filtration (P : PowerSeries F) (K W : F) (hW : W ≠ 0) (z : PowerSeries F) :
    serreP P K z = C ((W - K) / W) * theta z + C (K / W) * serreP P W z := by
  unfold serreP
  have h1 : (C ((W - K) / W) : PowerSeries F) + C (K / W) = 1 := by
    rw [← map_add, show (W - K) / W + K / W = 1 by field_simp; ring, map_one]
  have h2 : (C (K / W) : PowerSeries F) * C W = C K := by
    rw [← map_mul, div_mul_cancel₀ _ hW]
  linear_combination (-theta z) * h1 + (P * z) * h2

end Field

section Products
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- With `k = ℓ - n`, reversing the order gives `∏_{m<n} (k+m) = ∏_{m<n} (-1-m)`. -/
lemma prod_k_add (n k : ℕ) (hk : k + n = ℓ) :
    ∏ m ∈ Finset.range n, ((k : ZMod ℓ) + m) = ∏ m ∈ Finset.range n, (-1 - (m : ZMod ℓ)) := by
  have hkz : (k : ZMod ℓ) = -(n : ZMod ℓ) := by
    have : (k : ZMod ℓ) + n = 0 := by
      rw [← Nat.cast_add, hk, CharP.cast_eq_zero]
    linear_combination this
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun m hm => ?_
  have hm' : m < n := Finset.mem_range.mp hm
  have : ((n - 1 - m : ℕ) : ZMod ℓ) = (n : ZMod ℓ) - 1 - m := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  rw [this, hkz]
  ring

/-- `(k+m)` is a unit for `m < n` when `k + n = ℓ`, `1 ≤ k`. -/
lemma k_add_ne_zero (n k m : ℕ) (hk : k + n = ℓ) (hk1 : 1 ≤ k) (hm : m < n) : (k : ZMod ℓ) + m ≠ 0 := by
  rw [← Nat.cast_add, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- **The Bol endpoint**: `∏_{m<n} (-1-m)/(k+m) = 1` for `k + n = ℓ`, `1 ≤ k`, where `n = k' - 1`. So the law at
`s = -1`, `j = k'-1` gives `u = 1`. -/
theorem bol_product (n k : ℕ) (hk : k + n = ℓ) (hk1 : 1 ≤ k) :
    ∏ m ∈ Finset.range n, ((-1 - (m : ZMod ℓ)) / ((k : ZMod ℓ) + m)) = 1 := by
  rw [Finset.prod_div_distrib, ← prod_k_add n k hk]
  exact div_self (Finset.prod_ne_zero_iff.mpr fun m hm =>
    k_add_ne_zero n k m hk hk1 (Finset.mem_range.mp hm))

/-- **The chain product**: `∏_{i=1}^{n-1} -(i+1)/(k+i) = -k` for `k + n = ℓ`, `1 ≤ k`, `1 ≤ n`, where `n = k' - 1`. -/
theorem chain_product (n k : ℕ) (hk : k + n = ℓ) (hk1 : 1 ≤ k) (hn : 1 ≤ n) :
    ∏ i ∈ Finset.range (n - 1), ((-((i : ZMod ℓ) + 2)) / ((k : ZMod ℓ) + (i + 1))) = -(k : ZMod ℓ) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hk0 : (k : ZMod ℓ) ≠ 0 := by simpa using k_add_ne_zero (d + 1) k 0 hk hk1 (by omega)
  have hb := bol_product (d + 1) k hk hk1
  rw [Finset.prod_range_succ'] at hb
  have hP : ∏ i ∈ Finset.range d, ((-1 - ((i + 1 : ℕ) : ZMod ℓ)) / ((k : ZMod ℓ) + ((i + 1 : ℕ) : ZMod ℓ))) =
      ∏ i ∈ Finset.range d, ((-((i : ZMod ℓ) + 2)) / ((k : ZMod ℓ) + (i + 1))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    congr 1
    ring
  rw [hP] at hb
  simp only [Nat.cast_zero, add_zero, sub_zero] at hb
  set Q := ∏ i ∈ Finset.range d, ((-((i : ZMod ℓ) + 2)) / ((k : ZMod ℓ) + (i + 1)))
  have hQ : Q = Q * (-1 / (k : ZMod ℓ)) * (-(k : ZMod ℓ)) := by
    field_simp
  rw [hQ, hb, one_mul]

end Products

end

end RamanujanTau.BLBound
