/-
# Watson's `ψ` as an Appell–Lerch sum, and `f − b = −4ψ(−q)` on the disc

* `watson_disc2`: `f(q) + 4ψ(−q) = b(q)` for `|q| < 1` (`MockTheta3.Watson3.watson_W2` transferred by Taylor series),
  with `ψ(−q) + 1 = aA(q) = Σ_{n≥0} (−1)ⁿ q^{n²}/(−q;q²)_n`.
* `aA_rank`: with `Q = −q`, `(1 − Q)·(ψ(Q)+1) = R(Q;Q⁴)`: the terms `n = 2m, 2m+1` of `ψ` pair up to the `m`-th
  term of the rank generating function `R(z;Q⁴)` at `z = Q`.
* `aA_AL`: hence (`rank_disc` with `z = Q`, base `Q⁴`, and `Ad_bilateral`)
  `(Q⁴;Q⁴)_∞ (ψ(Q)+1) = Σ_{n∈ℤ} (−1)ⁿ Q^{6n²+2n}/(1 − Q^{4n+1})`.
-/
import RamanujanTau.MockCusp.Bilateral
import RamanujanTau.MockCusp.BAE

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set Finset Taylor
open scoped Topology Real

noncomputable section

local notation "ψC" => MockTheta5.JTP.ψC

/-! ### `f + 4ψ(−q) = b` on the disc -/

noncomputable def P3 (n : ℕ) : Polynomial ℤ := ∏ i ∈ range n, (1 + Polynomial.X ^ (1 + 2 * i))

/-- `aA(q) = Σ_{n≥0} (−1)ⁿ q^{n²}/(−q;q²)_n = ψ(−q) + 1`. -/
noncomputable def aA (z : ℂ) : ℂ :=
  ∑' n, (((-1) ^ n : ℤ) : ℂ) * z ^ (n ^ 2) * (((P3 n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ 1

lemma aA_eq (z : ℂ) : aA z = ∑' n, (-1) ^ n * z ^ (n ^ 2) / ∏ i ∈ range n, (1 + z ^ (1 + 2 * i)) := by
  simp [aA, P3, Polynomial.map_prod, Polynomial.eval_prod, div_eq_mul_inv]

theorem aA_T : Hol aA ∧ T aA = ψC (PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P3 n : Polynomial ℤ) : PowerSeries ℤ) ^ 1)) := by
  obtain ⟨h1, h2, h3⟩ := MockTheta3.Radial.hyps (fun i => 1 + 2 * i) (fun i => by dsimp only; omega)
  exact T_series (fun n => (-1) ^ n) 1 P3 h1 h2 h3 MockTheta3.Radial.sgn_le

lemma coe_P3 (n : ℕ) : ((P3 n : Polynomial ℤ) : PowerSeries ℤ) = MockTheta3.Watson3.NP 1 2 n := by
  rw [P3, MockTheta3.Radial.coe_prod_one_add (fun i => 1 + 2 * i)]
  simp [Watson.FP]

lemma A0_eq : MockTheta3.Watson3.A 0 = PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ range (m + 1),
    PowerSeries.C ((-1) ^ n : ℤ) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P3 n : Polynomial ℤ) : PowerSeries ℤ) ^ 1) := by
  rw [MockTheta3.Watson3.A, MockTheta3.Radial.osum_eq_mk fun n k hk => by
    rw [MockTheta3.Watson3.uA, mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc]
    exact MockTheta3.Watson3.coeff_Xpow_mul_zero (by nlinarith) _]
  congr 1; funext m; congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MockTheta3.Watson3.uA, coe_P3]; simp

/-- **Watson's second identity on the disc**: `f(q) + 4(aA(q) − 1) = b(q)`, i.e. `f(q) + 4ψ(−q) = b(q)`. -/
theorem watson_disc2 {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    MockTheta3.Radial.fA z + 4 * (aA z - 1) = MockTheta3.Radial.bA z := by
  have hf := MockTheta3.Radial.fA_T
  have ha := aA_T
  have hW := MockTheta3.Watson3.watson_W2
  have h4 : Hol (fun z => 4 * (aA z - 1)) := (differentiableOn_const _).mul (ha.1.sub (differentiableOn_const _))
  refine eq_of_T (f := fun z => MockTheta3.Radial.fA z + 4 * (aA z - 1)) (g := MockTheta3.Radial.bA)
    (hf.1.add h4) MockTheta3.Radial.bA_hol ?_ hz
  rw [T_add hf.1 h4, T_mul (f := fun _ => (4 : ℂ)) (g := fun z => aA z - 1) (differentiableOn_const _)
      (ha.1.sub (differentiableOn_const _)),
    T_sub (f := aA) (g := fun _ => (1 : ℂ)) ha.1 (differentiableOn_const _), T_const, T_const, hf.2, ha.2,
    MockTheta3.Radial.bA_T, ← MockTheta3.Radial.F1_eq, ← A0_eq, ← hW]
  simp [map_sub, map_mul, map_ofNat, map_add]

/-! ### pairing `ψ` into the rank generating function -/

/-- `Q^{n²}/(Q;Q²)_n`. -/
def ap (n : ℕ) (Q : ℂ) : ℂ := Q ^ (n ^ 2) / ∏ i ∈ range n, (1 - Q ^ (1 + 2 * i))

lemma aA_eq_ap (q : ℂ) : aA q = ∑' n, ap n (-q) := by
  rw [aA_eq]
  congr 1; funext n
  rw [ap]
  congr 1
  · have hsq : ((-1 : ℂ)) ^ (n ^ 2) = (-1) ^ n := by
      rcases Nat.even_or_odd n with h | h
      · rw [h.neg_one_pow, (Nat.even_pow.mpr ⟨h, by norm_num⟩).neg_one_pow]
      · rw [h.neg_one_pow, (h.pow).neg_one_pow]
    rw [neg_pow q (n ^ 2), hsq]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Odd.neg_pow ⟨i, by ring⟩]; ring

lemma summable_ap {q : ℂ} (hq : ‖q‖ < 1) : Summable fun n => ap n (-q) := by
  refine Summable.of_norm_bounded (summable_sq_mul_pow (norm_nonneg q) hq ((1 - ‖q‖)⁻¹)
    (by have : 0 < 1 - ‖q‖ := by linarith
        positivity)) fun n => ?_
  have hp := MockTheta3.Radial.prod_bound (norm_nonneg q) hq (fun i => 1 + 2 * i) (fun i => by dsimp only; omega) n le_rfl
  have he : ∏ i ∈ range n, (1 - (-q) ^ (1 + 2 * i)) = ∏ i ∈ range n, (1 + q ^ (1 + 2 * i)) :=
    Finset.prod_congr rfl fun i _ => by rw [Odd.neg_pow ⟨i, by ring⟩]; ring
  rw [ap, he, norm_div, norm_pow, norm_neg, div_eq_mul_inv, inv_pow]
  have hpos : 0 < (1 - ‖q‖) ^ n := pow_pos (by linarith) n
  gcongr

lemma tsum_pair {f : ℕ → ℂ} (hf : Summable f) : ∑' n, f n = ∑' k, (f (2 * k) + f (2 * k + 1)) := by
  have he : Summable fun k => f (2 * k) := hf.comp_injective fun a b h => by simpa using h
  have ho : Summable fun k => f (2 * k + 1) := hf.comp_injective fun a b h => by simpa using h
  rw [(he.hasSum.add ho.hasSum).tsum_eq, (he.hasSum.even_add_odd ho.hasSum).tsum_eq]

lemma pc_succ (c : ℂ) (n : ℕ) (Q : ℂ) : pc c (n + 1) Q = pc c n Q * (1 - c * Q ^ (1 + n)) := by
  rw [pc, Finset.prod_range_succ]; rfl

/-- `(Q;Q²)_{2m+1} = (1−Q)·(Q⁵;Q⁴)_m·(Q³;Q⁴)_m`. -/
lemma D_odd {Q : ℂ} (hQ : Q ≠ 0) (m : ℕ) :
    ∏ i ∈ range (2 * m + 1), (1 - Q ^ (1 + 2 * i)) = (1 - Q) * (pc Q m (Q ^ 4) * pc Q⁻¹ m (Q ^ 4)) := by
  induction m with
  | zero => simp [pc]
  | succ m ih =>
    have e1 : Q * (Q ^ 4) ^ (1 + m) = Q ^ (1 + 2 * (2 * m + 1 + 1)) := by ring
    have e2 : Q⁻¹ * (Q ^ 4) ^ (1 + m) = Q ^ (1 + 2 * (2 * m + 1)) := by
      field_simp; ring
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      pc_succ, pc_succ, e1, e2]; ring

lemma ap_pair {Q : ℂ} (hQ : Q ≠ 0) (hQ1 : ‖Q‖ < 1) (m : ℕ) :
    (1 - Q) * (ap (2 * m) Q + ap (2 * m + 1) Q) = rT Q m (Q ^ 4) := by
  have hne : ∀ k, ∏ i ∈ range k, (1 - Q ^ (1 + 2 * i)) ≠ 0 := fun k => by
    rw [Finset.prod_ne_zero_iff]; intro i _ h0
    have h1 : Q ^ (1 + 2 * i) = 1 := by linear_combination -h0
    have := congrArg norm h1
    rw [norm_pow, norm_one] at this
    exact absurd this (ne_of_lt (pow_lt_one₀ (norm_nonneg _) hQ1 (by omega)))
  have hD := D_odd hQ m
  have h2 : ∏ i ∈ range (2 * m + 1), (1 - Q ^ (1 + 2 * i)) =
      (∏ i ∈ range (2 * m), (1 - Q ^ (1 + 2 * i))) * (1 - Q ^ (4 * m + 1)) := by
    rw [Finset.prod_range_succ]; ring_nf
  have hQ1' : (1 : ℂ) - Q ≠ 0 := by
    intro h0; have : Q = 1 := by linear_combination -h0
    rw [this, norm_one] at hQ1; exact lt_irrefl _ hQ1
  have hpc : pc Q m (Q ^ 4) * pc Q⁻¹ m (Q ^ 4) ≠ 0 := by
    intro h0; apply hne (2 * m + 1); rw [hD, h0, mul_zero]
  have hA := hne (2 * m)
  have hB := hne (2 * m + 1)
  rw [h2] at hB
  have hB' : 1 - Q ^ (4 * m + 1) ≠ 0 := right_ne_zero_of_mul hB
  unfold ap rT
  rw [h2, show (2 * m + 1) ^ 2 = (2 * m) ^ 2 + (4 * m + 1) by ring, mul_assoc, ← mul_inv]
  rw [show (Q ^ 4) ^ (m ^ 2) = Q ^ ((2 * m) ^ 2) by rw [← pow_mul]; ring_nf]
  have hD' : pc Q m (Q ^ 4) * pc Q⁻¹ m (Q ^ 4) =
      (∏ i ∈ range (2 * m), (1 - Q ^ (1 + 2 * i))) * (1 - Q ^ (4 * m + 1)) / (1 - Q) := by
    rw [← h2, hD]; field_simp
  rw [hD']
  field_simp
  ring

/-- **`(1 − Q)(ψ(Q) + 1) = R(Q; Q⁴)`** with `Q = −q`. -/
theorem aA_rank {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) : (1 + q) * aA q = Rd (-q) ((-q) ^ 4) := by
  have hQ : -q ≠ 0 := neg_ne_zero.mpr hq0
  have hQ1 : ‖-q‖ < 1 := by rwa [norm_neg]
  rw [aA_eq_ap, tsum_pair (summable_ap hq), ← tsum_mul_left, Rd]
  congr 1; funext m
  rw [← ap_pair hQ hQ1 m]; ring

end

end MockCusp
