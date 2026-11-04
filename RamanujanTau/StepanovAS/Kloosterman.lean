/-
# Stepanov's method for the Kloosterman curve `y^p - y = x + b/x`

`L` a finite field with `[L : F_p] = r = s + t`, `q = p^r`, `β = b ∈ F_p ⊆ L`, `γ = c ∈ F_p`.
`S_c = {x ∈ L^× : Tr(x + β/x) = c}`.

* `Y = expand (p^s) Y₀`, `Y(x) = ∑_{i<t} (x^{q + p^{s+i}} + β x^{q - p^{s+i}})`, a polynomial in
  `X^{p^s}` of degree `q + q/p`;
* `Z = γ X^{e+1} - ∑_{i<s} (X^{e+1+p^i} + β X^{e+1-p^i})`, `e = p^{s-1}`, degree `≤ 2e+1`;
* on `S_c`: `Y(x) x^e = Z(x)` (split the trace `∑_{i<r}` into `i < s` and `s ≤ i < r`).

Stepanov (`stepanov_hasse_card_le`) with `P = p`, `A = q/p`, `M = p^s`, `J = p^{s-1} + 2p` gives
`|S_c| ≤ q/p + 3p·p^t` (`card_traceFiber_le`), for `1 ≤ s ≤ t`, `3 ≤ t`.
-/
import RamanujanTau.StepanovAS.Aux

set_option autoImplicit false

namespace RamanujanTau.StepanovAS

open Polynomial Finset
open scoped Classical

variable (p : ℕ) [hp : Fact p.Prime]
variable (L : Type*) [Field L] [Fintype L] [Algebra (ZMod p) L]

/-- the high part of the trace, as a polynomial in `X^{p^s}` (before expansion). -/
noncomputable def Y0 (β : L) (t : ℕ) : L[X] :=
  ∑ i ∈ range t, X ^ (p ^ t + p ^ i) + ∑ i ∈ range t, C β * X ^ (p ^ t - p ^ i)

/-- `Z(x) = x^{e+1}(γ - A(x))`, `A` the low part of the trace. -/
noncomputable def Zpoly (β γ : L) (s : ℕ) : L[X] :=
  C γ * X ^ (p ^ (s - 1) + 1) -
    (∑ i ∈ range s, X ^ (p ^ (s - 1) + 1 + p ^ i) +
      ∑ i ∈ range s, C β * X ^ (p ^ (s - 1) + 1 - p ^ i))

/-- the trace fibre `S_c`. -/
noncomputable def traceFiber (b c : ZMod p) : Finset L :=
  (Finset.univ.filter fun x : L =>
    x ≠ 0 ∧ Algebra.trace (ZMod p) L (x + algebraMap (ZMod p) L b * x⁻¹) = c)

omit [Fintype L] [Algebra (ZMod p) L] in
theorem pow_sub_eq_mul_inv_pow {x : L} (hx : x ≠ 0) {n m : ℕ} (h : m ≤ n) :
    x ^ (n - m) = x ^ n * x⁻¹ ^ m := by
  rw [pow_sub₀ x hx h, inv_pow]

theorem charP_L : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p

/-- `Tr(z) = ∑_{i<r} z^{p^i}` in `L`. -/
theorem algebraMap_trace_eq (z : L) :
    algebraMap (ZMod p) L (Algebra.trace (ZMod p) L z) =
      ∑ i ∈ range (Module.finrank (ZMod p) L), z ^ (p ^ i) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod]

theorem frob_term (b : ZMod p) (x : L) (i : ℕ) :
    (x + algebraMap (ZMod p) L b * x⁻¹) ^ (p ^ i) =
      x ^ (p ^ i) + algebraMap (ZMod p) L b * x⁻¹ ^ (p ^ i) := by
  haveI := charP_L p L
  rw [add_pow_char_pow, mul_pow, ← map_pow, ZMod.pow_card_pow]

/-- **The key identity on the trace fibre**: `Y(x) x^e = Z(x)`. -/
theorem eval_Y_mul_eq_Z {s t : ℕ} (hs : 1 ≤ s) (hr : Module.finrank (ZMod p) L = s + t)
    (b c : ZMod p) {x : L} (hx : x ∈ traceFiber p L b c) :
    (expand L (p ^ s) (Y0 p L (algebraMap (ZMod p) L b) t)).eval x * x ^ (p ^ (s - 1)) =
      (Zpoly p L (algebraMap (ZMod p) L b) (algebraMap (ZMod p) L c) s).eval x := by
  set β := algebraMap (ZMod p) L b
  set γ := algebraMap (ZMod p) L c
  set e := p ^ (s - 1)
  obtain ⟨hx0, htr⟩ := (Finset.mem_filter.mp hx).2
  have hq : Fintype.card L = p ^ (s + t) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hr]
  have hxq : x ^ (p ^ (s + t)) = x := by rw [← hq]; exact FiniteField.pow_card x
  have hpos := hp.out.pos
  -- the trace relation
  have htr' : ∑ i ∈ range (s + t), (x ^ (p ^ i) + β * x⁻¹ ^ (p ^ i)) = γ := by
    rw [← hr]
    have := congrArg (algebraMap (ZMod p) L) htr
    rw [algebraMap_trace_eq] at this
    refine Eq.trans ?_ this
    exact Finset.sum_congr rfl fun i _ => (frob_term p L b x i).symm
  rw [Finset.sum_range_add] at htr'
  -- evaluate `Y`
  have hY : (expand L (p ^ s) (Y0 p L β t)).eval x =
      x * ∑ i ∈ range t, (x ^ (p ^ (s + i)) + β * x⁻¹ ^ (p ^ (s + i))) := by
    simp only [Y0, map_add, map_sum, map_mul, expand_C, map_pow, expand_X, eval_add,
      eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum, mul_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hit : p ^ i ≤ p ^ t := Nat.pow_le_pow_right hpos (by simp at hi; omega)
    have e1 : (x ^ p ^ s) ^ (p ^ t + p ^ i) = x * x ^ p ^ (s + i) := by
      rw [← pow_mul, mul_add, ← pow_add, ← pow_add, pow_add, hxq]
    have e2 : (x ^ p ^ s) ^ (p ^ t - p ^ i) = x * x⁻¹ ^ p ^ (s + i) := by
      rw [← pow_mul, Nat.mul_sub, ← pow_add, ← pow_add,
        pow_sub_eq_mul_inv_pow L hx0 (Nat.pow_le_pow_right hpos
          (show s + i ≤ s + t by simp at hi; omega)), hxq]
    rw [e1, e2]; ring
  -- the low part
  have hlow : ∀ i ∈ range s, x ^ (e + 1) * (x ^ (p ^ i) + β * x⁻¹ ^ (p ^ i)) =
      x ^ (e + 1 + p ^ i) + β * x ^ (e + 1 - p ^ i) := by
    intro i hi
    have hie : p ^ i ≤ e + 1 := by
      have := Nat.pow_le_pow_right hpos (show i ≤ s - 1 by simp at hi; omega); omega
    rw [pow_sub_eq_mul_inv_pow L hx0 hie, pow_add]; ring
  have hsum : ∑ i ∈ range t, (x ^ (p ^ (s + i)) + β * x⁻¹ ^ (p ^ (s + i))) =
      γ - ∑ i ∈ range s, (x ^ (p ^ i) + β * x⁻¹ ^ (p ^ i)) := by
    rw [← htr']; ring
  rw [hY, hsum]
  simp only [Zpoly, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
  have := Finset.sum_congr rfl hlow
  rw [Finset.sum_add_distrib] at this
  rw [← this, ← Finset.mul_sum, pow_succ]
  ring

/-! ### Degrees -/

omit [Fintype L] [Algebra (ZMod p) L] in
theorem natDegree_Y0 (β : L) {t : ℕ} (ht : 1 ≤ t) :
    (Y0 p L β t).natDegree = p ^ t + p ^ (t - 1) := by
  have hpos := hp.out.pos
  have h1 : p ^ (t - 1) < p ^ t := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have hY : Y0 p L β (t' + 1) = (∑ i ∈ range (t' + 1), C β * X ^ (p ^ (t' + 1) - p ^ i) +
      ∑ i ∈ range t', X ^ (p ^ (t' + 1) + p ^ i)) + X ^ (p ^ (t' + 1) + p ^ t') := by
    rw [Y0, Finset.sum_range_succ]; ring
  have hpt : 0 < p ^ t' := pow_pos hpos _
  rw [hY, natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_X_pow]
  refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p ^ (t' + 1)) ?_) (by omega)
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  · rcases Nat.eq_zero_or_pos t' with h0 | h0
    · subst h0; simp
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _
      (n := p ^ (t' + 1) + p ^ (t' - 1)) ?_) ?_
    · intro i hi
      rw [natDegree_X_pow]
      have := Nat.pow_le_pow_right hpos (show i ≤ t' - 1 by simp at hi; omega); omega
    · have := Nat.pow_lt_pow_right hp.out.one_lt (show t' - 1 < t' by omega); omega

omit [Fintype L] [Algebra (ZMod p) L] in
theorem natDegree_Zpoly_le (β γ : L) (s : ℕ) :
    (Zpoly p L β γ s).natDegree ≤ 2 * p ^ (s - 1) + 1 := by
  have hpos := hp.out.pos
  unfold Zpoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [natDegree_X_pow]
    have := Nat.pow_le_pow_right hpos (show i ≤ s - 1 by simp at hi; omega); omega
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)

/-! ### Parameters and the count -/

theorem arith_dim (p E B : ℕ) (hp : 2 ≤ p) (hE : 1 ≤ E) (hEB : p * E ≤ B) (hB : p ^ 3 ≤ B) :
    p * E * (E * B + (E + 2 * p) + (p - 1) * (2 * E + 1)) < (E + 2 * p) * p * (E * B) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have h4 : 4 * (m + 2) ≤ B := by
    have h2 : 4 ≤ (m + 2) ^ 2 := by nlinarith
    have : 4 * (m + 2) ≤ (m + 2) ^ 3 :=
      calc 4 * (m + 2) ≤ (m + 2) ^ 2 * (m + 2) := Nat.mul_le_mul_right _ h2
        _ = (m + 2) ^ 3 := by ring
    omega
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  have key : E * B + (E + 2 * (m + 2)) + (m + 1) * (2 * E + 1) < E * B + 2 * (m + 2) * B := by
    nlinarith
  have hpos : 0 < (m + 2) * E := by positivity
  calc (m + 2) * E * (E * B + (E + 2 * (m + 2)) + (m + 1) * (2 * E + 1))
      < (m + 2) * E * (E * B + 2 * (m + 2) * B) := Nat.mul_lt_mul_of_pos_left key hpos
    _ = (E + 2 * (m + 2)) * (m + 2) * (E * B) := by ring

theorem arith_card (p E B N : ℕ) (hp : 2 ≤ p) (hE : 1 ≤ E)
    (h : p * E * N ≤ E * B - 1 + p * E * B * (E + 2 * p - 1) + (p - 1) * (p * E * B * 1 + E * B)) :
    N ≤ E * B + 3 * p * B := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have h1 : E * B - 1 ≤ E * B := Nat.sub_le _ _
  have h2 : E + 2 * (m + 2) - 1 = E + 2 * m + 3 := by omega
  have h3 : m + 2 - 1 = m + 1 := by omega
  rw [h2, h3] at h
  have hpos : 0 < (m + 2) * E := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (m + 2) * E * N
      ≤ E * B + (m + 2) * E * B * (E + 2 * m + 3) + (m + 1) * ((m + 2) * E * B * 1 + E * B) := by
        omega
    _ ≤ (m + 2) * E * (E * B + 3 * (m + 2) * B) := by
        ring_nf; nlinarith [Nat.zero_le (E * B), Nat.zero_le (E * B * m)]

/-- **Stepanov's bound for the trace fibres** of `x + b/x`:
`#{x ∈ L^× : Tr(x + b/x) = c} ≤ q/p + 3p·p^t` for `[L:F_p] = s + t`, `1 ≤ s ≤ t`, `3 ≤ t`. -/
theorem card_traceFiber_le {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t)
    (hr : Module.finrank (ZMod p) L = s + t) (b c : ZMod p) :
    (traceFiber p L b c).card ≤ p ^ (s - 1) * p ^ t + 3 * p * p ^ t := by
  haveI := charP_L p L
  have hp2 := hp.out.two_le
  have hpos := hp.out.pos
  set E := p ^ (s - 1)
  set B := p ^ t
  have hE : 1 ≤ E := Nat.one_le_pow _ _ hpos
  have hps : p ^ s = p * E := by
    rw [show s = (s - 1) + 1 by omega, pow_succ, mul_comm]
  have hq : Fintype.card L = p * E * B := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hr, pow_add, hps]
  have hpB : p * p ^ (t - 1) = B := by
    rw [← pow_succ']; congr 1; omega
  set Y := expand L (p ^ s) (Y0 p L (algebraMap (ZMod p) L b) t)
  have hdeg : Y.natDegree = Fintype.card L * 1 + E * B := by
    simp only [Y]
    rw [natDegree_expand, natDegree_Y0 p L _ (by omega), hq, hps]
    have : (p ^ t + p ^ (t - 1)) * (p * E) = p * E * B + E * (p * p ^ (t - 1)) := by
      simp only [B]; ring
    rw [this, hpB]; ring
  have hY : Y ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg
    have : 0 < E * B := Nat.mul_pos (by omega) (pow_pos hpos _)
    omega
  have hQ : p ^ s ∣ Fintype.card L := by
    rw [hq, hps, mul_assoc]; exact Nat.mul_dvd_mul_left _ ⟨B, rfl⟩
  have hEB : p * E ≤ B := by
    rw [← hps]; exact Nat.pow_le_pow_right hpos hst
  have hB3 : p ^ 3 ≤ B := Nat.pow_le_pow_right hpos ht
  have h := stepanov_hasse_card_le p s hQ (Y0 p L (algebraMap (ZMod p) L b) t)
    (Zpoly p L (algebraMap (ZMod p) L b) (algebraMap (ZMod p) L c) s) hY
    (e := E) (W := 2 * E + 1) (J := E + 2 * p) (P := p) (A := E * B) (M := p ^ s)
    hdeg le_rfl (by
      rw [hq]
      have : (p - 1) * (E * B) + E * B = p * (E * B) := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [this, mul_assoc])
    (natDegree_Zpoly_le p L _ _ s) (by omega) (Nat.mul_pos (by omega) (pow_pos hpos _))
    le_rfl (by rw [hps]; exact arith_dim p E B hp2 hE hEB hB3)
    (traceFiber p L b c) (fun x hx => ⟨(Finset.mem_filter.mp hx).2.1,
      eval_Y_mul_eq_Z p L hs hr b c hx⟩)
  rw [hps, hq] at h
  exact arith_card p E B _ hp2 hE h

end RamanujanTau.StepanovAS
