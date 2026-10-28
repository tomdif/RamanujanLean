import RamanujanTau.SharpHQ.Hensel

/-!
# The pointwise coefficient bound from the valuations of the conjugates

At a test curve `W` the `ℓ+1` conjugates of the `Δ`-modular equation are

  `y_C = Δ(W/C, ω_C)`,  `φ_C^* ω_C = ω`,  `C` running over the order-`ℓ` subgroups,

so that `f_k(W) = e_k(y)` (algebraicity), and `‖y_C‖ = ‖λ_C‖^{12}` with `λ_C` the Lie scalar of
`φ_C : W → W/C` (good reduction of `W/C`). With `v = v(E(W)) < ℓ/(ℓ+1)` the Lie valuations are
`v(λ_H) = 1 − v` for the canonical subgroup `H` and `v(λ_C) = v/ℓ` for `C ≠ H` (dually: `π̌` has
valuations `v` and `1 − v/ℓ`). On the Tate curve (`v = 0`) these are the conjugates
`ys (Pdisc) 12 ζ`: `ℓ^{12}Δ(q^ℓ)` for `H = μ_ℓ`, and `Δ(ζ^j q^{1/ℓ})`.

Only **upper bounds** on the norms are needed:

* **`ConjBound φ f`** (the explicit hypothesis `hConj`): for every test curve `W` with
  `‖ℓ‖^ℓ < ‖E(W)‖^{ℓ+1}` there are `y : Option (Fin ℓ) → K` (`none` = `H`) with
  * `f_k(W) = e_k(y)` for `k ≤ ℓ`;
  * `‖y_H‖·‖E(W)‖^{12} ≤ ‖ℓ‖^{12}`, i.e. `v(y_H) ≥ 12(1 − v)`;
  * `‖y_C‖^ℓ ≤ ‖E(W)‖^{12}` for `C ≠ H`, i.e. `v(y_C) ≥ 12v/ℓ`.

* **`coeffBound_of_conj`**: `ConjBound φ f → CoeffBound ℓ hℓ φ f`. This is the Newton-polygon bound
  `|e_k| ≤ max |∏_{C∈T} y_C|`: a `k`-subset without `H` has
  `v ≥ 12kv/ℓ ≥ 12(ℓ+1−k)v − 12(ℓ−k)`, and one containing `H` has
  `v ≥ 12(1−v) + 12(k−1)v/ℓ ≥ 12(ℓ+1−k)v − 12(ℓ−k)`. Both inequalities are equivalent to
  `v ≤ ℓ/(ℓ+1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SharpHQ
open ModP AtkinOBrienFinal AtkinOBrien DBound VLayer KatzForms Igusa

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

variable (ℓ) in
/-- **The conjugate bound `hConj`** (pointwise, on test curves of the break region). -/
def ConjBound (φ : ℤ_[ℓ] →+* K) (f : ℕ → Poly ℓ) : Prop :=
  ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
    ∃ y : Option (Fin ℓ) → K,
      (∀ k, k ≤ ℓ → MvPolynomial.eval (pt W) (MvPolynomial.map φ (f k)) =
        MvPolynomial.eval y (MvPolynomial.esymm (Option (Fin ℓ)) K k)) ∧
      ‖y none‖ * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
      ∀ j : Fin ℓ, ‖y (some j)‖ ^ ℓ ≤ ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12

omit hℓp in
/-- the real inequality behind the Newton bound. -/
lemma key_ineq {t e A : ℝ} (ht : 0 ≤ t) (he : 0 ≤ e) (hA0 : 0 ≤ A) (hl : ℓ ≠ 0)
    (hB : t ^ ℓ ≤ e ^ (ℓ + 1)) {j : ℕ} (hj : j ≤ ℓ) (hA : A ^ ℓ ≤ e ^ (12 * j)) :
    t ^ (12 * (ℓ - j)) * A ≤ e ^ (12 * (ℓ + 1 - j)) := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) hl).mp ?_
  obtain ⟨r, rfl⟩ : ∃ r, ℓ = j + r := ⟨ℓ - j, by omega⟩
  have e1 : j + r - j = r := by omega
  have e2 : j + r + 1 - j = r + 1 := by omega
  rw [e1, e2, mul_pow]
  calc (t ^ (12 * r)) ^ (j + r) * A ^ (j + r) = (t ^ (j + r)) ^ (12 * r) * A ^ (j + r) := by
        ring
    _ ≤ (e ^ (j + r + 1)) ^ (12 * r) * e ^ (12 * j) := by
        gcongr
    _ = (e ^ (12 * (r + 1))) ^ (j + r) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

lemma prod_somes_le (y : Option (Fin ℓ) → K) {e : ℝ}
    (hy : ∀ j : Fin ℓ, ‖y (some j)‖ ^ ℓ ≤ e ^ 12) (T : Finset (Option (Fin ℓ))) (hT : none ∉ T) :
    ‖∏ i ∈ T, y i‖ ^ ℓ ≤ e ^ (12 * T.card) := by
  rw [norm_prod, ← Finset.prod_pow, pow_mul, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
  cases i with
  | none => exact absurd hi hT
  | some j => exact hy j

/-- **The Newton bound**: `ConjBound → CoeffBound`. -/
theorem coeffBound_of_conj (φ : ℤ_[ℓ] →+* K) (hε : 0 < ‖(ℓ : K)‖) {f : ℕ → Poly ℓ}
    (hC : ConjBound ℓ hℓ φ f) : CoeffBound ℓ hℓ φ f := by
  classical
  intro W hW hBr k hk
  obtain ⟨y, hyf, hyH, hyC⟩ := hC W hW hBr
  set e := ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ with he
  set t := ‖(ℓ : K)‖ with ht
  have hl : ℓ ≠ 0 := hℓp.out.ne_zero
  have hBrk : t ^ ℓ ≤ e ^ (ℓ + 1) := hBr.le
  have he0 : 0 < e := by
    by_contra h
    push Not at h
    have h0 : e = 0 := le_antisymm h (norm_nonneg _)
    have := hBrk
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at this
    exact absurd (lt_of_lt_of_le (pow_pos hε ℓ) this) (lt_irrefl 0)
  rw [hyf k hk, MvPolynomial.esymm, map_sum, ← norm_pow, ← norm_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun T hT => ?_
  have hTc := (Finset.mem_powersetCard.mp hT).2
  rw [map_prod, norm_mul, norm_pow]
  simp only [MvPolynomial.eval_X]
  by_cases hn : none ∈ T
  · -- the canonical conjugate occurs
    have hk1 : 1 ≤ k := by
      rw [← hTc]; exact Finset.card_pos.mpr ⟨none, hn⟩
    rw [← Finset.mul_prod_erase T y hn, norm_mul]
    set A := ‖∏ i ∈ T.erase none, y i‖ with hA
    have hcard : (T.erase none).card = k - 1 := by rw [Finset.card_erase_of_mem hn, hTc]
    have hA' : A ^ ℓ ≤ e ^ (12 * (k - 1)) := by
      rw [hA, ← hcard]
      exact prod_somes_le y hyC _ (Finset.notMem_erase _ _)
    have h1 := key_ineq hε.le he0.le (norm_nonneg _) hl hBrk (by omega : k - 1 ≤ ℓ) hA'
    have e1 : ℓ - (k - 1) = (ℓ - k) + 1 := by omega
    have e2 : ℓ + 1 - (k - 1) = (ℓ + 1 - k) + 1 := by omega
    rw [e1, e2, mul_add, mul_add, mul_one, pow_add, pow_add] at h1
    have hyH0 : 0 ≤ ‖y none‖ := norm_nonneg _
    refine le_of_mul_le_mul_right ?_ (pow_pos he0 12)
    calc t ^ (12 * (ℓ - k)) * (‖y none‖ * A) * e ^ 12
        = t ^ (12 * (ℓ - k)) * A * (‖y none‖ * e ^ 12) := by ring
      _ ≤ t ^ (12 * (ℓ - k)) * A * t ^ 12 :=
          mul_le_mul_of_nonneg_left hyH (by positivity)
      _ = t ^ (12 * (ℓ - k)) * t ^ 12 * A := by ring
      _ ≤ e ^ (12 * (ℓ + 1 - k)) * e ^ 12 := h1
  · have hA' : ‖∏ i ∈ T, y i‖ ^ ℓ ≤ e ^ (12 * k) := by
      rw [← hTc]; exact prod_somes_le y hyC T hn
    exact key_ineq hε.le he0.le (norm_nonneg _) hl hBrk hk hA'

end SharpHQ
