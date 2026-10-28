import RamanujanTau.UBound.Final
import RamanujanTau.SharpHQ.Final

/-!
# UB without `GeomU`: the hypothesis and the arithmetic lemmas

**`QuotBound φ`** is the pointwise geometric input, in the style of `SharpHQ.ConjBound`. At every test
curve `W` of the break region `v(E(W)) < ℓ/(ℓ+1)` it supplies the `ℓ + 1` quotients `V C` in the Vélu
normalization `φ_C^*ω_C = ω` (`none` = the canonical subgroup `H`), with:

* **(algebraicity, Hecke)**: for every isobaric `P` of weight `k ≥ 1` and its classical image `PT`
  under `T_ℓ` (`ev PT = T_ℓ(ev P)`), `ℓ·PT(W) = Σ_C P(V C)`;
* **(integrality)**: `‖c₄(V C)‖³ ≤ ‖Δ(V C)‖`, `‖c₆(V C)‖² ≤ ‖Δ(V C)‖`;
* **(Lie valuations)**: `‖Δ(V H)‖·‖E(W)‖^{12} ≤ ‖ℓ‖^{12}`, `‖Δ(V C)‖^ℓ ≤ ‖E(W)‖^{12}` (`C ≠ H`);
* **(Hasse valuations)**: `‖E(V H)‖·‖E(W)‖^ℓ ≤ max(‖ℓ‖^{ℓ−1}‖E(W)‖^{ℓ+1}, ‖ℓ‖^ℓ)` and
  `‖E(V C)‖ ≤ ‖E(W)‖` (`C ≠ H`).

`UBSharp.Velu` derives it from `QuotEBound` (stated on `ConjAlg`'s objects `veluC C`, `C ∈ subs`),
and `UBSharp.HConj` derives `SharpHQ.HConj` from it.

The arithmetic lemmas:
* `dvd_of_radius_u`: one radius `‖s‖^{(ℓ+1)M} = ‖ℓ‖^{ℓM−1}` and `‖θ‖^ℓ = ‖s‖^j` turn the step-(K)
  bound `‖θ‖‖ℓ x‖ ≤ ‖s‖^m` into `ℓ^{u(min(m, M−1), j)} ∣ x`;
* `le_u`: `N ≤ u(2(N+j+1), j)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBSharp
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound HeckeQExp KatzForms Igusa

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

variable (ℓ) in
/-- **The pointwise quotient bound** (algebraicity of `T_ℓ` at test curves of the break region and
the valuations of the `ℓ+1` quotients, all in the Vélu normalization `φ_C^*ω_C = ω`). -/
def QuotBound {K : Type*} [NormedField K] [IsUltrametricDist K] (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
    ∃ V : Option (Fin ℓ) → WeierstrassCurve K,
      (∀ (k : ℕ) (P PT : Poly ℓ), 1 ≤ k → Iso P k → Iso PT k →
        ev ℤ_[ℓ] PT = Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P) →
        (ℓ : K) * MvPolynomial.eval (pt W) (MvPolynomial.map φ PT) =
          ∑ C, MvPolynomial.eval (pt (V C)) (MvPolynomial.map φ P)) ∧
      (∀ C, ‖(V C).c₄‖ ^ 3 ≤ ‖(V C).Δ‖ ∧ ‖(V C).c₆‖ ^ 2 ≤ ‖(V C).Δ‖) ∧
      ‖(V none).Δ‖ * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
      (∀ c : Fin ℓ, ‖(V (some c)).Δ‖ ^ ℓ ≤ ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12) ∧
      ‖MvPolynomial.eval (pt (V none)) (Eh φ hℓ)‖ * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ c : Fin ℓ, ‖MvPolynomial.eval (pt (V (some c))) (Eh φ hℓ)‖ ≤
        ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖)

/-! ### forms at a `Δ`-integral point -/

section Integral
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **An integral isobaric form of weight `w` at a point with `‖x₀‖³ ≤ D`, `‖x₁‖² ≤ D` has
`‖P(x)‖^{12} ≤ D^w`.** (At `x = (c₄, −c₆)` of a curve with `‖c₄‖³, ‖c₆‖² ≤ ‖Δ‖`: the model scaled by
`Δ^{1/12}` is integral.) -/
lemma norm_eval_pow_le {w : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P w)
    (hc : ∀ d, ‖P.coeff d‖ ≤ 1) {x : Fin 2 → K} {D : ℝ} (hD : 0 ≤ D) (h0 : ‖x 0‖ ^ 3 ≤ D)
    (h1 : ‖x 1‖ ^ 2 ≤ D) : ‖MvPolynomial.eval x P‖ ^ 12 ≤ D ^ w := by
  classical
  rw [MvPolynomial.eval_eq']
  rcases P.support.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, norm_zero, zero_pow (by norm_num)]; positivity
  obtain ⟨d, hd, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun d => P.coeff d * ∏ i, x i ^ d i)
  refine (pow_le_pow_left₀ (norm_nonneg _) hle 12).trans ?_
  have hw : 4 * d 0 + 6 * d 1 = w := by
    rw [← weight_wt]; exact hP (MvPolynomial.mem_support_iff.mp hd)
  rw [norm_mul, Fin.prod_univ_two, norm_mul, norm_pow, norm_pow, mul_pow, mul_pow, ← pow_mul,
    ← pow_mul, ← hw]
  calc ‖P.coeff d‖ ^ 12 * (‖x 0‖ ^ (d 0 * 12) * ‖x 1‖ ^ (d 1 * 12))
      ≤ 1 * ((‖x 0‖ ^ 3) ^ (4 * d 0) * (‖x 1‖ ^ 2) ^ (6 * d 1)) := by
        rw [← pow_mul, ← pow_mul, show 3 * (4 * d 0) = d 0 * 12 by ring,
          show 2 * (6 * d 1) = d 1 * 12 by ring]
        exact mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hc d)) (by positivity)
    _ ≤ 1 * (D ^ (4 * d 0) * D ^ (6 * d 1)) := by gcongr
    _ = D ^ (4 * d 0 + 6 * d 1) := by rw [one_mul, pow_add]

end Integral

/-! ### integer arithmetic -/

omit hℓp in
/-- the integer core of `dvd_of_radius_u`. -/
lemma int_core {M j m v : ℕ} (hM : 0 < M) (hl : 1 ≤ ℓ) (hm : m + 1 ≤ M)
    (h : (ℓ * M - 1) * (m * ℓ) ≤ (ℓ * M - 1) * j + (v + 1) * (ℓ * ((ℓ + 1) * M))) :
    ((ℓ : ℤ) * m) ≤ j + (v + 1) * (ℓ + 1) := by
  have h1 : 1 ≤ ℓ * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h' : ((ℓ * M - 1 : ℕ) : ℤ) * (m * ℓ) ≤ ((ℓ * M - 1 : ℕ) : ℤ) * j +
      (v + 1) * (ℓ * ((ℓ + 1) * M)) := by exact_mod_cast h
  rw [Nat.cast_sub h1] at h'
  push_cast at h'
  by_contra hc
  push Not at hc
  have hc' : ((j : ℤ) + (v + 1) * (ℓ + 1) + 1) * (ℓ * M) ≤ (ℓ * m) * (ℓ * M) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hmM : (m : ℤ) + 1 ≤ M := by exact_mod_cast hm
  have : (ℓ : ℤ) * m + ℓ ≤ ℓ * M := by nlinarith
  nlinarith

/-- `u(m', j) ≤ v` from `ℓm' ≤ j + (v+1)(ℓ+1)`. -/
lemma u_toNat_le {m j v : ℕ} (h : ((ℓ : ℤ) * m) ≤ j + (v + 1) * (ℓ + 1)) :
    (u ℓ m j).toNat ≤ v := by
  have hc : ⌈((ℓ : ℚ) * m - j) / (ℓ + 1)⌉ ≤ (v : ℤ) + 1 := by
    rw [Int.ceil_le, div_le_iff₀ (by positivity)]
    have : ((ℓ * m : ℤ) : ℚ) ≤ ((j + (v + 1) * (ℓ + 1) : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith
  unfold u
  omega

/-- **`N ≤ u(2(N+j+1), j)`.** -/
lemma le_u (N j : ℕ) : N ≤ (u ℓ (2 * (N + j + 1)) j).toNat := by
  have hl : (2 : ℚ) ≤ ℓ := by exact_mod_cast hℓp.out.two_le
  have hc : (N : ℤ) < ⌈((ℓ : ℚ) * (2 * (N + j + 1) : ℕ) - j) / (ℓ + 1)⌉ := by
    rw [Int.lt_ceil, lt_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  unfold u
  omega

/-! ### the radius lemma -/

section Radius
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **One radius suffices for `u`**: with `‖s‖^{(ℓ+1)M} = ‖ℓ‖^{ℓM−1}` and `‖θ‖^ℓ = ‖s‖^j`, the bound
`‖θ‖·‖φ(ℓx)‖ ≤ ‖s‖^m` gives `ℓ^{u(min(m, M−1), j)} ∣ x`. -/
lemma dvd_of_radius_u (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hpK : ‖(ℓ : K)‖ < 1) {s θ : K} {M j m : ℕ} (hM : 0 < M)
    (hs : ‖s‖ ^ ((ℓ + 1) * M) = ‖(ℓ : K)‖ ^ (ℓ * M - 1)) (hθ : ‖θ‖ ^ ℓ = ‖s‖ ^ j) (x : ℤ_[ℓ])
    (h : ‖θ‖ * ‖φ ((ℓ : ℤ_[ℓ]) * x)‖ ≤ ‖s‖ ^ m) :
    (ℓ : ℤ_[ℓ]) ^ (u ℓ (min m (M - 1)) j).toNat ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  set v := x.valuation with hv
  set t := ‖(ℓ : K)‖ with ht
  have hx' : ‖φ ((ℓ : ℤ_[ℓ]) * x)‖ = t ^ (v + 1) := by
    rw [map_mul, map_natCast, norm_mul, SharpHQ.norm_phi_eq φ hφ hx, pow_succ, mul_comm]
  rw [hx'] at h
  set e := ℓ * ((ℓ + 1) * M) with he
  have h2 := pow_le_pow_left₀ (by positivity) h e
  have hL : (‖θ‖ * t ^ (v + 1)) ^ e = t ^ ((ℓ * M - 1) * j + (v + 1) * e) := by
    rw [mul_pow, he, pow_mul ‖θ‖, hθ, ← pow_mul, mul_comm j, pow_mul, hs, ← pow_mul, ← pow_mul,
      pow_add]
  have hR : (‖s‖ ^ m) ^ e = t ^ ((ℓ * M - 1) * (m * ℓ)) := by
    rw [← pow_mul, he, show m * (ℓ * ((ℓ + 1) * M)) = (ℓ + 1) * M * (m * ℓ) by ring, pow_mul, hs,
      ← pow_mul]
  rw [hL, hR] at h2
  have h3 := (pow_le_pow_iff_right_of_lt_one₀ hε hpK).mp h2
  have hl : 1 ≤ ℓ := hℓp.out.one_lt.le
  have h4 : (ℓ * M - 1) * (min m (M - 1) * ℓ) ≤ (ℓ * M - 1) * j + (v + 1) * e :=
    le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (min_le_left _ _))) h3
  have hle := u_toNat_le (int_core hM hl (by omega) h4)
  conv_rhs => rw [PadicInt.unitCoeff_spec hx]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ hle) _

end Radius

end UBSharp
