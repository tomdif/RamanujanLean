/-
# Local coefficients of `L(Δ,s)^{−1/2}`

For a real parameter `l` (later `l = λ(p) = τ(p)p^{−11/2}`) the local factor of `L(Δ,s)^{−1/2}`
at `p` is `(1 − lZ + Z²)^{1/2}`, `Z = p^{−s}` (analytic normalization).  Writing
`1 − lZ + Z² = (1 − aZ)(1 − bZ)` with `a + b = l`, `ab = 1` (Satake parameters),

    (1 − lZ + Z²)^{1/2} = (1 − aZ)^{1/2} (1 − bZ)^{1/2},
    (1 − X)^{1/2} = 1 − 2 Σ_{n≥0} C_n (X/4)^{n+1}           (`C_n` = Catalan numbers).

We build the square root in `ℂ⟦X⟧` from Mathlib's Catalan series, prove that the result does not
depend on the choice of `(a,b)` (square roots with constant term `1` are unique in the domain
`ℂ⟦X⟧`) and has real coefficients, and define `alphaLoc l k ∈ ℝ` as its `k`-th coefficient.

* `alphaLoc_sq_sum`: `Σ_{i+j=k} alphaLoc l i · alphaLoc l j = [1, −l, 1, 0, 0, …]_k`;
* `abs_alphaLoc_le_pow`: for any Satake pair with `‖a‖, ‖b‖ ≤ R`, `|alphaLoc l k| ≤ R^k`
  (majorant `(2 − √(1−X))²`, whose coefficients are `1, 1, 8C_{k−1}/4^k ≤ 1`);
* `abs_alphaLoc_le_one`: if `l² ≤ 4` (Deligne), `|alphaLoc l k| ≤ 1` for **all** `k`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs

open PowerSeries Finset

noncomputable section

/-- The Catalan series over `ℂ`. -/
def catC : ℂ⟦X⟧ := map (Nat.castRingHom ℂ) catalanSeries

/-- `√(1 − 4X) = 1 − 2X·C(X)`. -/
def S4 : ℂ⟦X⟧ := 1 - 2 * X * catC

lemma catC_eq : catC ^ 2 * X + 1 = catC := by
  have h := congrArg (map (Nat.castRingHom ℂ)) catalanSeries_sq_mul_X_add_one
  simpa only [map_add, map_mul, map_pow, map_X, map_one] using h

lemma S4_sq : S4 ^ 2 = 1 - 4 * X := by
  have h := catC_eq
  unfold S4
  linear_combination (4 * X) * h

lemma coeff_catC (n : ℕ) : coeff n catC = (catalan n : ℂ) := by
  simp [catC, catalanSeries_coeff]

lemma coeff_S4_zero : coeff 0 S4 = 1 := by
  simp [S4]

lemma coeff_S4_succ (n : ℕ) : coeff (n + 1) S4 = -2 * (catalan n : ℂ) := by
  have : (2 : ℂ⟦X⟧) * X * catC = X * (C (2 : ℂ) * catC) := by
    rw [map_ofNat]; ring
  rw [S4, map_sub, this, coeff_succ_X_mul, coeff_C_mul, coeff_catC, coeff_one]
  simp

/-- `(1 − aX)^{1/2} = S4(aX/4)`. -/
def Sq (a : ℂ) : ℂ⟦X⟧ := rescale (a / 4) S4

lemma Sq_sq (a : ℂ) : Sq a ^ 2 = 1 - C a * X := by
  rw [Sq, ← map_pow, S4_sq, map_sub, map_one, map_mul, rescale_X, map_ofNat]
  have : (4 : ℂ⟦X⟧) * (C (a / 4) * X) = C (4 * (a / 4)) * X := by
    rw [map_mul, map_ofNat]; ring
  rw [this]; congr 3; ring

lemma constantCoeff_Sq (a : ℂ) : constantCoeff (Sq a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Sq, coeff_rescale, pow_zero, one_mul, coeff_S4_zero]

/-- `(1 − aX)^{1/2}(1 − bX)^{1/2}`. -/
def E (a b : ℂ) : ℂ⟦X⟧ := Sq a * Sq b

/-- `1 − lX + X²`. -/
def G (l : ℂ) : ℂ⟦X⟧ := 1 - C l * X + X ^ 2

lemma E_sq {a b : ℂ} {l : ℂ} (hs : a + b = l) (hp : a * b = 1) : E a b ^ 2 = G l := by
  rw [E, mul_pow, Sq_sq, Sq_sq, G, ← hs]
  have h1 : (C (a * b) : ℂ⟦X⟧) = 1 := by rw [hp, map_one]
  have h2 : (C (a * b) : ℂ⟦X⟧) = C a * C b := map_mul _ _ _
  rw [map_add]
  linear_combination (-(X ^ 2) : ℂ⟦X⟧) * h1.symm.trans h2

lemma constantCoeff_E (a b : ℂ) : constantCoeff (E a b) = 1 := by
  rw [E, map_mul, constantCoeff_Sq, constantCoeff_Sq, mul_one]

/-- Uniqueness of square roots with constant term `1` in `ℂ⟦X⟧`. -/
lemma sqrt_unique {F H : ℂ⟦X⟧} (h : F ^ 2 = H ^ 2) (hF : constantCoeff F = 1)
    (hH : constantCoeff H = 1) : F = H := by
  have h0 : (F - H) * (F + H) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have := congrArg constantCoeff h1
    rw [map_add, hF, hH, map_zero] at this
    norm_num at this

lemma E_indep {a b a' b' : ℂ} {l : ℂ} (hs : a + b = l) (hp : a * b = 1) (hs' : a' + b' = l)
    (hp' : a' * b' = 1) : E a b = E a' b' :=
  sqrt_unique ((E_sq hs hp).trans (E_sq hs' hp').symm) (constantCoeff_E a b) (constantCoeff_E a' b')

/-- Satake parameters exist for every real `l` (complex roots of `X² − lX + 1`). -/
lemma exists_satake (l : ℝ) : ∃ a b : ℂ, a + b = l ∧ a * b = 1 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((l : ℂ) ^ 2 - 4) (n := 2) (by norm_num)
  exact ⟨(l + d) / 2, (l - d) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hd⟩

/-- A chosen Satake pair. -/
def rA (l : ℝ) : ℂ := (exists_satake l).choose
def rB (l : ℝ) : ℂ := (exists_satake l).choose_spec.choose
lemma rAB_sum (l : ℝ) : rA l + rB l = l := (exists_satake l).choose_spec.choose_spec.1
lemma rAB_prod (l : ℝ) : rA l * rB l = 1 := (exists_satake l).choose_spec.choose_spec.2

/-- The local square root series `(1 − lX + X²)^{1/2}` (complex coefficients a priori). -/
def EL (l : ℝ) : ℂ⟦X⟧ := E (rA l) (rB l)

lemma EL_eq {l : ℝ} {a b : ℂ} (hs : a + b = l) (hp : a * b = 1) : EL l = E a b :=
  E_indep (rAB_sum l) (rAB_prod l) hs hp

lemma EL_sq (l : ℝ) : EL l ^ 2 = G l := E_sq (rAB_sum l) (rAB_prod l)

lemma map_conj_G (l : ℝ) : map (starRingEnd ℂ) (G l) = G l := by
  simp [G, map_sub, map_add, map_one, map_mul, map_C, map_X, map_pow, Complex.conj_ofReal]

/-- The coefficients of `EL l` are real. -/
lemma coeff_EL_conj (l : ℝ) (k : ℕ) : (starRingEnd ℂ) (coeff k (EL l)) = coeff k (EL l) := by
  have h : map (starRingEnd ℂ) (EL l) = EL l := by
    refine sqrt_unique ?_ ?_ ?_
    · rw [← map_pow, EL_sq, map_conj_G]
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, EL,
        constantCoeff_E, map_one]
    · rw [EL, constantCoeff_E]
  have := congrArg (coeff k) h
  rwa [coeff_map] at this

/-- **Local coefficients of `L^{−1/2}`**: `α_p(p^k) = alphaLoc (λ(p)) k`. -/
def alphaLoc (l : ℝ) (k : ℕ) : ℝ := (coeff k (EL l)).re

lemma ofReal_alphaLoc (l : ℝ) (k : ℕ) : ((alphaLoc l k : ℝ) : ℂ) = coeff k (EL l) :=
  Complex.conj_eq_iff_re.mp (coeff_EL_conj l k)

lemma alphaLoc_eq_coeff {l : ℝ} {a b : ℂ} (hs : a + b = l) (hp : a * b = 1) (k : ℕ) :
    ((alphaLoc l k : ℝ) : ℂ) = coeff k (E a b) := by
  rw [ofReal_alphaLoc, EL_eq hs hp]

/-- The coefficients of `1 − lX + X²`. -/
def Gc (l : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else if k = 1 then -l else if k = 2 then 1 else 0

lemma coeff_G (l : ℝ) (k : ℕ) : coeff k (G l) = (Gc l k : ℂ) := by
  rcases k with _ | _ | _ | k
  · simp [G, Gc]
  · simp [G, Gc, coeff_X_pow]
  · simp [G, Gc]
  · simp [G, Gc, coeff_X_pow]

/-- **The local square identity** `(Σ α_k X^k)² = 1 − lX + X²`. -/
theorem alphaLoc_sq_sum (l : ℝ) (k : ℕ) :
    ∑ q ∈ antidiagonal k, alphaLoc l q.1 * alphaLoc l q.2 = Gc l k := by
  have h := congrArg (coeff k) (EL_sq l)
  rw [sq, coeff_mul, coeff_G] at h
  apply Complex.ofReal_injective
  rw [← h]; push_cast
  exact Finset.sum_congr rfl fun q _ => by rw [ofReal_alphaLoc, ofReal_alphaLoc]

lemma alphaLoc_zero (l : ℝ) : alphaLoc l 0 = 1 := by
  have h := ofReal_alphaLoc l 0
  rw [coeff_zero_eq_constantCoeff_apply, EL, constantCoeff_E] at h
  exact_mod_cast h

lemma alphaLoc_one (l : ℝ) : alphaLoc l 1 = -l / 2 := by
  have h := alphaLoc_sq_sum l 1
  simp [Gc, Finset.Nat.antidiagonal_succ, alphaLoc_zero] at h
  linarith

lemma alphaLoc_two (l : ℝ) : alphaLoc l 2 = 1 / 2 - l ^ 2 / 8 := by
  have h := alphaLoc_sq_sum l 2
  simp [Gc, Finset.Nat.antidiagonal_succ, alphaLoc_zero, alphaLoc_one] at h
  linarith

/-! ## The majorant `(2 − √(1−X))²` -/

/-- `|coeff_n S4|`: `t 0 = 1`, `t (n+1) = 2 C_n`. -/
def tS (n : ℕ) : ℝ := if n = 0 then 1 else 2 * catalan (n - 1)

lemma norm_coeff_S4 (n : ℕ) : ‖coeff n S4‖ = tS n := by
  rcases n with _ | n
  · simp [coeff_S4_zero, tS]
  · rw [coeff_S4_succ, norm_mul, norm_neg]; simp [tS]

lemma tS_nonneg (n : ℕ) : 0 ≤ tS n := by unfold tS; split_ifs <;> positivity

/-- The real Catalan series. -/
def catR : ℝ⟦X⟧ := map (Nat.castRingHom ℝ) catalanSeries

def TR : ℝ⟦X⟧ := 1 + 2 * X * catR

lemma coeff_TR (n : ℕ) : coeff n TR = tS n := by
  rcases n with _ | n
  · simp [TR, tS]
  · have : (2 : ℝ⟦X⟧) * X * catR = X * (C (2 : ℝ) * catR) := by rw [map_ofNat]; ring
    rw [TR, map_add, this, coeff_succ_X_mul, coeff_C_mul, coeff_one]
    simp [catR, catalanSeries_coeff, tS]

lemma TR_sq : TR ^ 2 = 1 - 4 * X + 8 * X * catR := by
  have h := congrArg (map (Nat.castRingHom ℝ)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  unfold TR
  rw [← catR] at h
  linear_combination (4 * X) * h

lemma two_catalan_le (n : ℕ) (hn : 1 ≤ n) : 2 * (catalan n : ℝ) ≤ 4 ^ n := by
  have h1 := succ_mul_catalan_eq_centralBinom n
  have h2 := Nat.centralBinom_le_four_pow n
  have h3 : (n + 1) * catalan n ≤ 4 ^ n := h1 ▸ h2
  have h4 : 2 * catalan n ≤ 4 ^ n :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) h3
  exact_mod_cast h4

/-- `Σ_{i+j=k} t_i t_j ≤ 4^k`. -/
lemma sum_tS_le (k : ℕ) : ∑ q ∈ antidiagonal k, tS q.1 * tS q.2 ≤ 4 ^ k := by
  have h := congrArg (coeff k) TR_sq
  rw [sq, coeff_mul] at h
  simp_rw [coeff_TR] at h
  rw [h]
  rcases k with _ | k
  · simp
  · have : (8 : ℝ⟦X⟧) * X * catR = X * (C (8 : ℝ) * catR) := by rw [map_ofNat]; ring
    rw [this, map_add, coeff_succ_X_mul, coeff_C_mul, map_sub, coeff_one]
    have h4 : (4 : ℝ⟦X⟧) * X = X * C (4 : ℝ) := by rw [map_ofNat]; ring
    rw [h4, coeff_succ_X_mul, coeff_C]
    simp only [catR, coeff_map, catalanSeries_coeff, Nat.coe_castRingHom]
    rcases k with _ | k
    · simp; norm_num
    · simp only [Nat.add_one_ne_zero, if_false, sub_zero]
      have := two_catalan_le (k + 1) (by omega)
      rw [pow_succ]
      nlinarith

/-- **Coefficient bound**: if the Satake parameters satisfy `‖a‖, ‖b‖ ≤ R`, then
`|α_p(p^k)| ≤ R^k`. -/
theorem abs_alphaLoc_le_pow {l : ℝ} {a b : ℂ} (hs : a + b = l) (hp : a * b = 1) {R : ℝ}
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (k : ℕ) : |alphaLoc l k| ≤ R ^ k := by
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have e := alphaLoc_eq_coeff hs hp k
  have : |alphaLoc l k| = ‖coeff k (E a b)‖ := by rw [← e, Complex.norm_real, Real.norm_eq_abs]
  rw [this, E, coeff_mul]
  calc ‖∑ q ∈ antidiagonal k, coeff q.1 (Sq a) * coeff q.2 (Sq b)‖
      ≤ ∑ q ∈ antidiagonal k, ‖coeff q.1 (Sq a) * coeff q.2 (Sq b)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ antidiagonal k, (R / 4) ^ k * (tS q.1 * tS q.2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [mem_antidiagonal] at hq
        rw [Sq, Sq, coeff_rescale, coeff_rescale, norm_mul, norm_mul, norm_mul, norm_pow,
          norm_pow, norm_coeff_S4, norm_coeff_S4, norm_div, norm_div]
        have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
        rw [h4, ← hq, pow_add]
        have t1 := tS_nonneg q.1
        have t2 := tS_nonneg q.2
        have e1 : (‖a‖ / 4) ^ q.1 ≤ (R / 4) ^ q.1 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have e2 : (‖b‖ / 4) ^ q.2 ≤ (R / 4) ^ q.2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        calc (‖a‖ / 4) ^ q.1 * tS q.1 * ((‖b‖ / 4) ^ q.2 * tS q.2)
            = ((‖a‖ / 4) ^ q.1 * (‖b‖ / 4) ^ q.2) * (tS q.1 * tS q.2) := by ring
          _ ≤ ((R / 4) ^ q.1 * (R / 4) ^ q.2) * (tS q.1 * tS q.2) := by
              gcongr
          _ = _ := by ring
    _ = (R / 4) ^ k * ∑ q ∈ antidiagonal k, tS q.1 * tS q.2 := by rw [Finset.mul_sum]
    _ ≤ (R / 4) ^ k * 4 ^ k := by gcongr; exact sum_tS_le k
    _ = R ^ k := by rw [← mul_pow]; ring_nf

/-- **Deligne range**: if `l² ≤ 4` then `|α_p(p^k)| ≤ 1` for every `k`. -/
theorem abs_alphaLoc_le_one {l : ℝ} (hl : l ^ 2 ≤ 4) (k : ℕ) : |alphaLoc l k| ≤ 1 := by
  set s := Real.sqrt (1 - l ^ 2 / 4)
  have hs2 : s ^ 2 = 1 - l ^ 2 / 4 := Real.sq_sqrt (by linarith)
  set a : ℂ := ⟨l / 2, s⟩
  set b : ℂ := ⟨l / 2, -s⟩
  have hsum : a + b = l := by apply Complex.ext <;> simp [a, b]
  have hprod : a * b = 1 := by
    apply Complex.ext <;> simp [a, b]
    · nlinarith
    · ring
  have hn : ∀ z : ℂ, z.re = l / 2 → z.im ^ 2 = s ^ 2 → ‖z‖ = 1 := by
    intro z hr hi
    rw [Complex.norm_def, Complex.normSq_apply, hr, ← sq, ← sq, hi, hs2]
    norm_num; ring_nf
  have ha : ‖a‖ ≤ 1 := (hn a rfl rfl).le
  have hb : ‖b‖ ≤ 1 := (hn b rfl (by simp [b])).le
  simpa using abs_alphaLoc_le_pow hsum hprod ha hb k

end

end RamanujanTau.SelbergCoeffs
