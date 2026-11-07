/-
# Coefficientwise order on `ℤ⟦q⟧` and the distinct-odd-parts products

Toolkit for the elementary proof of the sign pattern of `f(q)` (`Andrews/Sign.lean`).

* `NN f`  : all coefficients of `f` are `≥ 0`;  `Dom f g` : `coeff k f ≤ coeff k g` for all `k`;
  `ADom f g` : `|coeff k f| ≤ coeff k g` for all `k`.  `ADom` is multiplicative (`ADom.mul`).
* `geo c a = Σ_j cʲ X^{aj} = 1/(1 − cX^a)`, hence `|[qᵏ] 1/(−q^a;q^b)_n| ≤ [qᵏ] 1/(q^a;q^b)_n` (`ADom_inv_NP`).
* Two shift inequalities for `(−q^a;q²)_K = ∏_{i<K}(1 + q^{a+2i})` (generating-function forms of
  "lower the smallest part by 2" and "raise the largest part by 2"):
  `NP_shift_low : (−q^{a+2};q²)_K − 1 ≤ q²((−q^a;q²)_{K+1} − 1)`,
  `NP_shift_high : q²((−q^a;q²)_K − 1) ≤ (−q^a;q²)_{K+1} − 1`.
-/
import RamanujanTau.MockTheta3Watson
import RamanujanTau.Watson.Euler

set_option autoImplicit false

namespace Andrews
open PowerSeries Finset Watson MockTheta3.Watson3

/-! ### coefficientwise order -/

/-- all coefficients nonnegative. -/
def NN (f : PowerSeries ℤ) : Prop := ∀ k, 0 ≤ coeff k f

/-- coefficientwise `f ≤ g`. -/
def Dom (f g : PowerSeries ℤ) : Prop := ∀ k, coeff k f ≤ coeff k g

/-- coefficientwise `|f| ≤ g`. -/
def ADom (f g : PowerSeries ℤ) : Prop := ∀ k, |coeff k f| ≤ coeff k g

lemma NN.mul {f g : PowerSeries ℤ} (hf : NN f) (hg : NN g) : NN (f * g) := fun k => by
  rw [coeff_mul]; exact sum_nonneg fun p _ => mul_nonneg (hf _) (hg _)

lemma NN.add {f g : PowerSeries ℤ} (hf : NN f) (hg : NN g) : NN (f + g) := fun k => by
  rw [map_add]; exact add_nonneg (hf k) (hg k)

lemma NN_one : NN 1 := fun k => by rw [coeff_one]; split_ifs <;> norm_num

lemma NN_X_pow (e : ℕ) : NN (X ^ e) := fun k => by rw [coeff_X_pow]; split_ifs <;> norm_num

lemma NN_zero : NN 0 := fun k => by simp

lemma NN.smul {f : PowerSeries ℤ} (hf : NN f) {c : ℕ} : NN ((c : PowerSeries ℤ) * f) := fun k => by
  rw [show ((c : PowerSeries ℤ)) = C (c : ℤ) by simp, coeff_C_mul]; exact mul_nonneg (by positivity) (hf k)

lemma Dom_iff {f g : PowerSeries ℤ} : Dom f g ↔ NN (g - f) := by
  constructor
  · intro h k; rw [map_sub]; linarith [h k]
  · intro h k; have := h k; rw [map_sub] at this; linarith

lemma Dom.refl (f : PowerSeries ℤ) : Dom f f := fun _ => le_rfl

lemma Dom.trans {f g h : PowerSeries ℤ} (h1 : Dom f g) (h2 : Dom g h) : Dom f h := fun k => (h1 k).trans (h2 k)

lemma Dom.add {f g f' g' : PowerSeries ℤ} (h : Dom f g) (h' : Dom f' g') : Dom (f + f') (g + g') := fun k => by
  rw [map_add, map_add]; exact add_le_add (h k) (h' k)

lemma Dom.mul_left {f g h : PowerSeries ℤ} (hh : NN h) (hfg : Dom f g) : Dom (h * f) (h * g) := by
  rw [Dom_iff] at *; rw [← mul_sub]; exact hh.mul hfg

lemma Dom_add_NN {f g : PowerSeries ℤ} (hg : NN g) : Dom f (f + g) := by
  rw [Dom_iff]; simpa using hg

lemma ADom.mul {f F g G : PowerSeries ℤ} (hf : ADom f F) (hg : ADom g G) : ADom (f * g) (F * G) := fun k => by
  rw [coeff_mul, coeff_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hf _) (hg _) (abs_nonneg _) ((abs_nonneg _).trans (hf _))

lemma ADom_X_pow (e : ℕ) : ADom (X ^ e) (X ^ e) := fun k => by
  rw [coeff_X_pow]; split_ifs <;> norm_num

lemma ADom_one : ADom 1 1 := fun k => by rw [coeff_one]; split_ifs <;> norm_num

/-! ### geometric series -/

lemma coeff_intCast_mul' (r : ℤ) (f : PowerSeries ℤ) (k : ℕ) :
    coeff k ((r : PowerSeries ℤ) * f) = r * coeff k f := by
  rw [show (r : PowerSeries ℤ) = C r by simp, coeff_C_mul]

/-- `Σ_j cʲ X^{aj}`. -/
noncomputable def geo (c : ℤ) (a : ℕ) : PowerSeries ℤ := mk fun k => if a ∣ k then c ^ (k / a) else 0

lemma one_sub_mul_geo (c : ℤ) {a : ℕ} (ha : 1 ≤ a) : (1 - (c : PowerSeries ℤ) * X ^ a) * geo c a = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_intCast_mul', coeff_X_pow_mul']
  simp only [geo, coeff_mk, coeff_one]
  by_cases hk : a ≤ k
  · rw [if_pos hk, if_neg (by omega : k ≠ 0)]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + a := ⟨k - a, by omega⟩
    rw [Nat.add_sub_cancel]
    have hd : a ∣ m + a ↔ a ∣ m := Nat.dvd_add_self_right
    by_cases h : a ∣ m
    · rw [if_pos (hd.mpr h), if_pos h, Nat.add_div_right _ (by omega), pow_succ]; ring
    · rw [if_neg (fun h' => h (hd.mp h')), if_neg h]; simp
  · rw [if_neg hk, mul_zero, sub_zero]
    by_cases h0 : k = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg]
      rintro ⟨j, rfl⟩
      rcases j with _ | j
      · simp at h0
      · exact hk (by nlinarith)

lemma inverse_eq_of_mul {u g : PowerSeries ℤ} (h : u * g = 1) : Ring.inverse u = g := by
  have hu : IsUnit u := IsUnit.of_mul_eq_one g h
  calc Ring.inverse u = Ring.inverse u * (u * g) := by rw [h, mul_one]
    _ = g := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

lemma inverse_one_sub (c : ℤ) {a : ℕ} (ha : 1 ≤ a) :
    Ring.inverse (1 - (c : PowerSeries ℤ) * X ^ a) = geo c a :=
  inverse_eq_of_mul (one_sub_mul_geo c ha)

lemma ADom_geo (a : ℕ) : ADom (geo (-1) a) (geo 1 a) := fun k => by
  simp only [geo, coeff_mk]; split_ifs <;> simp

/-- `|[qᵏ] 1/(−q^a;q^b)_n| ≤ [qᵏ] 1/(q^a;q^b)_n`. -/
lemma ADom_inv_NP {a : ℕ} (ha : 1 ≤ a) (b n : ℕ) :
    ADom (Ring.inverse (NP a b n)) (Ring.inverse (FP 1 a b n)) := by
  induction n with
  | zero => simp [NP, FP_zero]; exact ADom_one
  | succ n ih =>
    rw [NP, FP_succ, FP_succ, Ring.mul_inverse_rev, Ring.mul_inverse_rev,
      inverse_one_sub _ (by omega), inverse_one_sub _ (by omega)]
    exact (ADom_geo _).mul ih

/-! ### the products `(−q^a;q^b)_n` -/

lemma NP_eq_succ (a b n : ℕ) : NP a b (n + 1) = NP a b n + X ^ (a + b * n) * NP a b n := by
  rw [NP_succ]; ring

lemma NN_NP (a b n : ℕ) : NN (NP a b n) := by
  induction n with
  | zero => simp [NP, FP_zero]; exact NN_one
  | succ n ih => rw [NP_succ]; exact ih.mul (NN_one.add (NN_X_pow _))

lemma NN_NP_sub_one (a b n : ℕ) : NN (NP a b n - 1) := by
  induction n with
  | zero => simp [NP, FP_zero]; exact NN_zero
  | succ n ih =>
    rw [show NP a b (n + 1) - 1 = (NP a b n - 1) + X ^ (a + b * n) * NP a b n by rw [NP_eq_succ]; ring]
    exact ih.add ((NN_X_pow _).mul (NN_NP a b n))

lemma Dom_NP_succ (a b n : ℕ) : Dom (NP a b n) (NP a b (n + 1)) := by
  rw [NP_eq_succ]; exact Dom_add_NN ((NN_X_pow _).mul (NN_NP a b n))

/-- every factor is dominated by the product: `1 + q^{a+bi} ≤ (−q^a;q^b)_K` for `i < K`. -/
lemma Dom_factor_NP (a b : ℕ) {i K : ℕ} (hi : i < K) : Dom (1 + X ^ (a + b * i)) (NP a b K) := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact (ih h).trans (Dom_NP_succ a b K)
    · subst h
      rw [Dom_iff, NP_succ, show NP a b i * (1 + X ^ (a + b * i)) - (1 + X ^ (a + b * i))
          = (NP a b i - 1) * (1 + X ^ (a + b * i)) by ring]
      exact (NN_NP_sub_one a b i).mul (NN_one.add (NN_X_pow _))

/-- "lower the smallest part by 2": `(−q^{a+2};q²)_K − 1 ≤ q²((−q^a;q²)_{K+1} − 1)`. -/
lemma NP_shift_low : ∀ (K a : ℕ), Dom (NP (a + 2) 2 K - 1) (X ^ 2 * (NP a 2 (K + 1) - 1)) := by
  intro K
  induction K with
  | zero =>
    intro a
    rw [Dom_iff]
    simp only [NP, FP_zero, sub_self, sub_zero, zero_add, FP_succ, one_mul]
    rw [show (1 - ((-1 : ℤ) : PowerSeries ℤ) * X ^ (a + 2 * 0) - 1) = X ^ a by simp]
    exact (NN_X_pow 2).mul (NN_X_pow a)
  | succ K ih =>
    intro a
    have e1 : NP (a + 2) 2 (K + 1) - 1 = X ^ (a + 2) * NP (a + 4) 2 K + (NP (a + 4) 2 K - 1) := by
      rw [NP_shift]; ring
    have e2 : X ^ 2 * (NP a 2 (K + 1 + 1) - 1)
        = X ^ (a + 2) * NP (a + 2) 2 (K + 1) + X ^ 2 * (NP (a + 2) 2 (K + 1) - 1) := by
      rw [NP_shift a 2 (K + 1)]; ring
    rw [e1, e2]
    refine Dom.add ?_ (ih (a + 2))
    refine Dom.mul_left (NN_X_pow _) ?_
    rw [NP_shift]
    have : NP (a + 4) 2 K = NP (a + 2 + 2) 2 K := by ring_nf
    rw [← this, show (1 + X ^ (a + 2)) * NP (a + 4) 2 K = NP (a + 4) 2 K + X ^ (a + 2) * NP (a + 4) 2 K by ring]
    exact Dom_add_NN ((NN_X_pow _).mul (NN_NP _ _ _))

/-- "raise the largest part by 2": `q²((−q^a;q²)_K − 1) ≤ (−q^a;q²)_{K+1} − 1`. -/
lemma NP_shift_high (a : ℕ) : ∀ K : ℕ, Dom (X ^ 2 * (NP a 2 K - 1)) (NP a 2 (K + 1) - 1) := by
  intro K
  induction K with
  | zero =>
    rw [Dom_iff]
    simp only [NP, FP_zero, sub_self, mul_zero, sub_zero, FP_succ, one_mul]
    convert NN_X_pow a using 1; simp
  | succ K ih =>
    have e1 : X ^ 2 * (NP a 2 (K + 1) - 1) = X ^ 2 * (NP a 2 K - 1) + X ^ (a + 2 * K + 2) * NP a 2 K := by
      rw [NP_eq_succ]; ring
    have e2 : NP a 2 (K + 1 + 1) - 1 = (NP a 2 (K + 1) - 1) + X ^ (a + 2 * (K + 1)) * NP a 2 (K + 1) := by
      rw [NP_eq_succ a 2 (K + 1)]; ring
    rw [e1, e2, show a + 2 * K + 2 = a + 2 * (K + 1) by ring]
    exact ih.add (Dom.mul_left (NN_X_pow _) (Dom_NP_succ a 2 K))

end Andrews
