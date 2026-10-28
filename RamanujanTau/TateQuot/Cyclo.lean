/-
# Cyclotomic constants: `Σ_{k=1}^{p−1} θ^m(u/(1−u)²)|_{u=ζ^k}` for `m = 0, 2, 4`

With `y_k = 1/(1 − ζ^k)` (`1 ≤ k < p`), the power sums `PS j = Σ_k y_k^j` satisfy
`((1−T)^p − 1) · Σ_k 1/(1 − y_k T) = p(1−T)^{p−1} − p` (`gen_identity`), which determines `PS 1, …, PS 6`.
Hence (`kappa0`, `kappa2`, `kappa4`)
* `Σ_k ζ^k/(ζ^k−1)² = −(p²−1)/12`,
* `Σ_k cpoly 2 (ζ^k)/(ζ^k−1)⁴ = (p⁴−1)/120`,
* `Σ_k cpoly 4 (ζ^k)/(ζ^k−1)⁶ = −(p⁶−1)/252`.
-/
import RamanujanTau.TateQuot.Deriv

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries Finset

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}

lemma sum_range_pow_prim (hζ : IsPrimitiveRoot ζ p) (r : ℕ) :
    ∑ k ∈ range p, (ζ ^ k) ^ r = if p ∣ r then (p : K) else 0 := by
  have hs : ∑ k ∈ range p, (ζ ^ k) ^ r = ∑ k ∈ range p, (ζ ^ r) ^ k :=
    sum_congr rfl fun k _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hs]
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := hm
    have h1 : ζ ^ (p * n) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [h1]
  · have hcop : r.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
    exact (hζ.pow_of_coprime r hcop).geom_sum_eq_zero hp.out.one_lt

/-- `Σ_{k=1}^{p−1} ζ^{kr} = p[p ∣ r] − 1`. -/
lemma sum_Ico_pow_prim (hζ : IsPrimitiveRoot ζ p) (r : ℕ) :
    ∑ k ∈ Ico 1 p, (ζ ^ k) ^ r = (if p ∣ r then (p : K) else 0) - 1 := by
  rw [← sum_range_pow_prim hζ r, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp.out.pos]
  simp

lemma pow_ne_one_Ico (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ∈ Ico 1 p) : ζ ^ k ≠ 1 := by
  rw [mem_Ico] at hk
  exact hζ.pow_ne_one_of_pos_of_lt (by omega) hk.2

/-- `y_k = 1/(1 − ζ^k)`. -/
def yk (ζ : K) (k : ℕ) : K := (1 - ζ ^ k)⁻¹

/-- `PS j = Σ_{k=1}^{p−1} y_k^j`. -/
def PS (_hζ : IsPrimitiveRoot ζ p) (j : ℕ) : K := ∑ k ∈ Ico 1 p, yk ζ k ^ j

/-- `1/(1 − yT)`. -/
def Hser (y : K) : PowerSeries K := mk fun j => y ^ j

lemma one_sub_mul_Hser (y : K) : (1 - C y * X) * Hser y = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_one]
  rcases n with _ | n
  · simp [Hser]
  · rw [coeff_succ_X_mul]; simp [Hser, pow_succ]; ring

lemma per_k {w : K} (hw : w ≠ 1) (hwp : w ^ p = 1) :
    ((1 - X) ^ p - 1) * Hser (1 - w)⁻¹ =
      C (1 - w) * ∑ r ∈ range p, C (w ^ r) * (1 - X) ^ (p - 1 - r) := by
  have hg := geom_sum₂_mul (C w : PowerSeries K) (1 - X) p
  simp only [← map_pow, hwp, map_one] at hg
  have h1w : (1 - w) * (1 - w)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hw))
  have hH := one_sub_mul_Hser (1 - w)⁻¹
  have hC : C (1 - w) * C (1 - w)⁻¹ = (1 : PowerSeries K) := by rw [← map_mul, h1w, map_one]
  have hCs : C (1 - w) = 1 - C w := by simp
  set S := ∑ r ∈ range p, C (w ^ r) * (1 - X) ^ (p - 1 - r)
  linear_combination Hser (1 - w)⁻¹ * hg - Hser (1 - w)⁻¹ * S * hCs +
    Hser (1 - w)⁻¹ * S * X * hC + C (1 - w) * S * hH

lemma gen_identity (hζ : IsPrimitiveRoot ζ p) :
    ((1 - X) ^ p - 1) * ∑ k ∈ Ico 1 p, Hser (yk ζ k) = C (p : K) * (1 - X) ^ (p - 1) - C (p : K) := by
  rw [mul_sum]
  show ∑ i ∈ Ico 1 p, ((1 - X) ^ p - 1) * Hser (1 - ζ ^ i)⁻¹ = _
  rw [sum_congr rfl fun k hk => per_k (pow_ne_one_Ico hζ hk)
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])]
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm : ∀ r ∈ range p, ∑ k ∈ Ico 1 p, C (1 - ζ ^ k) * (C ((ζ ^ k) ^ r) * (1 - X) ^ (p - 1 - r))
      = (if r = 0 then C (p : K) * (1 - X) ^ (p - 1) else 0) - (if r = p - 1 then C (p : K) else 0) := by
    intro r hr
    rw [mem_range] at hr
    have e : ∑ k ∈ Ico 1 p, C (1 - ζ ^ k) * (C ((ζ ^ k) ^ r) * (1 - X) ^ (p - 1 - r)) =
        C (∑ k ∈ Ico 1 p, (ζ ^ k) ^ r - ∑ k ∈ Ico 1 p, (ζ ^ k) ^ (r + 1)) * (1 - X) ^ (p - 1 - r) := by
      rw [← sum_sub_distrib, map_sum, sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul]; congr 2; ring
    rw [e, sum_Ico_pow_prim hζ, sum_Ico_pow_prim hζ]
    have h1 : p ∣ r ↔ r = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero p⟩
    have h2 : p ∣ r + 1 ↔ r = p - 1 := by
      constructor
      · intro h; have := Nat.le_of_dvd (by omega) h; omega
      · intro h; rw [h, Nat.sub_add_cancel hp.out.pos]
    simp only [h1, h2]
    have h2le := hp.out.two_le
    by_cases ha : r = 0
    · have hb : r ≠ p - 1 := by omega
      simp only [if_pos ha, if_neg hb]
      rw [ha, Nat.sub_zero, show ((p : K) - 1 - (0 - 1)) = p by ring]; ring
    · by_cases hb : r = p - 1
      · simp only [if_neg ha, if_pos hb]
        rw [hb, Nat.sub_self, pow_zero, mul_one, show ((0 : K) - 1 - (p - 1)) = -p by ring, map_neg]
        ring
      · simp only [if_neg ha, if_neg hb]; simp
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  simp [hp.out.pos]

omit hp in
lemma coeff_one_sub_X_pow (n i : ℕ) :
    coeff i ((1 - X : PowerSeries K) ^ n) = (-1) ^ i * (n.choose i : K) := by
  induction n generalizing i with
  | zero => rcases i with _ | i <;> simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_sub, mul_one, map_sub, ih]
    rcases i with _ | i
    · simp
    · rw [coeff_succ_mul_X, ih, Nat.choose_succ_succ]; push_cast; ring

/-- The coefficient equations: `Σ_{i ≤ j} ((−1)^i C(p,i) − [i=0]) PS_{j−i} = p(−1)^j C(p−1,j) − p[j=0]`. -/
lemma eqn (hζ : IsPrimitiveRoot ζ p) (j : ℕ) :
    ∑ i ∈ range (j + 1), ((-1) ^ i * (p.choose i : K) - if i = 0 then 1 else 0) * PS hζ (j - i) =
      (p : K) * ((-1) ^ j * ((p - 1).choose j : K)) - if j = 0 then (p : K) else 0 := by
  have h := congrArg (coeff j) (gen_identity hζ)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a ((1 - X) ^ p - 1 : PowerSeries K) * coeff b (∑ k ∈ Ico 1 p, Hser (yk ζ k)))]
    at h
  rw [map_sub, coeff_C_mul, coeff_one_sub_X_pow, coeff_C] at h
  rw [← h]
  refine sum_congr rfl fun i _ => ?_
  rw [map_sub, coeff_one_sub_X_pow, coeff_one, map_sum]
  simp [PS, Hser, coeff_mk]

lemma choose_cast (a b : ℕ) : (a.choose b : K) = (descPochhammer K b).eval (a : K) / b.factorial :=
  Nat.cast_choose_eq_descPochhammer_div K a b

/-- **The power sums** `PS 1, …, PS 6` of `y_k = 1/(1−ζ^k)`. -/
theorem PS_values (hζ : IsPrimitiveRoot ζ p) :
    PS hζ 0 = (p:K) - 1 ∧ PS hζ 1 = (p:K)/2 - 1/2 ∧ PS hζ 2 = (5 - (p:K))*((p:K) - 1)/12 ∧
    PS hζ 3 = (3 - (p:K))*((p:K) - 1)/8 ∧
    PS hζ 4 = ((p:K) - 1)*((p:K)^3 + (p:K)^2 - 109*(p:K) + 251)/720 ∧
    PS hζ 5 = ((p:K) - 5)*((p:K) - 1)*((p:K)^2 + 6*(p:K) - 19)/288 ∧
    PS hζ 6 = (1 - (p:K))*(2*(p:K)^5 + 2*(p:K)^4 - 355*(p:K)^3 - 355*(p:K)^2 + 11153*(p:K) - 19087)/60480 := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : ((p - 1 : ℕ) : K) = (p : K) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have h0 : PS hζ 0 = (p:K) - 1 := by
    simp [PS, hp1]
  have e2 := eqn hζ 2
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e2
  norm_num at e2
  have e3 := eqn hζ 3
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e3
  norm_num at e3
  have e4 := eqn hζ 4
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e4
  norm_num at e4
  have e5 := eqn hζ 5
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e5
  norm_num at e5
  have e6 := eqn hζ 6
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e6
  norm_num at e6
  have e7 := eqn hζ 7
  simp only [sum_range_succ, sum_range_zero, choose_cast, descPochhammer_succ_eval,
    descPochhammer_zero, Polynomial.eval_one, hp1, Nat.factorial, Nat.succ_eq_add_one] at e7
  norm_num at e7
  have h1 : PS hζ 1 = (p:K)/2 - 1/2 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e2 + ((p:K)^2/2 - (p:K)/2) * h0
  have h2 : PS hζ 2 = (5 - (p:K))*((p:K) - 1)/12 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e3 + ((p:K)^2/2 - (p:K)/2) * h1 + (-(p:K)^3/6 + (p:K)^2/2 - (p:K)/3) * h0
  have h3 : PS hζ 3 = (3 - (p:K))*((p:K) - 1)/8 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e4 + ((p:K)^2/2 - (p:K)/2) * h2 + (-(p:K)^3/6 + (p:K)^2/2 - (p:K)/3) * h1 + ((p:K)^4/24 - (p:K)^3/4 + 11*(p:K)^2/24 - (p:K)/4) * h0
  have h4 : PS hζ 4 = ((p:K) - 1)*((p:K)^3 + (p:K)^2 - 109*(p:K) + 251)/720 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e5 + ((p:K)^2/2 - (p:K)/2) * h3 + (-(p:K)^3/6 + (p:K)^2/2 - (p:K)/3) * h2 + ((p:K)^4/24 - (p:K)^3/4 + 11*(p:K)^2/24 - (p:K)/4) * h1 + (-(p:K)^5/120 + (p:K)^4/12 - 7*(p:K)^3/24 + 5*(p:K)^2/12 - (p:K)/5) * h0
  have h5 : PS hζ 5 = ((p:K) - 5)*((p:K) - 1)*((p:K)^2 + 6*(p:K) - 19)/288 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e6 + ((p:K)^2/2 - (p:K)/2) * h4 + (-(p:K)^3/6 + (p:K)^2/2 - (p:K)/3) * h3 + ((p:K)^4/24 - (p:K)^3/4 + 11*(p:K)^2/24 - (p:K)/4) * h2 + (-(p:K)^5/120 + (p:K)^4/12 - 7*(p:K)^3/24 + 5*(p:K)^2/12 - (p:K)/5) * h1 + ((p:K)^6/720 - (p:K)^5/48 + 17*(p:K)^4/144 - 5*(p:K)^3/16 + 137*(p:K)^2/360 - (p:K)/6) * h0
  have h6 : PS hζ 6 = (1 - (p:K))*(2*(p:K)^5 + 2*(p:K)^4 - 355*(p:K)^3 - 355*(p:K)^2 + 11153*(p:K) - 19087)/60480 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-1 : K) * e7 + ((p:K)^2/2 - (p:K)/2) * h5 + (-(p:K)^3/6 + (p:K)^2/2 - (p:K)/3) * h4 + ((p:K)^4/24 - (p:K)^3/4 + 11*(p:K)^2/24 - (p:K)/4) * h3 + (-(p:K)^5/120 + (p:K)^4/12 - 7*(p:K)^3/24 + 5*(p:K)^2/12 - (p:K)/5) * h2 + ((p:K)^6/720 - (p:K)^5/48 + 17*(p:K)^4/144 - 5*(p:K)^3/16 + 137*(p:K)^2/360 - (p:K)/6) * h1 + (-(p:K)^7/5040 + (p:K)^6/240 - 5*(p:K)^5/144 + 7*(p:K)^4/48 - 29*(p:K)^3/90 + 7*(p:K)^2/20 - (p:K)/7) * h0

  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- `θ^m (u/(1−u)²)` at `u = w`: `cpoly m (w) / (w−1)^{m+2}`. -/
def cK (m : ℕ) (w : K) : K := Polynomial.eval₂ (Int.castRingHom K) w (cpoly m) / (w - 1) ^ (m + 2)

omit [CharZero K] hp in
lemma cK_y {w : K} (hw : w ≠ 1) :
    cK 0 w = (1 - w)⁻¹ ^ 2 - (1 - w)⁻¹ ∧
    cK 2 w = 6 * (1 - w)⁻¹ ^ 4 - 12 * (1 - w)⁻¹ ^ 3 + 7 * (1 - w)⁻¹ ^ 2 - (1 - w)⁻¹ ∧
    cK 4 w = 120 * (1 - w)⁻¹ ^ 6 - 360 * (1 - w)⁻¹ ^ 5 + 390 * (1 - w)⁻¹ ^ 4 -
      180 * (1 - w)⁻¹ ^ 3 + 31 * (1 - w)⁻¹ ^ 2 - (1 - w)⁻¹ := by
  have h1 : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h2 : (w - 1) ≠ 0 := sub_ne_zero.mpr hw
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cK, cpoly, Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_one, Polynomial.eval₂_ofNat] <;>
    field_simp <;> ring

/-- **`Σ_{k=1}^{p−1} ζ^k/(ζ^k−1)² = −(p²−1)/12`.** -/
theorem kappa0 (hζ : IsPrimitiveRoot ζ p) :
    ∑ k ∈ Ico 1 p, cK 0 (ζ ^ k) = -((p : K) ^ 2 - 1) / 12 := by
  obtain ⟨h0, h1, h2, -⟩ := PS_values hζ
  rw [sum_congr rfl fun k hk => (cK_y (pow_ne_one_Ico hζ hk)).1, sum_sub_distrib]
  simp only [PS, yk, pow_one] at h1 h2
  rw [h1, h2]; ring

theorem kappa2 (hζ : IsPrimitiveRoot ζ p) :
    ∑ k ∈ Ico 1 p, cK 2 (ζ ^ k) = ((p : K) ^ 4 - 1) / 120 := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := PS_values hζ
  rw [sum_congr rfl fun k hk => (cK_y (pow_ne_one_Ico hζ hk)).2.1]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp only [PS, yk, pow_one] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]; ring

theorem kappa4 (hζ : IsPrimitiveRoot ζ p) :
    ∑ k ∈ Ico 1 p, cK 4 (ζ ^ k) = -((p : K) ^ 6 - 1) / 252 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := PS_values hζ
  rw [sum_congr rfl fun k hk => (cK_y (pow_ne_one_Ico hζ hk)).2.2]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp only [PS, yk, pow_one] at h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6]; ring

end TateQuot
