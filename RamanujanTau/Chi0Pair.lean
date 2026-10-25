/-
# A Bailey pair for `χ₀` (relative to `a = q`), part 1: a finite identity by WZ

  `Σ_{j∈ℤ} (q^{j(6j−1)} − q^{(2j+1)(3j+1)}) [2n+1; n−3j]_q = 1 − q^{2n+1}`.

Proof by the WZ method in the fraction field `K` of `ℤ⟦q⟧`, with `z = q`. With `iv k = 1/(q;q)_k` for `k ≥ 0` and
`0` for `k < 0`, the relation `iv (k−1) = iv k (1 − z^k)` holds for **every** `k ∈ ℤ`, so the WZ step is a single
field identity for all `j`. With `p(n,j) = summand/(1 − q^{2n+1})` and the certificate
`g(n,j) = −q^{6j²−4j+n+1} [2n; n+1−3j]_q` (found with sympy),
`p(n+1,j) − p(n,j) = g(n,j+1) − g(n,j)`.
-/
import RamanujanTau.FourSquaresWZ

set_option autoImplicit false

namespace Chi0
open PowerSeries Finset MockTheta5.Bailey FourSquares

local notation "K" => FractionRing (PowerSeries ℤ)

/-- `z = q` in `K`. -/
noncomputable abbrev z : K := φ X

lemma z_ne : z ≠ 0 := fun h => X_ne_zero (φ_inj (h.trans (map_zero φ).symm))

/-- `1/(q;q)_k`, or `0` for `k < 0`. -/
noncomputable def iv (k : ℤ) : K := if 0 ≤ k then (φ (qfac k.toNat))⁻¹ else 0

lemma qfacK_ne (m : ℕ) : φ (qfac m) ≠ 0 := φ_ne (isUnit_qfac m)

lemma iv_pred (k : ℤ) : iv (k - 1) = iv k * (1 - z ^ k) := by
  unfold iv
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [if_neg (by omega), if_neg (by omega), zero_mul]
  · simp
  · rw [if_pos (by omega), if_pos hk.le]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [show (m : ℤ) + 1 - 1 = (m : ℤ) by ring, Int.toNat_natCast, show ((m : ℤ) + 1).toNat = m + 1 by omega,
      qfac_succ', map_mul, map_sub, map_one, map_pow, show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
    have h1 := qfacK_ne m
    have h2 : (1 - z ^ (m + 1) : K) ≠ 0 := by
      have := φ_ne (isUnit_one_sub (m := m + 1) (by omega)); simpa using this
    field_simp

/-- `[N; k]_q` in `K` (zero outside `0 ≤ k ≤ N`). -/
noncomputable def gb (N : ℕ) (k : ℤ) : K := φ (qfac N) * iv k * iv (N - k)

/-- the normalized summand `p(n,j)`. -/
noncomputable def pK (n : ℕ) (j : ℤ) : K :=
  (z ^ (j * (6 * j - 1)) - z ^ ((2 * j + 1) * (3 * j + 1))) * gb (2 * n + 1) (n - 3 * j) / (1 - z ^ (2 * n + 1 : ℤ))

/-- the WZ certificate. -/
noncomputable def gK (n : ℕ) (j : ℤ) : K := -(z ^ (6 * j ^ 2 - 4 * j + n + 1) * gb (2 * n) (n + 1 - 3 * j))

lemma one_sub_z_ne {m : ℕ} (hm : 1 ≤ m) : (1 - z ^ (m : ℤ) : K) ≠ 0 := by
  have := φ_ne (isUnit_one_sub (m := m) hm)
  rw [zpow_natCast]; simpa using this

theorem wz_step (n : ℕ) (j : ℤ) : pK (n + 1) j - pK n j = gK n (j + 1) - gK n j := by
  have hz := z_ne
  -- inverse factorials in terms of `iv (n+1−3j)` and `iv (n+3j+2)`
  have hL1 : iv ((n : ℤ) - 3 * j) = iv ((n : ℤ) + 1 - 3 * j) * (1 - z ^ ((n : ℤ) + 1 - 3 * j)) := by
    rw [← iv_pred]; congr 1; ring
  have hL3 : iv ((n : ℤ) - 2 - 3 * j) = iv ((n : ℤ) + 1 - 3 * j) * (1 - z ^ ((n : ℤ) + 1 - 3 * j)) *
      (1 - z ^ ((n : ℤ) - 3 * j)) * (1 - z ^ ((n : ℤ) - 1 - 3 * j)) := by
    rw [← hL1, ← iv_pred, show (n : ℤ) - 3 * j - 1 = (n : ℤ) - 1 - 3 * j by ring, ← iv_pred]; first | done | (congr 1; ring)
  have hR1 : iv ((n : ℤ) + 3 * j + 1) = iv ((n : ℤ) + 3 * j + 2) * (1 - z ^ ((n : ℤ) + 3 * j + 2)) := by
    rw [← iv_pred]; congr 1; ring
  have hR3 : iv ((n : ℤ) + 3 * j - 1) = iv ((n : ℤ) + 3 * j + 2) * (1 - z ^ ((n : ℤ) + 3 * j + 2)) *
      (1 - z ^ ((n : ℤ) + 3 * j + 1)) * (1 - z ^ ((n : ℤ) + 3 * j)) := by
    rw [← hR1, ← iv_pred, show (n : ℤ) + 3 * j + 1 - 1 = (n : ℤ) + 3 * j by ring, ← iv_pred]; first | done | (congr 1; ring)
  -- factorials
  have hzn : ∀ m : ℕ, (z ^ m : K) = z ^ (m : ℤ) := fun m => (zpow_natCast z m).symm
  have hQ1 : φ (qfac (2 * n + 1)) = φ (qfac (2 * n)) * (1 - z ^ (2 * (n : ℤ) + 1)) := by
    rw [qfac_succ', map_mul, map_sub, map_one, map_pow, hzn]; push_cast; ring_nf
  have hQ3 : φ (qfac (2 * (n + 1) + 1)) = φ (qfac (2 * n)) * (1 - z ^ (2 * (n : ℤ) + 1)) *
      (1 - z ^ (2 * (n : ℤ) + 2)) * (1 - z ^ (2 * (n : ℤ) + 3)) := by
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, qfac_succ', qfac_succ', map_mul, map_mul, hQ1, map_sub,
      map_sub, map_one, map_pow, map_pow, hzn, hzn]
    push_cast; ring_nf
  -- monomials
  have hM2 : z ^ ((2 * j + 1) * (3 * j + 1)) = z ^ (j * (6 * j - 1)) * z ^ (6 * j + 1) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  have hG0 : z ^ (6 * j ^ 2 - 4 * j + n + 1) = z ^ (j * (6 * j - 1)) * z ^ ((n : ℤ) + 1 - 3 * j) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  have hG1 : z ^ (6 * (j + 1) ^ 2 - 4 * (j + 1) + n + 1) = z ^ (j * (6 * j - 1)) * z ^ ((n : ℤ) + 9 * j + 3) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  have h1 : (1 - z ^ (2 * (n : ℤ) + 1) : K) ≠ 0 := by
    rw [show 2 * (n : ℤ) + 1 = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring]; exact one_sub_z_ne (by omega)
  have h3 : (1 - z ^ (2 * (n : ℤ) + 3) : K) ≠ 0 := by
    rw [show 2 * (n : ℤ) + 3 = ((2 * n + 3 : ℕ) : ℤ) by push_cast; ring]; exact one_sub_z_ne (by omega)
  unfold pK gK gb
  push_cast
  rw [show (2 * ((n : ℤ) + 1) + 1 : ℤ) - ((n : ℤ) + 1 - 3 * j) = (n : ℤ) + 3 * j + 2 by ring,
    show (2 * (n : ℤ) + 1 : ℤ) - ((n : ℤ) - 3 * j) = (n : ℤ) + 3 * j + 1 by ring,
    show (2 * (n : ℤ) : ℤ) - ((n : ℤ) + 1 - 3 * (j + 1)) = (n : ℤ) + 3 * j + 2 by ring,
    show (2 * (n : ℤ) : ℤ) - ((n : ℤ) + 1 - 3 * j) = (n : ℤ) + 3 * j - 1 by ring,
    show (n : ℤ) + 1 - 3 * (j + 1) = (n : ℤ) - 2 - 3 * j by ring,
    show 2 * ((n : ℤ) + 1) + 1 = 2 * (n : ℤ) + 3 by ring,
    hL1, hL3, hR1, hR3, hQ3, hQ1, hM2, hG0, hG1]
  have e3 : ∀ (u v w : ℤ), z ^ (u * n + v * j + w) = (z ^ (n : ℤ)) ^ u * (z ^ j) ^ v * z ^ w := fun u v w => by
    rw [zpow_add₀ hz, zpow_add₀ hz, ← zpow_mul, ← zpow_mul, mul_comm (n : ℤ), mul_comm j]
  rw [show 6 * j + 1 = 0 * (n : ℤ) + 6 * j + 1 by ring, e3,
    show 2 * (n : ℤ) + 1 = 2 * n + 0 * j + 1 by ring, e3,
    show 2 * (n : ℤ) + 2 = 2 * n + 0 * j + 2 by ring, e3,
    show 2 * (n : ℤ) + 3 = 2 * n + 0 * j + 3 by ring, e3,
    show (n : ℤ) + 1 - 3 * j = 1 * n + (-3) * j + 1 by ring, e3,
    show (n : ℤ) - 3 * j = 1 * n + (-3) * j + 0 by ring, e3,
    show (n : ℤ) - 1 - 3 * j = 1 * n + (-3) * j + (-1) by ring, e3,
    show (n : ℤ) + 3 * j + 2 = 1 * n + 3 * j + 2 by ring, e3,
    show (n : ℤ) + 3 * j + 1 = 1 * n + 3 * j + 1 by ring, e3,
    show (n : ℤ) + 3 * j = 1 * n + 3 * j + 0 by ring, e3,
    show (n : ℤ) + 9 * j + 3 = 1 * n + 9 * j + 3 by ring, e3] at *
  generalize iv (1 * (n : ℤ) + (-3) * j + 1) = a at *
  generalize iv (1 * (n : ℤ) + 3 * j + 2) = b at *
  generalize φ (qfac (2 * n)) = Q at *
  generalize z ^ (j * (6 * j - 1)) = M at *
  have hx0 : z ^ (n : ℤ) ≠ 0 := zpow_ne_zero _ hz
  have hy0 : z ^ j ≠ 0 := zpow_ne_zero _ hz
  generalize z ^ (n : ℤ) = x at *
  generalize z ^ j = y at *
  simp only [zpow_neg, zpow_one, zpow_zero, mul_one, one_mul, zpow_ofNat] at *
  have h1' : (1 - z * x ^ 2 : K) ≠ 0 := by convert h1 using 1; ring
  have h3' : (1 - z ^ 3 * x ^ 2 : K) ≠ 0 := by convert h3 using 1; ring
  field_simp
  ring

/-! ## Summation -/

lemma iv_neg {k : ℤ} (hk : k < 0) : iv k = 0 := by unfold iv; rw [if_neg (by omega)]

lemma gb_lo {N : ℕ} {k : ℤ} (hk : k < 0) : gb N k = 0 := by unfold gb; rw [iv_neg hk]; ring
lemma gb_hi {N : ℕ} {k : ℤ} (hk : (N : ℤ) < k) : gb N k = 0 := by unfold gb; rw [iv_neg (by omega : (N : ℤ) - k < 0)]; ring

lemma pK_zero_of {n : ℕ} {j : ℤ} (h : (n : ℤ) - 3 * j < 0 ∨ ((2 * n + 1 : ℕ) : ℤ) < (n : ℤ) - 3 * j) : pK n j = 0 := by
  unfold pK
  rcases h with h | h
  · rw [gb_lo h]; ring
  · rw [gb_hi h]; ring

lemma gK_zero_of {n : ℕ} {j : ℤ} (h : (n : ℤ) + 1 - 3 * j < 0 ∨ ((2 * n : ℕ) : ℤ) < (n : ℤ) + 1 - 3 * j) : gK n j = 0 := by
  unfold gK
  rcases h with h | h
  · rw [gb_lo h]; ring
  · rw [gb_hi h]; ring

/-- the sum over the window `|j| ≤ R`. -/
noncomputable def T (n R : ℕ) : K := ∑ i ∈ range (2 * R + 1), pK n ((i : ℤ) - R)

lemma T_succ_R {n R : ℕ} (hR : n ≤ R) : T n (R + 1) = T n R := by
  unfold T
  rw [show 2 * (R + 1) + 1 = (2 * R + 1) + 1 + 1 by ring, sum_range_succ, sum_range_succ',
    pK_zero_of (j := ((2 * R + 1 + 1 : ℕ) : ℤ) - ((R + 1 : ℕ) : ℤ)) (Or.inl (by push_cast; omega)),
    pK_zero_of (j := ((0 : ℕ) : ℤ) - ((R + 1 : ℕ) : ℤ)) (Or.inr (by push_cast; omega)), add_zero, add_zero]
  refine sum_congr rfl fun i _ => ?_
  congr 1; push_cast; ring

lemma T_telescope (n R : ℕ) (hR : n + 3 ≤ R) : T (n + 1) R = T n R := by
  have h : ∀ i ∈ range (2 * R + 1), pK (n + 1) ((i : ℤ) - R) - pK n ((i : ℤ) - R) =
      gK n (((i + 1 : ℕ) : ℤ) - R) - gK n ((i : ℤ) - R) := fun i _ => by
    rw [wz_step]; push_cast; ring_nf
  have := sum_congr rfl h
  rw [sum_sub_distrib, sum_range_sub (fun i => gK n ((i : ℤ) - R))] at this
  rw [gK_zero_of (j := (((2 * R + 1 : ℕ) : ℤ) - R)) (Or.inl (by push_cast; omega)),
    gK_zero_of (j := (((0 : ℕ) : ℤ) - R)) (Or.inr (by push_cast; omega)), sub_zero] at this
  unfold T
  linear_combination this

lemma T_eq_one (n : ℕ) : T n (n + 3) = 1 := by
  induction n with
  | zero =>
    rw [T_succ_R (by omega), T_succ_R (by omega), T_succ_R (by omega)]
    unfold T pK gb
    simp only [sum_range_succ]
    have h1 : (1 - z : K) ≠ 0 := by
      have := φ_ne (isUnit_one_sub (m := 1) le_rfl); simpa using this
    have hq : φ (qfac 1) = 1 - z := by simp [qfac]
    norm_num [iv, hq]
    field_simp
  | succ n ih =>
    rw [T_telescope n (n + 1 + 3) (by omega), T_succ_R (by omega), ih]

/-- **the finite identity** `Σ_j (q^{j(6j−1)} − q^{(2j+1)(3j+1)}) [2n+1; n−3j]_q = 1 − q^{2n+1}` (in `K`). -/
theorem finite_identity (n : ℕ) :
    ∑ i ∈ range (2 * (n + 3) + 1), (z ^ (((i : ℤ) - (n + 3 : ℕ)) * (6 * ((i : ℤ) - (n + 3 : ℕ)) - 1)) -
        z ^ ((2 * ((i : ℤ) - (n + 3 : ℕ)) + 1) * (3 * ((i : ℤ) - (n + 3 : ℕ)) + 1))) *
      gb (2 * n + 1) ((n : ℤ) - 3 * ((i : ℤ) - (n + 3 : ℕ))) = 1 - z ^ (2 * n + 1 : ℤ) := by
  have h := T_eq_one n
  have hd : (1 - z ^ (2 * n + 1 : ℤ) : K) ≠ 0 := by exact_mod_cast one_sub_z_ne (m := 2 * n + 1) (by omega)
  unfold T pK at h
  simp only [div_eq_mul_inv] at h
  rw [← Finset.sum_mul, mul_inv_eq_one₀ hd] at h
  exact h

/-! ## Back to `ℤ⟦q⟧` -/

/-- `1/(q;q)_k` in `ℤ⟦q⟧`, or `0` for `k < 0`. -/
noncomputable def invf (k : ℤ) : PowerSeries ℤ := if 0 ≤ k then Ring.inverse (qfac k.toNat) else 0

lemma φ_invf (k : ℤ) : φ (invf k) = iv k := by
  unfold invf iv
  split_ifs
  · exact φ_inverse (isUnit_qfac _)
  · exact map_zero φ

/-- the coefficient `c_j = q^{j(6j−1)} − q^{(2j+1)(3j+1)}` of the χ₀ pair. -/
noncomputable def cj (j : ℤ) : PowerSeries ℤ := X ^ (j * (6 * j - 1)).toNat - X ^ ((2 * j + 1) * (3 * j + 1)).toNat

lemma e1_nonneg (j : ℤ) : 0 ≤ j * (6 * j - 1) := by
  rcases (by omega : j ≤ 0 ∨ 1 ≤ j) with h | h
  · nlinarith
  · nlinarith
lemma e2_nonneg (j : ℤ) : 0 ≤ (2 * j + 1) * (3 * j + 1) := by
  rcases le_total 0 j with h | h
  · positivity
  · have : j ≤ -1 ∨ j = 0 := by omega
    rcases this with h' | h'
    · nlinarith
    · subst h'; norm_num

lemma φ_cj (j : ℤ) : φ (cj j) = z ^ (j * (6 * j - 1)) - z ^ ((2 * j + 1) * (3 * j + 1)) := by
  unfold cj
  rw [map_sub, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (e1_nonneg j),
    Int.toNat_of_nonneg (e2_nonneg j)]

/-- **the χ₀ Bailey pair (relative to `a = q`), in `j`-indexed form**:
`(1 − q^{2n+1})/(q;q)_{2n+1} = Σ_j c_j / ((q;q)_{n−3j} (q;q)_{n+3j+1})`. -/
theorem pair_identity (n : ℕ) :
    (1 - X ^ (2 * n + 1)) * Ring.inverse (qfac (2 * n + 1)) =
      ∑ i ∈ range (2 * (n + 3) + 1), cj ((i : ℤ) - (n + 3 : ℕ)) * invf ((n : ℤ) - 3 * ((i : ℤ) - (n + 3 : ℕ))) *
        invf ((n : ℤ) + 3 * ((i : ℤ) - (n + 3 : ℕ)) + 1) := by
  apply φ_inj
  have h := finite_identity n
  have hQ := qfacK_ne (2 * n + 1)
  rw [map_mul, map_sub, map_one, map_pow, φ_inverse (isUnit_qfac _), map_sum]
  simp only [map_mul, φ_cj, φ_invf]
  unfold gb at h
  rw [← zpow_natCast, show ((2 * n + 1 : ℕ) : ℤ) = (2 * n + 1 : ℤ) by push_cast; ring, ← h, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [show ((2 * n + 1 : ℕ) : ℤ) - ((n : ℤ) - 3 * ((i : ℤ) - (n + 3 : ℕ))) =
    (n : ℤ) + 3 * ((i : ℤ) - (n + 3 : ℕ)) + 1 by push_cast; ring]
  field_simp

end Chi0
