/-
# Garvan's conjugate Bailey pair (relative to `a = q`)

With `F(r,n) = qⁿ (q;q)_n / ((q;q)_{n−r} (q;q)_{n+r+1})` and `S_r = Σ_{n≥r} F(r,n)`, the WZ certificate
`G(r,n) = −q^r(1+q^{r+1}) (q;q)_n / ((q;q)_{n−r−1} (q;q)_{n+r+1})` (sympy) gives
`F(r,n) + q^{3r+3} F(r+1,n) = G(r,n) − G(r,n+1)`, hence, letting `n → ∞`,

  `S_r + q^{3r+3} S_{r+1} = q^r (1 + q^{r+1}) / (q;q)_∞`   (`S_rec`).

-/
import RamanujanTau.Chi0Pair
import RamanujanTau.MockTheta5DurfeeInf

set_option autoImplicit false

namespace Chi0
open PowerSeries Finset MockTheta5.Bailey FourSquares MockTheta5.JTP

local notation "K" => FractionRing (PowerSeries ℤ)

/-- `F(r,n)`. -/
noncomputable def Fc (r n : ℕ) : PowerSeries ℤ := X ^ n * qfac n * invf ((n : ℤ) - r) * invf ((n : ℤ) + r + 1)

/-- the certificate `G(r,n)`. -/
noncomputable def Gc (r n : ℕ) : PowerSeries ℤ :=
  -(X ^ r * (1 + X ^ (r + 1)) * qfac n * invf ((n : ℤ) - r - 1) * invf ((n : ℤ) + r + 1))

lemma φ_qfac_succ (n : ℕ) : φ (qfac (n + 1)) = φ (qfac n) * (1 - z ^ ((n : ℤ) + 1)) := by
  rw [qfac_succ', map_mul, map_sub, map_one, map_pow, ← zpow_natCast]; push_cast; ring_nf

theorem wz_conj (r n : ℕ) : Fc r n + X ^ (3 * r + 3) * Fc (r + 1) n = Gc r n - Gc r (n + 1) := by
  apply φ_inj
  have hz := z_ne
  have hL : iv ((n : ℤ) - (r + 1 : ℕ)) = iv ((n : ℤ) - r) * (1 - z ^ ((n : ℤ) - r)) := by
    rw [← iv_pred]; first | done | (congr 1; push_cast; ring)
  have hL' : iv ((n : ℤ) - r - 1) = iv ((n : ℤ) - r) * (1 - z ^ ((n : ℤ) - r)) := by
    rw [← iv_pred]
  have hL'' : iv (((n + 1 : ℕ) : ℤ) - r - 1) = iv ((n : ℤ) - r) := by
    rw [show ((n + 1 : ℕ) : ℤ) - r - 1 = (n : ℤ) - r by push_cast; ring]
  have hR : iv ((n : ℤ) + r + 1) = iv ((n : ℤ) + r + 2) * (1 - z ^ ((n : ℤ) + r + 2)) := by
    rw [← iv_pred]; congr 1; ring
  have hR' : iv ((n : ℤ) + (r + 1 : ℕ) + 1) = iv ((n : ℤ) + r + 2) := by
    rw [show (n : ℤ) + (r + 1 : ℕ) + 1 = (n : ℤ) + r + 2 by push_cast; ring]
  have hR'' : iv (((n + 1 : ℕ) : ℤ) + r + 1) = iv ((n : ℤ) + r + 2) := by
    rw [show ((n + 1 : ℕ) : ℤ) + r + 1 = (n : ℤ) + r + 2 by push_cast; ring]
  simp only [Fc, Gc, map_add, map_sub, map_neg, map_mul, map_pow, map_one, φ_invf]
  rw [φ_qfac_succ, hL, hL', hL'', hR, hR', hR'']
  generalize iv ((n : ℤ) - r) = a
  generalize iv ((n : ℤ) + r + 2) = b
  generalize φ (qfac n) = Q
  have e : ∀ (u v w : ℤ), z ^ (u * n + v * r + w) = (z ^ (n : ℤ)) ^ u * (z ^ (r : ℤ)) ^ v * z ^ w := fun u v w => by
    rw [zpow_add₀ hz, zpow_add₀ hz, ← zpow_mul, ← zpow_mul, mul_comm (n : ℤ), mul_comm (r : ℤ)]
  rw [show (n : ℤ) - r = 1 * n + (-1) * r + 0 by ring, e, show (n : ℤ) + r + 2 = 1 * n + 1 * r + 2 by ring, e,
    show (n : ℤ) + 1 = 1 * n + 0 * r + 1 by ring, e]
  have hzn : ∀ m : ℕ, (z ^ m : K) = z ^ (m : ℤ) := fun m => (zpow_natCast z m).symm
  rw [hzn n, hzn r, hzn (3 * r + 3), hzn (r + 1), show ((3 * r + 3 : ℕ) : ℤ) = 0 * n + 3 * r + 3 by push_cast; ring, e,
    show ((r + 1 : ℕ) : ℤ) = 0 * n + 1 * r + 1 by push_cast; ring, e]
  have hx : z ^ (n : ℤ) ≠ 0 := zpow_ne_zero _ hz
  have hy : z ^ (r : ℤ) ≠ 0 := zpow_ne_zero _ hz
  generalize z ^ (n : ℤ) = x at *
  generalize z ^ (r : ℤ) = y at *
  simp only [zpow_neg, zpow_one, zpow_zero, mul_one, one_mul, zpow_ofNat]
  field_simp
  ring

/-! ## Telescoping and the limit -/

lemma Gc_zero (r : ℕ) : Gc r 0 = 0 := by
  unfold Gc invf; rw [if_neg (by omega)]; ring

lemma telescope (r N : ℕ) : ∑ n ∈ range N, (Fc r n + X ^ (3 * r + 3) * Fc (r + 1) n) = -Gc r N := by
  rw [sum_congr rfl fun n _ => wz_conj r n, sum_range_sub' (fun n => Gc r n), Gc_zero, zero_sub]

lemma X_pow_dvd_Fc (r n : ℕ) : (X : PowerSeries ℤ) ^ n ∣ Fc r n := by
  unfold Fc; rw [mul_assoc, mul_assoc]; exact dvd_mul_right _ _

/-- `S_r = Σ_{n ≥ 0} F(r,n)` (stabilized coefficientwise). -/
noncomputable def Sr (r : ℕ) : PowerSeries ℤ := mk fun k => coeff k (∑ n ∈ range (k + 1), Fc r n)

lemma coeff_Sr {r k N : ℕ} (hN : k + 1 ≤ N) : coeff k (Sr r) = coeff k (∑ n ∈ range N, Fc r n) := by
  rw [Sr, coeff_mk, map_sum, map_sum]
  refine (sum_subset (Finset.range_mono hN) fun n hn hn' => ?_)
  simp only [mem_range, not_lt] at hn hn'
  obtain ⟨c, hc⟩ := X_pow_dvd_Fc r n
  rw [hc, coeff_X_pow_mul', if_neg (by omega)]

lemma coeff_X_pow_mul_sum {f : ℕ → PowerSeries ℤ} (hf : ∀ n, (X : PowerSeries ℤ) ^ n ∣ f n) (m : ℕ)
    {S : PowerSeries ℤ} (hS : ∀ k N, k + 1 ≤ N → coeff k S = coeff k (∑ n ∈ range N, f n)) {k N : ℕ}
    (hN : k + 1 ≤ N) : coeff k (X ^ m * S) = coeff k (X ^ m * ∑ n ∈ range N, f n) := by
  rw [coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with h
  · exact hS _ _ (by omega)
  · rfl

/-- the limit of `−G(r,N)`. -/
lemma coeff_Gc_lim {r k N : ℕ} (hN : k + r + 2 ≤ N) :
    coeff k (-Gc r N) = coeff k (X ^ r * (1 + X ^ (r + 1)) * partitionGF) := by
  unfold Gc invf
  rw [if_pos (by omega), if_pos (by omega), neg_neg]
  have h1 : (X : PowerSeries ℤ) ^ (k + 1) ∣ qfac N - qfacInf := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, ← coeff_qfacInf (show i + 1 ≤ N by omega), sub_self]
  have h2 := inv_qfac_dvd (k := k) (N := ((N : ℤ) - r - 1).toNat) (by omega)
  have h3 := inv_qfac_dvd (k := k) (N := ((N : ℤ) + r + 1).toNat) (by omega)
  have hP : qfacInf * partitionGF = 1 := Ring.mul_inverse_cancel _ isUnit_qfacInf
  obtain ⟨c1, hc1⟩ := h1; obtain ⟨c2, hc2⟩ := h2; obtain ⟨c3, hc3⟩ := h3
  rw [sub_eq_iff_eq_add] at hc1 hc2 hc3
  rw [hc1, hc2, hc3, ← partitionGF]
  have : X ^ r * (1 + X ^ (r + 1)) * (X ^ (k + 1) * c1 + qfacInf) * (X ^ (k + 1) * c2 + partitionGF) *
      (X ^ (k + 1) * c3 + partitionGF) =
      X ^ r * (1 + X ^ (r + 1)) * partitionGF * (qfacInf * partitionGF) +
        X ^ (k + 1) * (X ^ r * (1 + X ^ (r + 1)) * (c1 * (X ^ (k + 1) * c2 + partitionGF) * (X ^ (k + 1) * c3 + partitionGF)
          + qfacInf * (c2 * (X ^ (k + 1) * c3 + partitionGF) + partitionGF * c3))) := by ring
  rw [this, hP, mul_one, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

/-- **the recurrence** `S_r + q^{3r+3} S_{r+1} = q^r(1+q^{r+1}) / (q;q)_∞`. -/
theorem S_rec (r : ℕ) : Sr r + X ^ (3 * r + 3) * Sr (r + 1) = X ^ r * (1 + X ^ (r + 1)) * partitionGF := by
  ext k
  have hN : k + 1 ≤ k + r + 2 := by omega
  rw [map_add, coeff_Sr hN, coeff_X_pow_mul_sum (X_pow_dvd_Fc (r + 1)) _ (fun k N h => coeff_Sr h) hN, ← map_add,
    mul_sum, ← sum_add_distrib, telescope, coeff_Gc_lim le_rfl]

/-! ## The closed form -/

/-- `γ_r = (q;q)_∞ S_r`. -/
noncomputable def γc (r : ℕ) : PowerSeries ℤ := qfacInf * Sr r

theorem γc_rec (r : ℕ) : γc r + X ^ (3 * r + 3) * γc (r + 1) = X ^ r * (1 + X ^ (r + 1)) := by
  have h := congrArg (qfacInf * ·) (S_rec r)
  simp only at h
  have hP : qfacInf * partitionGF = 1 := Ring.mul_inverse_cancel _ isUnit_qfacInf
  unfold γc
  linear_combination h + (X ^ r * (1 + X ^ (r + 1))) * hP

/-- the exponent `r + 3ru + u(3u+5)/2`. -/
def eC (r u : ℕ) : ℕ := r + 3 * r * u + u * (3 * u + 5) / 2

lemma eC_succ (r u : ℕ) : eC r (u + 1) = 3 * r + 3 + eC (r + 1) u := by
  unfold eC
  have h1 : (u + 1) * (3 * (u + 1) + 5) = u * (3 * u + 5) + 2 * (3 * u + 4) := by ring
  rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]
  have : 2 ∣ u * (3 * u + 5) := by
    rcases Nat.even_or_odd u with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨k * (6 * k + 5), by ring⟩
    · exact ⟨(2 * k + 1) * (3 * k + 4), by ring⟩
  ring

/-- the `u`-th term `(−1)^u q^{eC r u} (1 + q^{r+1+u})`. -/
noncomputable def tC (r u : ℕ) : PowerSeries ℤ := (-1) ^ u * X ^ eC r u * (1 + X ^ (r + 1 + u))

lemma X_pow_dvd_tC (r u : ℕ) : (X : PowerSeries ℤ) ^ u ∣ tC r u := by
  unfold tC
  have : u ≤ eC r u := by
    unfold eC
    have : u ≤ u * (3 * u + 5) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le this
  rw [hd, pow_add]; exact ⟨(-1) ^ u * X ^ d * (1 + X ^ (r + 1 + u)), by ring⟩

/-- Garvan's closed form `Σ_{u≥0} (−1)^u q^{r+3ru+u(3u+5)/2} (1 + q^{r+1+u})`. -/
noncomputable def Cc (r : ℕ) : PowerSeries ℤ := mk fun k => coeff k (∑ u ∈ range (k + 1), tC r u)

lemma coeff_Cc {r k N : ℕ} (hN : k + 1 ≤ N) : coeff k (Cc r) = coeff k (∑ u ∈ range N, tC r u) := by
  rw [Cc, coeff_mk, map_sum, map_sum]
  refine (sum_subset (Finset.range_mono hN) fun u hu hu' => ?_)
  simp only [mem_range, not_lt] at hu hu'
  obtain ⟨c, hc⟩ := X_pow_dvd_tC r u
  rw [hc, coeff_X_pow_mul', if_neg (by omega)]

lemma tC_succ (r u : ℕ) : tC r (u + 1) = -(X ^ (3 * r + 3) * tC (r + 1) u) := by
  unfold tC
  rw [eC_succ, pow_add, show r + 1 + (u + 1) = r + 1 + 1 + u by ring, pow_succ]
  ring

theorem Cc_rec (r : ℕ) : Cc r + X ^ (3 * r + 3) * Cc (r + 1) = X ^ r * (1 + X ^ (r + 1)) := by
  ext k
  have hN : k + 1 ≤ k + 2 := by omega
  rw [map_add, coeff_Cc hN, coeff_X_pow_mul_sum (X_pow_dvd_tC (r + 1)) _ (fun k N h => coeff_Cc h) hN, ← map_add]
  rw [show k + 2 = (k + 1) + 1 by ring, sum_range_succ' (tC r), sum_range_succ (tC (r + 1)), mul_add, mul_sum]
  rw [sum_congr rfl (fun u _ => tC_succ r u), sum_neg_distrib]
  have h0 : tC r 0 = X ^ r * (1 + X ^ (r + 1)) := by unfold tC eC; simp
  rw [h0]
  have hlast : coeff k (X ^ (3 * r + 3) * tC (r + 1) (k + 1)) = 0 := by
    obtain ⟨c, hc⟩ := X_pow_dvd_tC (r + 1) (k + 1)
    rw [hc, ← mul_assoc, ← pow_add, coeff_X_pow_mul', if_neg (by omega)]
  have : -∑ x ∈ range (k + 1), X ^ (3 * r + 3) * tC (r + 1) x + X ^ r * (1 + X ^ (r + 1)) +
      (∑ i ∈ range (k + 1), X ^ (3 * r + 3) * tC (r + 1) i + X ^ (3 * r + 3) * tC (r + 1) (k + 1)) =
      X ^ r * (1 + X ^ (r + 1)) + X ^ (3 * r + 3) * tC (r + 1) (k + 1) := by ring
  rw [this, map_add, hlast, add_zero]

/-- **Garvan's conjugate pair**: `γ_r = Σ_{u≥0} (−1)^u q^{r+3ru+u(3u+5)/2}(1 + q^{r+1+u})`. -/
theorem γc_eq (r : ℕ) : γc r = Cc r := by
  have key : ∀ m r, (X : PowerSeries ℤ) ^ m ∣ γc r - Cc r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
      intro r
      have h1 := γc_rec r; have h2 := Cc_rec r
      have : γc r - Cc r = -(X ^ (3 * r + 3) * (γc (r + 1) - Cc (r + 1))) := by linear_combination h1 - h2
      rw [this]
      obtain ⟨c, hc⟩ := ih (r + 1)
      rw [hc]
      exact ⟨-(X ^ (3 * r + 2) * c), by ring⟩
  ext k
  obtain ⟨c, hc⟩ := key (k + 1) r
  have := congrArg (coeff k) hc
  rw [coeff_X_pow_mul', if_neg (by omega), map_sub, sub_eq_zero] at this
  exact this

end Chi0
