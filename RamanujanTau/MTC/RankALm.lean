/-
# The Appell–Lerch form of the rank generating function at `z = X^a`, `q = X^b`

`rank_AL_m`: for `0 < a < b`,
`Σ_n X^{bn²}/((X^{a+b};X^b)_n (X^{b−a};X^b)_n) = (1/(X^b;X^b)_∞) Σ_r X^{br²} α_r` in `ℤ⟦X⟧`, with
`α_0 = 1`, `α_r = (−1)^r X^{b C(r+1,2) − a}(1 + X^{br})(−(1 − X^a)²)/((1 − X^{a+br})(1 − X^{br−a}))`.
This is `RankProof.rank_AL` (constant `z`) redone with the field-generic finite pair `RankProof.al_pair` in
`FractionRing ℤ⟦X⟧` and Durfee's identity in base `X^b`.
-/
import RamanujanTau.RankAL
import RamanujanTau.CrankAndrewsGarvan
import RamanujanTau.RankSpec

set_option autoImplicit false

namespace MTC
open PowerSeries Finset RankProof MockTheta5.Bailey MockTheta5.JTP

abbrev KZ := FractionRing (PowerSeries ℤ)
noncomputable abbrev φZ : PowerSeries ℤ →+* KZ := algebraMap (PowerSeries ℤ) KZ

lemma φZ_inj : Function.Injective φZ := IsFractionRing.injective _ _

lemma φZ_inverse {u : PowerSeries ℤ} (hu : IsUnit u) : φZ (Ring.inverse u) = (φZ u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one])

lemma φZ_ne {f : PowerSeries ℤ} (h : f ≠ 0) : φZ f ≠ 0 := fun h' => h (φZ_inj (by rw [h', map_zero]))

lemma isUnit_one_sub_Xpow {k : ℕ} (hk : 0 < k) : IsUnit (1 - X ^ k : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff]; simp [zero_pow hk.ne']

lemma one_sub_Xpow_ne {k : ℕ} (hk : 0 < k) : (1 - X ^ k : PowerSeries ℤ) ≠ 0 :=
  (isUnit_one_sub_Xpow hk).ne_zero

section RankM
variable {a b : ℕ} (ha : 0 < a) (hab : a < b)

/-- the variable `x = X` in the fraction field. -/
noncomputable abbrev xZ : KZ := φZ X

lemma xZ_ne : xZ ≠ 0 := φZ_ne X_ne_zero

/-- `α_r` as a power series. -/
noncomputable def αm (a b r : ℕ) : PowerSeries ℤ :=
  if r = 0 then 1
  else (-1) ^ r * X ^ (b * (r + 1).choose 2 - a) * (1 + X ^ (b * r)) * (-(1 - X ^ a) ^ 2) *
    Ring.inverse ((1 - X ^ (a + b * r)) * (1 - X ^ (b * r - a)))

include ha hab in
lemma φZ_αm (r : ℕ) : φZ (αm a b r) = alL (xZ ^ b) (xZ ^ a) r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [αm, alL]
  have hr0 : r ≠ 0 := by omega
  have hbr : a < b * r := by nlinarith
  have hC : r ≤ (r + 1).choose 2 := by rw [Nat.choose_succ_succ', Nat.choose_one_right]; omega
  have hbC : a ≤ b * (r + 1).choose 2 := by nlinarith
  have hu : IsUnit ((1 - X ^ (a + b * r)) * (1 - X ^ (b * r - a)) : PowerSeries ℤ) :=
    (isUnit_one_sub_Xpow (by omega)).mul (isUnit_one_sub_Xpow (by omega))
  have hx : xZ ≠ 0 := xZ_ne
  have hA : xZ ^ a ≠ 0 := pow_ne_zero _ hx
  have e1 : xZ ^ (b * (r + 1).choose 2 - a) = (xZ ^ b) ^ ((r + 1).choose 2) / xZ ^ a := by
    rw [eq_div_iff hA, ← pow_add, Nat.sub_add_cancel hbC, pow_mul]
  have e2 : xZ ^ (b * r - a) = (xZ ^ b) ^ r / xZ ^ a := by
    rw [eq_div_iff hA, ← pow_add, Nat.sub_add_cancel hbr.le, pow_mul]
  have e3 : xZ ^ (a + b * r) = xZ ^ a * (xZ ^ b) ^ r := by rw [pow_add, pow_mul]
  have e4 : xZ ^ (b * r) = (xZ ^ b) ^ r := pow_mul _ _ _
  have h1 : (1 : KZ) - xZ ^ a * (xZ ^ b) ^ r ≠ 0 := by
    have := φZ_ne (one_sub_Xpow_ne (show 0 < a + b * r by omega))
    rwa [map_sub, map_one, map_pow, e3] at this
  have h2 : (1 : KZ) - (xZ ^ b) ^ r / xZ ^ a ≠ 0 := by
    have := φZ_ne (one_sub_Xpow_ne (show 0 < b * r - a by omega))
    rwa [map_sub, map_one, map_pow, e2] at this
  have h2' : xZ ^ a - (xZ ^ b) ^ r ≠ 0 := fun h => h2 (by
    rw [← sub_eq_zero.mp h, div_self hA, sub_self])
  simp only [αm, alL, if_neg hr0]
  rw [map_mul, φZ_inverse hu]
  simp only [map_mul, map_sub, map_add, map_one, map_pow, map_neg]
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- `(q;q)_m` in base `X^b` is `Ea b (qfac m)`. -/
lemma φZ_Eqfac (m : ℕ) : φZ (Ea b (by omega) (qfac m)) = P (xZ ^ b) m := by
  have hb0 : b ≠ 0 := by omega
  rw [qfac, map_prod, map_prod, P]
  refine prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, Ea_X, map_sub, map_one, map_pow, map_pow, ← pow_mul]

include ha hab in
lemma φZ_Wn (n : ℕ) :
    φZ (Pfin (a + b) b n) * φZ (Pfin (b - a) b n) = Wn (xZ ^ b) (xZ ^ a) n := by
  have hx := xZ_ne
  rw [Pfin, Pfin, map_prod, map_prod, ← prod_mul_distrib, Wn]
  refine prod_congr rfl fun i _ => ?_
  simp only [map_sub, map_one, map_pow]
  have e1 : a + b + b * i = a + b * (i + 1) := by ring
  have e2 : b - a + b * i = b * (i + 1) - a := by
    rw [mul_add, mul_one]; omega
  rw [e1, e2, pow_add, pow_mul, pow_sub₀ _ hx (by nlinarith), pow_mul]
  ring

include ha hab in
lemma hq_m : ∀ i : ℕ, 1 - (xZ ^ b) ^ (i + 1) ≠ 0 := fun i => by
  have := φZ_ne (one_sub_Xpow_ne (show 0 < b * (i + 1) from Nat.mul_pos (by omega) (by omega)))
  rwa [map_sub, map_one, map_pow, pow_mul] at this

lemma hz_m : xZ ^ a ≠ 0 := pow_ne_zero _ xZ_ne

include ha hab in
lemma hzq_m : ∀ i : ℕ, 1 - xZ ^ a * (xZ ^ b) ^ (i + 1) ≠ 0 := fun i => by
  have := φZ_ne (one_sub_Xpow_ne (show 0 < a + b * (i + 1) by omega))
  rwa [map_sub, map_one, map_pow, pow_add, pow_mul] at this

include ha hab in
lemma hzq'_m : ∀ i : ℕ, xZ ^ a - (xZ ^ b) ^ (i + 1) ≠ 0 := fun i => by
  have hne : (X ^ a - X ^ (b * (i + 1)) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (coeff a) h
    rw [map_sub, coeff_X_pow_self, coeff_X_pow, if_neg (by nlinarith), sub_zero] at this
    exact one_ne_zero this
  have := φZ_ne hne
  rwa [map_sub, map_pow, map_pow, pow_mul] at this

include ha hab in
/-- **the finite pair in `ℤ⟦X⟧`**. -/
theorem al_pair_m (n : ℕ) :
    ∑ r ∈ range (n + 1), αm a b r * Ring.inverse (Ea b (by omega) (qfac (n - r))) *
      Ring.inverse (Ea b (by omega) (qfac (n + r)))
      = Ring.inverse (Pfin (a + b) b n) * Ring.inverse (Pfin (b - a) b n) := by
  have hb0 : b ≠ 0 := by omega
  apply φZ_inj
  have h := al_pair (hq_m ha hab) hz_m (hzq_m ha hab) (hzq'_m ha hab) n
  have hP1 : IsUnit (Pfin (a + b) b n) := isUnit_Pfin _ _ _ (by omega)
  have hP2 : IsUnit (Pfin (b - a) b n) := isUnit_Pfin _ _ _ (by omega)
  have hE : ∀ m, IsUnit (Ea b hb0 (qfac m)) := fun m => (isUnit_qfac m).map _
  have hψ : ∀ m, φZ (Ring.inverse (Ea b hb0 (qfac m))) = (P (xZ ^ b) m)⁻¹ := fun m => by
    rw [φZ_inverse (hE m), φZ_Eqfac ha hab]
  rw [map_mul, φZ_inverse hP1, φZ_inverse hP2, ← mul_inv, φZ_Wn ha hab, map_sum,
    ← mul_one (Wn (xZ ^ b) (xZ ^ a) n)⁻¹, ← h, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, hψ, hψ, φZ_αm ha hab, Fr]
  have h1 := P_ne (hq_m ha hab) (n - r)
  have h2 := P_ne (hq_m ha hab) (n + r)
  have hW : Wn (xZ ^ b) (xZ ^ a) n ≠ 0 := by
    rw [← φZ_Wn ha hab]; exact mul_ne_zero (φZ_ne hP1.ne_zero) (φZ_ne hP2.ne_zero)
  field_simp

/-- `Σ_n X^{bn²}/((X^{a+b};X^b)_n (X^{b−a};X^b)_n)`. -/
noncomputable def Dm (a b : ℕ) : PowerSeries ℤ :=
  mk fun c => coeff c (∑ n ∈ range (c + 1), X ^ (b * n ^ 2) * Ring.inverse (Pfin (a + b) b n) *
    Ring.inverse (Pfin (b - a) b n))

/-- `Σ_r X^{br²} α_r`. -/
noncomputable def ALm (a b : ℕ) : PowerSeries ℤ :=
  mk fun c => coeff c (∑ r ∈ range (c + 1), X ^ (b * r ^ 2) * αm a b r)

lemma ALm_dvd (a b : ℕ) (hb : 0 < b) (c : ℕ) :
    (X : PowerSeries ℤ) ^ (c + 1) ∣ ALm a b - ∑ r ∈ range (c + 1), X ^ (b * r ^ 2) * αm a b r := by
  rw [X_pow_dvd_iff]; intro i hi
  rw [map_sub, ALm, coeff_mk, sub_eq_zero, map_sum, map_sum]
  refine sum_subset (range_subset_range.mpr (by omega)) fun r _ hr => ?_
  simp only [mem_range, not_lt] at hr
  have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
  exact coeffZ_Xpow_zero (by nlinarith) _

/-- the double-sum term. -/
noncomputable def Hm (a b : ℕ) (hb : b ≠ 0) (c r m : ℕ) : ℤ :=
  coeff c (X ^ (b * r ^ 2) * αm a b r * Ea b hb (rectTerm (2 * r) m))

include ha hab in
/-- **the Appell–Lerch form of the rank generating function at `z = X^a`, `q = X^b`**. -/
theorem rank_AL_m : Dm a b = Ea b (by omega) (Ring.inverse qfacInf) * ALm a b := by
  have hb0 : b ≠ 0 := by omega
  have hEi : ∀ m, Ea b hb0 (Ring.inverse (qfac m)) = Ring.inverse (Ea b hb0 (qfac m)) := fun m =>
    CrankProof.map_inverse _ (isUnit_qfac m)
  ext c
  let f := Hm a b hb0 c
  have hR : coeff c (Ea b hb0 (Ring.inverse qfacInf) * ALm a b) =
      ∑ r ∈ range (c + 1), ∑ m ∈ range (c + 1), f r m := by
    rw [coeffZ_congr (ALm_dvd a b (by omega) c), mul_sum, map_sum]
    refine sum_congr rfl fun r _ => ?_
    have hd : (X : PowerSeries ℤ) ^ (c + 1) ∣ Ea b hb0 (rectInf (2 * r)) - Ea b hb0 (rectPartial (2 * r) (c + 1)) := by
      rw [← map_sub]
      exact (pow_dvd_pow _ (by nlinarith)).trans (Ea_dvd b hb0 (rect_dvd (2 * r) c))
    rw [← durfee_rect_base (2 * r), mul_comm, coeffZ_congr hd, rectPartial, map_sum, mul_sum, map_sum]
    exact sum_congr rfl fun m _ => rfl
  have hL : coeff c (Dm a b) = ∑ j ∈ range (c + 1), ∑ r ∈ range (j + 1), f r (j - r) := by
    rw [Dm, coeff_mk, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← al_pair_m ha hab j, mul_sum, map_sum]
    refine sum_congr rfl fun r hr => ?_
    obtain ⟨m, rfl⟩ : ∃ m, j = r + m := ⟨j - r, by have := mem_range.mp hr; omega⟩
    show _ = Hm a b hb0 c r (r + m - r)
    rw [Hm, show r + m - r = m by omega, rectTerm, RingHom.map_mul (Ea b hb0), RingHom.map_mul (Ea b hb0),
      RingHom.map_pow (Ea b hb0), Ea_X, hEi, hEi, show r + m + r = 2 * r + m by ring, ← pow_mul,
      show b * (r + m) ^ 2 = b * r ^ 2 + b * (m ^ 2 + 2 * r * m) by ring, pow_add]
    congr 1
    ring
  rw [hL, hR, sum_range_diag_flip]
  refine sum_congr rfl fun r hr => ?_
  refine sum_subset (range_subset_range.mpr (by omega)) fun m _ hm => ?_
  simp only [mem_range, not_lt] at hm
  show Hm a b hb0 c r m = 0
  rw [Hm, rectTerm, RingHom.map_mul (Ea b hb0), RingHom.map_mul (Ea b hb0), RingHom.map_pow (Ea b hb0), Ea_X,
    ← pow_mul,
    show X ^ (b * r ^ 2) * αm a b r * (X ^ (b * (m ^ 2 + 2 * r * m)) * Ea b hb0 (Ring.inverse (qfac m))
      * Ea b hb0 (Ring.inverse (qfac (2 * r + m))))
      = X ^ (b * r ^ 2 + b * (m ^ 2 + 2 * r * m))
        * (αm a b r * Ea b hb0 (Ring.inverse (qfac m)) * Ea b hb0 (Ring.inverse (qfac (2 * r + m)))) by
      rw [pow_add]; ring]
  have hr' := mem_range.mp hr
  have h1 : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
  have h2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
  have h3 : c + 1 ≤ r + m := by omega
  exact coeffZ_Xpow_zero (by nlinarith [Nat.zero_le (2 * r * m)]) _

end RankM

lemma Pfin_1_5 (n : ℕ) : Pfin 1 5 (n + 1) = (1 - X) * Pfin 6 5 n := by
  rw [Pfin, Pfin, prod_range_succ', mul_comm]
  congr 1
  · simp
  · exact prod_congr rfl fun i _ => by congr 2; ring

lemma mul_inverse_mul {u v : PowerSeries ℤ} (hu : IsUnit u) : u * Ring.inverse (u * v) = Ring.inverse v := by
  rw [Ring.mul_inverse_rev, mul_comm (Ring.inverse v), ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

/-- **`(1 − q)(1 + φ(q)) = Σ q^{5n²}/((q⁶;q⁵)_n (q⁴;q⁵)_n)`**. -/
theorem Phi_Dm : (1 - X) * Phi 1 = Dm 1 5 := by
  ext c
  rw [coeffZ_congr (Phi_dvd 1 c), Dm, coeff_mk]
  congr 1
  rw [PhiTr, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Pfin_1_5, show (5 : ℕ) - 1 = 4 from rfl, show (1 : ℕ) + 5 = 6 from rfl]
  have hu : IsUnit (1 - X : PowerSeries ℤ) := by simpa using isUnit_one_sub_Xpow (k := 1) one_pos
  rw [show (1 - X) * (X ^ (5 * n ^ 2) * Ring.inverse ((1 - X) * Pfin 6 5 n) * Ring.inverse (Pfin 4 5 n))
      = X ^ (5 * n ^ 2) * ((1 - X) * Ring.inverse ((1 - X) * Pfin 6 5 n)) * Ring.inverse (Pfin 4 5 n) by ring,
    mul_inverse_mul hu]

end MTC
