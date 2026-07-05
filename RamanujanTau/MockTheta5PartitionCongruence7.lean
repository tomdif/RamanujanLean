/-
# Ramanujan's partition congruence `p(7n+5) ≡ 0 (mod 7)` — the full power-series proof

Mirror of the `mod 5` proof, with `(q;q)_∞⁶ = ((q;q)_∞³)² = jacobiCubeSum²`:

  * char-7 Frobenius `(q;q)_∞⁷ ≡ (q⁷;q⁷)_∞ (mod 7)`  (`frobenius_qfacInf7`),
  * `coeff_{≡5 (mod 7)}((q;q)_∞⁶) = 0`  (`coeff_qfac6_mod7`) — the Cauchy product of `jacobiCubeSum` with
    itself feeds every triangular pair `(j,k)` into the `mod 7` arithmetic heart,
  * `Ψ₇ partitionGF = Ψ₇((q;q)_∞⁶) · expand₇(Ψ₇ partitionGF)`  (`P_eq7`), no induction,

giving **`seven_dvd_coeff_partitionGF`: `7 ∣ p(7n+5)`**.  No `sorry`.
-/
import RamanujanTau.MockTheta5PartitionCongruence
import RamanujanTau.PartitionCongruenceMod7

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

noncomputable def Ψ7 : PowerSeries ℤ →+* PowerSeries (ZMod 7) := PowerSeries.map (Int.castRingHom (ZMod 7))
noncomputable def E7 : PowerSeries ℤ →+* PowerSeries ℤ := (PowerSeries.expand 7 (by norm_num)).toRingHom
noncomputable def expand7 : PowerSeries (ZMod 7) →+* PowerSeries (ZMod 7) :=
  (PowerSeries.expand 7 (by norm_num)).toRingHom

lemma E7_X : E7 X = X ^ 7 := PowerSeries.expand_X 7 (by norm_num)

private lemma coeff_Ψ7 (n : ℕ) (f : PowerSeries ℤ) :
    coeff n (Ψ7 f) = (Int.castRingHom (ZMod 7)) (coeff n f) := PowerSeries.coeff_map _ _ _

lemma coeff_expand7 (n : ℕ) (f : PowerSeries (ZMod 7)) :
    coeff n (expand7 f) = if 7 ∣ n then coeff (n / 7) f else 0 := by
  have h : expand7 f = PowerSeries.expand 7 (by norm_num) f := rfl
  rw [h, PowerSeries.coeff_expand]

/-! ### char-7 Frobenius -/

lemma E7_qfac (n : ℕ) : E7 (qfac n) = ∏ i ∈ Finset.range n, (1 - X ^ (7 * i + 7)) := by
  rw [qfac, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_sub, map_one, map_pow, E7_X, ← pow_mul, show 7 * (i + 1) = 7 * i + 7 from by ring]

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : CharP (PowerSeries (ZMod 7)) 7 :=
  charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod 7)) 7

lemma frob_factor7 (e : ℕ) : ((1 : PowerSeries (ZMod 7)) - X ^ e) ^ 7 = 1 - X ^ (7 * e) := by
  rw [sub_pow_char_of_commute _ (Commute.all _ _), one_pow, ← pow_mul, Nat.mul_comm e 7]

lemma coeff_E7_qfacInf {i N : ℕ} (h : i + 1 ≤ 7 * N) :
    coeff i (E7 qfacInf) = coeff i (E7 (qfac N)) := by
  have hdvd : (X : PowerSeries ℤ) ^ (i + 1) ∣ (E7 qfacInf - E7 (qfac N)) := by
    obtain ⟨g, hg⟩ : (X : PowerSeries ℤ) ^ N ∣ (qfacInf - qfac N) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro j hj
      rw [map_sub, coeff_qfacInf (show j + 1 ≤ N by omega), sub_self]
    rw [← map_sub, hg, map_mul, map_pow, E7_X, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _
  obtain ⟨c, hc⟩ := hdvd
  have hz : coeff i (E7 qfacInf) - coeff i (E7 (qfac N)) = 0 := by
    rw [← map_sub, hc]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ i (by omega)
  exact sub_eq_zero.mp hz

lemma frobenius_qfac7 (N : ℕ) : (Ψ7 (qfac N)) ^ 7 = Ψ7 (E7 (qfac N)) := by
  rw [E7_qfac, Ψ7, qfac, map_prod, map_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [map_sub, map_one, map_pow, PowerSeries.map_X]
  rw [frob_factor7 (i + 1), show 7 * (i + 1) = 7 * i + 7 from by ring]

private lemma coeff_congr7 {f g : PowerSeries (ZMod 7)} {m : ℕ}
    (h : (X : PowerSeries (ZMod 7)) ^ (m + 1) ∣ (f - g)) : coeff m f = coeff m g := by
  obtain ⟨c, hc⟩ := h
  have hz : coeff m f - coeff m g = 0 := by rw [← map_sub, hc, coeff_X_pow_mul']; simp
  exact sub_eq_zero.mp hz

lemma frobenius_qfacInf7 : (Ψ7 qfacInf) ^ 7 = Ψ7 (E7 qfacInf) := by
  ext m
  have hqf : (X : PowerSeries (ZMod 7)) ^ (m + 1) ∣ (Ψ7 qfacInf - Ψ7 (qfac (m + 1))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, Ψ7, PowerSeries.coeff_map, PowerSeries.coeff_map,
        coeff_qfacInf (show i + 1 ≤ m + 1 by omega), sub_self]
  have h7 : (X : PowerSeries (ZMod 7)) ^ (m + 1) ∣ ((Ψ7 qfacInf) ^ 7 - (Ψ7 (qfac (m + 1))) ^ 7) :=
    dvd_trans hqf (sub_dvd_pow_sub_pow _ _ 7)
  have hE7 : (X : PowerSeries (ZMod 7)) ^ (m + 1) ∣ (Ψ7 (E7 qfacInf) - Ψ7 (E7 (qfac (m + 1)))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, Ψ7, PowerSeries.coeff_map, PowerSeries.coeff_map,
        coeff_E7_qfacInf (show i + 1 ≤ 7 * (m + 1) by omega), sub_self]
  rw [coeff_congr7 h7, frobenius_qfac7, coeff_congr7 hE7]

/-! ### `(q;q)_∞⁶ = jacobiCubeSum²` vanishes mod 7 at exponents `≡ 5 (mod 7)` -/

private lemma Ψ7_qfac6_eq : Ψ7 (qfacInf ^ 6) = Ψ7 jacobiCubeSum * Ψ7 jacobiCubeSum := by
  rw [← map_mul, show qfacInf ^ 6 = (qfacInf ^ 3) * (qfacInf ^ 3) from by ring, jacobi_cube_identity]

lemma coeff_qfac6_mod7 {a : ℕ} (ha : a % 7 = 5) : coeff a (Ψ7 (qfacInf ^ 6)) = 0 := by
  rw [Ψ7_qfac6_eq, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  obtain ⟨x, y⟩ := p
  have hxy : x + y = a := Finset.mem_antidiagonal.mp hp
  by_cases hx : coeff x jacobiCubeSum = 0
  · rw [coeff_Ψ7, hx, map_zero, zero_mul]
  by_cases hy : coeff y jacobiCubeSum = 0
  · rw [coeff_Ψ7 y, hy, map_zero, mul_zero]
  obtain ⟨j, hj, hjval⟩ := coeff_jacobiCubeSum_value hx
  obtain ⟨k, hk, hkval⟩ := coeff_jacobiCubeSum_value hy
  have hexp : ((j : ℤ) * ((j : ℤ) + 1) + (k : ℤ) * ((k : ℤ) + 1)) ≡ 3 [ZMOD 7] := by
    rw [hj, hk, show 2 * (x : ℤ) + 2 * (y : ℤ) = 2 * (a : ℤ) from by rw [← hxy]; push_cast; ring]
    have haa : ((a : ℤ)) % 7 = 5 := by omega
    unfold Int.ModEq; omega
  have hwt : ((2 * (j : ℤ) + 1) * (2 * (k : ℤ) + 1)) ≡ 0 [ZMOD 7] :=
    RamanujanTau.PartitionCongruenceMod7.jacobi_weight_prod_dvd_of_exponent hexp
  have hdvd : (7 : ℤ) ∣ coeff x jacobiCubeSum * coeff y jacobiCubeSum := by
    rw [hjval, hkval]
    obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp hwt
    exact ⟨(-1) ^ j * (-1) ^ k * c, by linear_combination ((-1 : ℤ) ^ j * (-1 : ℤ) ^ k) * hc⟩
  rw [coeff_Ψ7, coeff_Ψ7, ← map_mul]
  show ((coeff x jacobiCubeSum * coeff y jacobiCubeSum : ℤ) : ZMod 7) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hdvd

/-! ### the assembly -/

lemma g7_unit : IsUnit (Ψ7 qfacInf) := isUnit_qfacInf.map Ψ7

lemma g7_pow7 : (Ψ7 qfacInf) ^ 7 = expand7 (Ψ7 qfacInf) := by
  rw [frobenius_qfacInf7]
  ext n
  rw [coeff_Ψ7, coeff_expand7]
  have h : E7 qfacInf = PowerSeries.expand 7 (by norm_num) qfacInf := rfl
  rw [h, PowerSeries.coeff_expand]
  split_ifs with hd
  · rw [coeff_Ψ7]
  · simp

lemma Ψ7_partitionGF_mul : Ψ7 partitionGF * Ψ7 qfacInf = 1 := by
  rw [← map_mul, partitionGF, Ring.inverse_mul_cancel _ isUnit_qfacInf, map_one]

lemma P_eq7 : Ψ7 partitionGF = Ψ7 (qfacInf ^ 6) * expand7 (Ψ7 partitionGF) := by
  set g := Ψ7 qfacInf with hg
  set P := Ψ7 partitionGF with hP
  have hu : IsUnit g := g7_unit
  have hPg : P * g = 1 := Ψ7_partitionGF_mul
  have hgP : g * P = 1 := by rw [mul_comm]; exact hPg
  have hgexp : g ^ 7 * expand7 P = 1 := by rw [g7_pow7, ← map_mul, hgP, map_one]
  have hgx : g * (g ^ 6 * expand7 P) = 1 := by
    rw [← mul_assoc, show g * g ^ 6 = g ^ 7 from by ring]; exact hgexp
  have hPinv : P = Ring.inverse g := by
    calc P = P * 1 := (mul_one _).symm
      _ = P * (g * Ring.inverse g) := by rw [Ring.mul_inverse_cancel g hu]
      _ = (P * g) * Ring.inverse g := by ring
      _ = Ring.inverse g := by rw [hPg, one_mul]
  rw [show Ψ7 (qfacInf ^ 6) = g ^ 6 from by rw [map_pow]]
  conv_lhs => rw [hPinv]
  symm
  calc g ^ 6 * expand7 P = 1 * (g ^ 6 * expand7 P) := (one_mul _).symm
    _ = (Ring.inverse g * g) * (g ^ 6 * expand7 P) := by rw [Ring.inverse_mul_cancel g hu]
    _ = Ring.inverse g * (g * (g ^ 6 * expand7 P)) := by ring
    _ = Ring.inverse g := by rw [hgx, mul_one]

/-- **Ramanujan's congruence, reduced form:** every `q^{7n+5}` coefficient of `1/(q;q)_∞` is `0` mod 7. -/
theorem partition_congruence_mod7 (n : ℕ) : coeff (7 * n + 5) (Ψ7 partitionGF) = 0 := by
  rw [P_eq7, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  obtain ⟨a, b⟩ := p
  have hab : a + b = 7 * n + 5 := Finset.mem_antidiagonal.mp hp
  by_cases hb : 7 ∣ b
  · obtain ⟨j, rfl⟩ := hb
    rw [coeff_qfac6_mod7 (show a % 7 = 5 by omega), zero_mul]
  · rw [coeff_expand7, if_neg hb, mul_zero]

/-- **Ramanujan's partition congruence** `7 ∣ p(7n+5)`, where `p(n) = coeff n (1/(q;q)_∞)`. -/
theorem seven_dvd_coeff_partitionGF (n : ℕ) : (7 : ℤ) ∣ coeff (7 * n + 5) partitionGF := by
  have h : ((coeff (7 * n + 5) partitionGF : ℤ) : ZMod 7) = 0 := by
    have hh := partition_congruence_mod7 n; rwa [coeff_Ψ7] at hh
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h

end MockTheta5.JTP
