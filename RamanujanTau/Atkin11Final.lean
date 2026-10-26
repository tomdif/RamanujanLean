/-
# Ramanujan's conjecture for powers of 11 (Atkin 1967), from the Atkin–Gordon inputs

  `Inputs → (24m ≡ 1 (mod 11ʳ) → 11ʳ ∣ p(m))`.

* `z(q)z(q¹¹) = φ¹²` turns `U(φ^λ J_{5a+i})` into `z^{-a} U(φ^{λ+12a} J_i)` (`U_J`), so all rows are
  shifted Gordon rows `C^{λ+12a}_{i, ·+5a}`.
* `L₀ = 1`, `L_{r+1} = U(φ^{λ_r} L_r)` (`λ_r = 1, 0, 1, 0, …`) satisfies `L_r = q·W_r·Σ_n p(11ʳn + μ_r)qⁿ`
  with `W_r ∈ {E(q), E(q¹¹)}`, and `L_r = Σ_{ν≥1} a_{r,ν} J_ν` with `11^{r + ⌊(ν−1)/2⌋} ∣ a_{r,ν}`.
-/
import RamanujanTau.Atkin11Matrix
import RamanujanTau.MockTheta5PartitionCount

set_option autoImplicit false

namespace Atkin11
open PowerSeries Finset

/-! ### `z(q) z(q¹¹) = φ¹²` and the shift -/

lemma map_inverse' (f : PS →+* PS) {u : PS} (hu : IsUnit u) : f (Ring.inverse u) = Ring.inverse (f u) := by
  have h1 : f u * f (Ring.inverse u) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]
  calc f (Ring.inverse u) = (Ring.inverse (f u) * f u) * f (Ring.inverse u) := by
        rw [Ring.inverse_mul_cancel _ (hu.map f), one_mul]
    _ = Ring.inverse (f u) * (f u * f (Ring.inverse u)) := by ring
    _ = Ring.inverse (f u) := by rw [h1, mul_one]

lemma V_inverse_E1 : V (Ring.inverse E1) = Ring.inverse E11 := map_inverse' _ isUnit_E1

lemma V_X : V (X : PS) = X ^ 11 := by simp [ex]

theorem z_mul_Vz : z * V z = φ ^ 12 := by
  have h : E11 * Ring.inverse E11 = 1 := Ring.mul_inverse_cancel _ isUnit_E11
  simp only [z, φ, map_mul, map_pow, V_X, V_inverse_E1, show V E11 = E121 from rfl]
  calc X ^ 5 * E11 ^ 12 * Ring.inverse E1 ^ 12 * ((X ^ 11) ^ 5 * E121 ^ 12 * Ring.inverse E11 ^ 12)
      = (X ^ 5 * E121 * Ring.inverse E1) ^ 12 * (E11 * Ring.inverse E11) ^ 12 := by ring
    _ = (X ^ 5 * E121 * Ring.inverse E1) ^ 12 := by rw [h, one_pow, mul_one]

lemma isUnit_inverse {u : PS} (hu : IsUnit u) : IsUnit (Ring.inverse u) := by
  obtain ⟨v, rfl⟩ := hu; rw [Ring.inverse_unit]; exact v⁻¹.isUnit

lemma z_ne_zero : z ≠ 0 := by
  have hu : IsUnit (E11 ^ 12 * Ring.inverse E1 ^ 12) := (isUnit_E11.pow 12).mul ((isUnit_inverse isUnit_E1).pow 12)
  rw [z, mul_assoc]
  exact mul_ne_zero (pow_ne_zero 5 X_ne_zero) hu.ne_zero

lemma J_add_mul_five (μ a : ℕ) : J (μ + 5 * a) = z ^ a * J μ := by
  induction a with
  | zero => simp
  | succ a ih => rw [show μ + 5 * (a + 1) = μ + 5 * a + 5 by ring, J_add_five, ih, pow_succ]; ring

lemma lc_mapDomain (a : ℕ) (g : ℕ →₀ ℤ) : lc (Finsupp.mapDomain (· + 5 * a) g) = z ^ a * lc g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg, mul_add]
  | single ν c =>
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      J_add_mul_five, mul_smul_comm]

lemma add_right_inj' (k : ℕ) : Function.Injective (· + k : ℕ → ℕ) := fun _ _ h => by simpa using h

/-- the shifted Gordon row of `U(φ^λ J_ν)`. -/
noncomputable def cRow (lam ν : ℕ) : ℕ →₀ ℤ :=
  Finsupp.comapDomain (· + 5 * (ν / 5)) (C (lam + 12 * (ν / 5)) (ν % 5))
    ((add_right_inj' _).injOn)

lemma cRow_apply (lam ν μ : ℕ) : cRow lam ν μ = C (lam + 12 * (ν / 5)) (ν % 5) (μ + 5 * (ν / 5)) := rfl

variable (hI : Inputs)
include hI

/-- **`U(φ^λ J_ν) = Σ_μ C^{λ+12a}_{i,μ+5a} J_μ`** (`ν = 5a + i`). -/
theorem U_J (lam ν : ℕ) : U (φ ^ lam * J ν) = lc (cRow lam ν) := by
  set a := ν / 5
  set i := ν % 5
  have hi : i < 5 := Nat.mod_lt _ (by norm_num)
  have hC := U_C hI (lam + 12 * a) i hi
  -- the row is supported on `μ ≥ 5a`
  have hsupp : ↑(C (lam + 12 * a) i).support ⊆ Set.range (· + 5 * a : ℕ → ℕ) := by
    intro μ hμ
    have := C_support (lam + 12 * a) i hi μ (Finsupp.mem_support_iff.mp hμ)
    exact ⟨μ - 5 * a, by simp only; omega⟩
  have hmap : Finsupp.mapDomain (· + 5 * a) (cRow lam ν) = C (lam + 12 * a) i :=
    Finsupp.mapDomain_comapDomain _ (add_right_inj' _) _ hsupp
  rw [← hmap, lc_mapDomain] at hC
  have hJ : J ν = z ^ a * J i := by
    rw [J_eq, J_small i hi]
  have e : φ ^ (lam + 12 * a) * J i = V (z ^ a) * (φ ^ lam * J ν) := by
    rw [hJ, pow_add, pow_mul, ← z_mul_Vz, map_pow, mul_pow]; ring
  rw [e, U_V_mul] at hC
  exact mul_left_cancel₀ (pow_ne_zero _ z_ne_zero) hC

omit hI in
/-- the coefficient-level step of the final induction. -/
theorem final_ineq (lam : ℕ) (hlam : lam ≤ 1) (ν μ : ℕ) (hν : 1 ≤ ν) (hμ : 1 ≤ μ) :
    1 + (μ - 1) / 2 ≤ (ν - 1) / 2 + (B ((lam + 12 * (ν / 5) : ℕ) : ℤ) (ν % 5) (μ + 5 * (ν / 5))).toNat := by
  unfold B
  rw [show (μ + 5 * (ν / 5)) % 5 = μ % 5 by omega]
  have hi : ν % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hs : μ % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hν5 : ν = 5 * (ν / 5) + ν % 5 := (Nat.div_add_mod ν 5).symm
  have hμ5 : μ = 5 * (μ / 5) + μ % 5 := (Nat.div_add_mod μ 5).symm
  generalize ν % 5 = i at *
  generalize μ % 5 = t at *
  push_cast
  interval_cases i <;> interval_cases t <;> simp only [δ, δtab] <;> norm_num <;> omega

/-! ### the generating functions `L_r` -/

omit hI in
/-- `λ_r = 1, 0, 1, 0, …`. -/
def lamOf (r : ℕ) : ℕ := if r % 2 = 0 then 1 else 0

omit hI in
noncomputable def L : ℕ → PS
  | 0 => 1
  | r + 1 => U (φ ^ lamOf r * L r)

omit hI in
lemma J_zero : J 0 = 1 := by simp [J, gi]

omit hI in
lemma seed10 : seedRows.getD 5 [] = [(1, 11), (2, 242), (3, 1331), (5, 14641)] := by decide

/-- **the 11-adic induction**: `L_r = Σ_{ν≥1} a_ν J_ν` with `11^{r + ⌊(ν−1)/2⌋} ∣ a_ν`. -/
theorem L_expansion (r : ℕ) (hr : 1 ≤ r) :
    ∃ a : ℕ →₀ ℤ, L r = lc a ∧ a 0 = 0 ∧ ∀ ν, 1 ≤ ν → (11 : ℤ) ^ (r + (ν - 1) / 2) ∣ a ν := by
  induction r, hr using Nat.le_induction with
  | base =>
    refine ⟨seedF 1 0, ?_, ?_, fun ν hν => ?_⟩
    · rw [L, lamOf, if_pos rfl, L, ← J_zero, ← C_lt (by norm_num : 1 < 11)]
      simpa using U_C hI 1 0 (by norm_num)
    · by_contra h
      rw [seedF, show 5 * 1 + 0 = 5 from rfl, seed10] at h
      obtain ⟨p, hp, e⟩ := ofList_ne_zero _ _ h
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp at e
    · rw [seedF, show 5 * 1 + 0 = 5 from rfl, seed10]
      refine ofList_dvd _ _ fun p hp e => ?_
      subst e
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
  | succ r hr ih =>
    obtain ⟨a, hL, ha0, hdiv⟩ := ih
    have hlam : lamOf r ≤ 1 := by unfold lamOf; split_ifs <;> norm_num
    refine ⟨Finsupp.linearCombination ℤ (cRow (lamOf r)) a, ?_, ?_, fun μ hμ => ?_⟩
    · rw [L, hL]
      clear hL ha0 hdiv
      induction a using Finsupp.induction_linear with
      | zero => simp [U, PowerSeries.ext_iff]
      | add f g hf hg => rw [map_add, mul_add, U_add, hf, hg, map_add, map_add]
      | single ν c =>
        rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, mul_smul_comm, U_smul,
          U_J hI, map_zsmul]
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
      refine sum_eq_zero fun ν hν => ?_
      have hν0 : ν ≠ 0 := fun h => Finsupp.mem_support_iff.mp hν (by rw [h, ha0])
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine mul_eq_zero_of_right _ ?_
      by_contra hc
      rw [cRow_apply, zero_add] at hc
      have := C_support _ (ν % 5) (Nat.mod_lt _ (by norm_num)) _ hc
      have h5 := Nat.div_add_mod ν 5
      have : lamOf r ≥ 0 := Nat.zero_le _
      omega
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
      refine Finset.dvd_sum fun ν hν => ?_
      have hν0 : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr fun h => Finsupp.mem_support_iff.mp hν (by rw [h, ha0])
      rw [Finsupp.smul_apply, smul_eq_mul, cRow_apply]
      have h1 := hdiv ν hν0
      have h2 := C_dvd (lamOf r + 12 * (ν / 5)) (ν % 5) (Nat.mod_lt _ (by norm_num)) (μ + 5 * (ν / 5))
      have h3 := final_ineq (lamOf r) hlam ν μ hν0 hμ
      refine (pow_dvd_pow _ (by omega : r + 1 + (μ - 1) / 2 ≤ (r + (ν - 1) / 2) +
        (B ((lamOf r + 12 * (ν / 5) : ℕ) : ℤ) (ν % 5) (μ + 5 * (ν / 5))).toNat)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul h1 h2

/-! ### the partition generating functions -/

omit hI in
/-- `μ₁ = 6`, `μ_{r+1} = μ_r + (10 or 5)·11ʳ`; `μ_r = (1 + 13·11ʳ)/24` (r odd), `(1 + 23·11ʳ)/24` (r even). -/
def mu : ℕ → ℕ
  | 0 => 0
  | 1 => 6
  | r + 2 => mu (r + 1) + (if (r + 1) % 2 = 1 then 10 else 5) * 11 ^ (r + 1)

omit hI in
lemma mu_succ {r : ℕ} (hr : 1 ≤ r) : mu (r + 1) = mu r + (if r % 2 = 1 then 10 else 5) * 11 ^ r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rfl

omit hI in
lemma mu_spec {r : ℕ} (hr : 1 ≤ r) : 24 * mu r = 1 + (if r % 2 = 1 then 13 else 23) * 11 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [mu_succ hr, pow_succ]
    generalize 11 ^ r = P at *
    split_ifs at ih ⊢ <;> omega

omit hI in
lemma mu_lt {r : ℕ} (hr : 1 ≤ r) : mu r < 11 ^ r := by
  have h := mu_spec hr
  have hP : 11 ≤ 11 ^ r := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 11) hr
  generalize 11 ^ r = P at h hP ⊢
  split_ifs at h <;> omega

omit hI in
noncomputable def W (r : ℕ) : PS := if r % 2 = 1 then E11 else E1

omit hI in
noncomputable def A (r : ℕ) : PS := PowerSeries.mk fun n => coeff (11 ^ r * n + mu r) MockTheta5.JTP.partitionGF

omit hI in
lemma U_Xpow (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 11) (F : PS) :
    U (X ^ k * F) = X * PowerSeries.mk fun n => coeff (11 * n + (11 - k)) F := by
  ext n
  rw [coeff_U, coeff_X_pow_mul']
  rcases n with _ | m
  · rw [if_neg (by omega)]; simp
  · rw [if_pos (by omega), mul_comm X, coeff_succ_mul_X, coeff_mk]
    rw [show 11 * (m + 1) - k = 11 * m + (11 - k) by omega]

omit hI in
lemma partitionGF_eq : MockTheta5.JTP.partitionGF = Ring.inverse E1 := rfl

omit hI in
theorem L_part (r : ℕ) (hr : 1 ≤ r) : L r = X * W r * A r := by
  induction r, hr using Nat.le_induction with
  | base =>
    rw [L, lamOf, if_pos rfl, L, pow_one, mul_one, φ, show E121 = V E11 from rfl,
      show X ^ 5 * V E11 * Ring.inverse E1 = V E11 * (X ^ 5 * MockTheta5.JTP.partitionGF) by rw [partitionGF_eq]; ring,
      U_V_mul, U_Xpow 5 (by norm_num) (by norm_num), W, if_pos rfl, A]
    simp only [mu, pow_one]; ring_nf
  | succ r hr ih =>
    have hA : ∀ c : ℕ, (PowerSeries.mk fun n => coeff (11 * n + c) (A r)) =
        PowerSeries.mk fun n => coeff (11 ^ (r + 1) * n + (mu r + c * 11 ^ r)) MockTheta5.JTP.partitionGF := by
      intro c; ext n; simp only [A, coeff_mk]; congr 1; rw [pow_succ]; ring
    rw [L, ih]
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · rw [lamOf, if_pos h, pow_one, W, if_neg (by omega), φ, show E121 = V E11 from rfl]
      have e : X ^ 5 * V E11 * Ring.inverse E1 * (X * E1 * A r) = V E11 * (X ^ 6 * A r) := by
        have := Ring.inverse_mul_cancel _ isUnit_E1
        linear_combination (X ^ 6 * V E11 * A r) * this
      rw [e, U_V_mul, U_Xpow 6 (by norm_num) (by norm_num), hA, W, if_pos (by omega), A, mu_succ hr,
        if_neg (by omega)]
      ring
    · rw [lamOf, if_neg (by omega), pow_zero, one_mul, W, if_pos h, show E11 = V E1 from rfl,
        show X * V E1 * A r = V E1 * (X ^ 1 * A r) by ring, U_V_mul, U_Xpow 1 le_rfl (by norm_num), hA, W,
        if_neg (by omega), A, mu_succ hr, if_pos h]
      norm_num; ring

/-! ### the theorem -/

omit hI in
lemma X_dvd_J {ν : ℕ} (hν : 1 ≤ ν) : (X : PS) ∣ J ν := by
  have hz : (X : PS) ∣ z := ⟨X ^ 4 * E11 ^ 12 * Ring.inverse E1 ^ 12, by rw [z]; ring⟩
  have h2 : (X : PS) ∣ g2 := X_dvd_iff.mpr constantCoeff_g2
  have h3 : (X : PS) ∣ g3 := by
    rw [g3]; exact dvd_mul_of_dvd_left (dvd_add (dvd_pow h2 (by norm_num)) (dvd_mul_of_dvd_right hz _)) _
  rw [J_eq]
  rcases Nat.eq_zero_or_pos (ν / 5) with h0 | h0
  · refine dvd_mul_of_dvd_right ?_ _
    have : ν % 5 ≠ 0 := by omega
    have h5 : ν % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : ν % 5
    · exact absurd rfl this
    · exact h2
    · exact h3
    · exact dvd_sub (dvd_pow h2 (by norm_num)) h3
    · exact dvd_mul_of_dvd_left h2 _
  · exact dvd_mul_of_dvd_left (dvd_pow hz (by omega)) _

omit hI in
lemma lc_dvd (a : ℕ →₀ ℤ) (ha0 : a 0 = 0) (d : ℤ) (hd : ∀ ν, 1 ≤ ν → d ∣ a ν) : (X * (d : PS)) ∣ lc a := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.dvd_sum fun ν hν => ?_
  have hν0 : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr fun h => Finsupp.mem_support_iff.mp hν (by rw [h, ha0])
  rw [zsmul_eq_mul, mul_comm X]
  exact mul_dvd_mul (Int.cast_dvd_cast _ _ (hd ν hν0)) (X_dvd_J hν0)

/-- **`11ʳ ∣ p(11ʳn + μ_r)`**. -/
theorem A_dvd (r : ℕ) (hr : 1 ≤ r) (n : ℕ) : (11 : ℤ) ^ r ∣ coeff n (A r) := by
  obtain ⟨a, hL, ha0, hdiv⟩ := L_expansion hI r hr
  obtain ⟨N, hN⟩ := lc_dvd a ha0 ((11 : ℤ) ^ r) fun ν hν => (pow_dvd_pow _ (by omega)).trans (hdiv ν hν)
  rw [← hL, L_part r hr, mul_assoc, mul_assoc] at hN
  have h1 := mul_left_cancel₀ X_ne_zero hN
  have hW : IsUnit (W r) := by unfold W; split_ifs; exacts [isUnit_E11, isUnit_E1]
  have h2 : A r = ((11 : ℤ) ^ r : PS) * (Ring.inverse (W r) * N) := by
    calc A r = Ring.inverse (W r) * (W r * A r) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hW, one_mul]
      _ = _ := by rw [h1]; push_cast; ring
  rw [h2, show ((11 : ℤ) ^ r : PS) = PowerSeries.C ((11 : ℤ) ^ r) by simp, coeff_C_mul]
  exact dvd_mul_right _ _

/-- **Ramanujan's conjecture for powers of 11** (Atkin 1967), from the Atkin–Gordon inputs:
if `24m ≡ 1 (mod 11ʳ)`, `r ≥ 1`, then `11ʳ ∣ p(m)`. -/
theorem ramanujan_pow11 {r : ℕ} (hr : 1 ≤ r) (m : ℕ) (hm : 24 * m ≡ 1 [MOD 11 ^ r]) :
    11 ^ r ∣ Fintype.card (Nat.Partition m) := by
  have hd24 : 24 * mu r ≡ 1 [MOD 11 ^ r] := by
    rw [mu_spec hr]
    split_ifs <;> simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hcop : Nat.gcd (11 ^ r) 24 = 1 := Nat.Coprime.pow_left _ (by decide)
  have hcong : m ≡ mu r [MOD 11 ^ r] := Nat.ModEq.cancel_left_of_coprime hcop (hm.trans hd24.symm)
  have hlt := mu_lt hr
  have hge : mu r ≤ m := by
    by_contra h
    have := Nat.ModEq.eq_of_lt_of_lt hcong (by omega) hlt
    omega
  obtain ⟨n, hn⟩ : ∃ n, m = 11 ^ r * n + mu r := by
    obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hge).mp hcong.symm
    exact ⟨n, by omega⟩
  have h := A_dvd hI r hr n
  rw [A, coeff_mk, ← hn, MockTheta5.JTP.coeff_partitionGF_eq_card] at h
  exact_mod_cast h

end Atkin11
