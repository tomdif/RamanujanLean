/-
# Watson's congruences for powers of 7, part 3: the stage transitions

`L_{2α} = (1/E)·Σ_s b_s τˢ`, `L_{2α+1} = (1/E(q⁷))·Σ_l a_l τˡ` with
`a_l = Σ_s b_s m_{4s+1, l+s}` and `b_s = Σ_l a_l m_{4l, s+l}`.
-/
import RamanujanTau.Pow7Mod

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey

/-- the odd-stage coefficients from the even-stage polynomial. -/
noncomputable def Aform7 (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ l ∈ range (7 * P.natDegree + 3),
    Polynomial.C (∑ s ∈ range (7 * l - 1), P.coeff s * mc7 (4 * s + 1) (l + s)) * Polynomial.X ^ l

/-- the even-stage coefficients from the odd-stage polynomial. -/
noncomputable def Bform7 (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ s ∈ range (7 * P.natDegree + 1),
    Polynomial.C (∑ l ∈ range (7 * s + 1), P.coeff l * mc7 (4 * l) (s + l)) * Polynomial.X ^ s

lemma coeff_Pm7 (k j : ℕ) : (Pm7 k).coeff j = mc7 k j := rfl

lemma coeff_Aform7 (P : Polynomial ℤ) (l : ℕ) :
    (Aform7 P).coeff l = if l < 7 * P.natDegree + 3 then ∑ s ∈ range (7 * l - 1), P.coeff s * mc7 (4 * s + 1) (l + s)
      else 0 := by
  rw [Aform7, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (7 * P.natDegree + 3)) l]
  simp [mem_range]

lemma coeff_Bform7 (P : Polynomial ℤ) (s : ℕ) :
    (Bform7 P).coeff s = if s < 7 * P.natDegree + 1 then ∑ l ∈ range (7 * s + 1), P.coeff l * mc7 (4 * l) (s + l)
      else 0 := by
  rw [Bform7, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (7 * P.natDegree + 1)) s]
  simp [mem_range]

/-- the reindexing identity, even → odd. -/
lemma reindex_A7 (P : Polynomial ℤ) :
    ∑ s ∈ range (P.natDegree + 1), Polynomial.C (P.coeff s) * Polynomial.X ^ (P.natDegree - s) * Pm7 (4 * s + 1)
      = Polynomial.X ^ P.natDegree * Aform7 P := by
  set M := P.natDegree
  ext n
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']
  simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', coeff_Pm7]
  split_ifs with hn
  · rw [coeff_Aform7]
    split_ifs with hl
    · -- both sides are `Σ_s P_s m_{6s+1, n−M+s}` over different ranges
      rw [← sum_subset (s₁ := range (M + 1) ∩ range (7 * (n - M) - 1)) inter_subset_left ?_,
        ← sum_subset (s₁ := range (M + 1) ∩ range (7 * (n - M) - 1)) inter_subset_right ?_]
      · refine sum_congr rfl fun s hs => ?_
        simp only [mem_inter, mem_range] at hs
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega, mc7_low _ _ (by omega), mul_zero]
    · refine sum_eq_zero fun s hs => ?_
      simp only [mem_range] at hs
      rw [if_pos (by omega), mc7_high _ _ (by omega), mul_zero]
  · refine sum_eq_zero fun s hs => ?_
    simp only [mem_range] at hs
    split_ifs with h
    · rw [mc7_low _ _ (by omega), mul_zero]
    · exact mul_zero _

/-- the reindexing identity, odd → even. -/
lemma reindex_B7 (P : Polynomial ℤ) :
    ∑ l ∈ range (P.natDegree + 1), Polynomial.C (P.coeff l) * Polynomial.X ^ (P.natDegree - l) * Pm7 (4 * l)
      = Polynomial.X ^ P.natDegree * Bform7 P := by
  set M := P.natDegree
  ext n
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']
  simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', coeff_Pm7]
  split_ifs with hn
  · rw [coeff_Bform7]
    split_ifs with hl
    · rw [← sum_subset (s₁ := range (M + 1) ∩ range (7 * (n - M) + 1)) inter_subset_left ?_,
        ← sum_subset (s₁ := range (M + 1) ∩ range (7 * (n - M) + 1)) inter_subset_right ?_]
      · refine sum_congr rfl fun s hs => ?_
        simp only [mem_inter, mem_range] at hs
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega, mc7_low _ _ (by omega), mul_zero]
    · refine sum_eq_zero fun s hs => ?_
      simp only [mem_range] at hs
      rw [if_pos (by omega), mc7_high _ _ (by omega), mul_zero]
  · refine sum_eq_zero fun s hs => ?_
    simp only [mem_range] at hs
    split_ifs with h
    · rw [mc7_low _ _ (by omega), mul_zero]
    · exact mul_zero _

lemma dis7_zero (r : ℕ) : dis7 r (0 : PowerSeries ℤ) = 0 := by ext n; simp [dis7]

lemma dis7_sum7s {ι : Type*} (r : ℕ) (t : Finset ι) (f : ι → PowerSeries ℤ) :
    dis7 r (∑ i ∈ t, f i) = ∑ i ∈ t, dis7 r (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [dis7_zero]
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, dis7_add, ih]

lemma dis7_intCast_mul (r : ℕ) (c : ℤ) (F : PowerSeries ℤ) : dis7 r ((c : PowerSeries ℤ) * F) = c * dis7 r F := by
  rw [show (c : PowerSeries ℤ) = C c by simp, dis7_C_mul]

lemma inv_Fser_ne : Ring.inverse Fser ≠ 0 := by
  intro h; have := Fser_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this

/-- `y·E(q) = q²·E(q⁴⁹)`. -/
lemma Y7_mul_E : Y7 * qfacInf = X ^ 2 * E7 eQ7 := by
  have hD := qfacInf_dissection7
  have hF := factor_mul_Qpoly7
  have hN : E7 Nser * E7 (Ring.inverse Nser) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ (by rw [← Fser_sq]; exact isUnit_Fser.pow 2), map_one]
  rw [Y7]
  conv_lhs => rw [hD]
  linear_combination X ^ 2 * E7 eQ7 * E7 (Ring.inverse Nser) * hF + X ^ 2 * E7 eQ7 * hN

lemma eQ7_pow4_Fser' : eQ7 ^ 4 * Fser = qfacInf ^ 4 := eQ7_pow4_mul_Fser

/-- `E7(1/F)·eQ⁴ = E(q⁴⁹)⁴`. -/
lemma E7_inv_Fser : E7 (Ring.inverse Fser) * eQ7 ^ 4 = E7 eQ7 ^ 4 := by
  have h := congrArg E7 eQ7_pow4_mul_Fser
  simp only [map_mul, map_pow] at h
  have hN : E7 Fser * E7 (Ring.inverse Fser) = 1 := by rw [← map_mul, Fser_mul_inv, map_one]
  rw [show E7 qfacInf = eQ7 from rfl] at h
  linear_combination -(E7 (Ring.inverse Fser) * h) + E7 eQ7 ^ 4 * hN

/-- **`τ(q)·τ(q⁷) = y⁴`**. -/
lemma tau7_mul_E7 : tau7 * E7 tau7 = Y7 ^ 4 := by
  have hu : IsUnit (qfacInf ^ 4) := isUnit_qfacInf.pow 4
  apply (hu.mul_left_inj).mp
  have h1 : (Y7 * qfacInf) ^ 4 = (X ^ 2 * E7 eQ7) ^ 4 := by rw [Y7_mul_E]
  have h2 := E7_inv_Fser
  have h3 := eQ7_pow4_mul_Fser
  have hn := Fser_mul_inv
  simp only [tau7, map_mul, E7_X]
  linear_combination -h1 + X ^ 8 * h2 + X ^ 8 * E7 (Ring.inverse Fser) * eQ7 ^ 4 * hn
    - X ^ 8 * E7 (Ring.inverse Fser) * Ring.inverse Fser * h3

lemma tau7_ne : tau7 ≠ 0 := mul_ne_zero X_ne_zero inv_Fser_ne

/-- `q²/E = y/E(q⁴⁹)`. -/
lemma X2_mul_pGF : X ^ 2 * partitionGF = E7 (Ring.inverse eQ7) * Y7 := by
  have h := Y7_mul_E
  have h1 : E7 eQ7 * E7 (Ring.inverse eQ7) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel _ isUnit_eQ7, map_one]
  have h2 : qfacInf * partitionGF = 1 := Ring.mul_inverse_cancel _ isUnit_qfacInf
  linear_combination -(X ^ 2 * partitionGF) * h1 - E7 (Ring.inverse eQ7) * partitionGF * h + E7 (Ring.inverse eQ7) * Y7 * h2

lemma E7_tau7_pow {M s : ℕ} (hs : s ≤ M) : E7 tau7 ^ M * tau7 ^ s = E7 tau7 ^ (M - s) * Y7 ^ (4 * s) := by
  rw [show E7 tau7 ^ M = E7 tau7 ^ (M - s) * E7 tau7 ^ s by rw [← pow_add]; congr 1; omega, mul_assoc,
    ← mul_pow, mul_comm (E7 tau7), tau7_mul_E7, ← pow_mul]

/-- **transition even → odd**: `U₇(q²·(1/E)·P(τ)) = (1/E(q⁷))·(A P)(τ)`. -/
theorem trans_even7 (P : Polynomial ℤ) :
    dis7 0 (X ^ 2 * partitionGF * Polynomial.aeval tau7 P) = Ring.inverse eQ7 * Polynomial.aeval tau7 (Aform7 P) := by
  set M := P.natDegree
  apply mul_left_cancel₀ (pow_ne_zero M tau7_ne)
  have key : E7 (tau7 ^ M) * (X ^ 2 * partitionGF * Polynomial.aeval tau7 P)
      = E7 (Ring.inverse eQ7) * ∑ s ∈ range (M + 1), E7 ((P.coeff s : PowerSeries ℤ) * tau7 ^ (M - s))
        * Y7 ^ (4 * s + 1) := by
    rw [Polynomial.aeval_eq_sum_range, X2_mul_pGF, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun s hs => ?_
    have hs' : s ≤ M := by simp at hs; omega
    simp only [map_mul, map_pow, map_intCast, Algebra.smul_def, algebraMap_int_eq, eq_intCast]
    rw [show E7 tau7 ^ M * (E7 (Ring.inverse eQ7) * Y7 * ((P.coeff s : PowerSeries ℤ) * tau7 ^ s))
        = E7 (Ring.inverse eQ7) * Y7 * (P.coeff s : PowerSeries ℤ) * (E7 tau7 ^ M * tau7 ^ s) by ring,
      E7_tau7_pow hs', pow_succ]
    ring
  rw [← dis7_E7_mul 0 (by norm_num), key, dis7_E7_mul 0 (by norm_num), dis7_sum7s]
  simp_rw [dis7_E7_mul 0 (by norm_num), Y7_dis]
  rw [mul_left_comm, show tau7 ^ M * Polynomial.aeval tau7 (Aform7 P)
      = Polynomial.aeval tau7 (Polynomial.X ^ M * Aform7 P) by simp, ← reindex_A7, map_sum]
  refine congrArg _ (sum_congr rfl fun s _ => ?_)
  simp only [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
  rfl

/-- **transition odd → even**: `U₇((1/E(q⁷))·P(τ)) = (1/E)·(B P)(τ)`. -/
theorem trans_odd7 (P : Polynomial ℤ) :
    dis7 0 (Ring.inverse eQ7 * Polynomial.aeval tau7 P) = partitionGF * Polynomial.aeval tau7 (Bform7 P) := by
  set M := P.natDegree
  apply mul_left_cancel₀ (pow_ne_zero M tau7_ne)
  have hinv : Ring.inverse eQ7 = E7 partitionGF := by rw [eQ7, E7_inverse isUnit_qfacInf]; rfl
  have key : E7 (tau7 ^ M) * (Ring.inverse eQ7 * Polynomial.aeval tau7 P)
      = E7 partitionGF * ∑ l ∈ range (M + 1), E7 ((P.coeff l : PowerSeries ℤ) * tau7 ^ (M - l)) * Y7 ^ (4 * l) := by
    rw [Polynomial.aeval_eq_sum_range, hinv, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun l hl => ?_
    have hl' : l ≤ M := by simp at hl; omega
    simp only [map_mul, map_pow, map_intCast, Algebra.smul_def, eq_intCast]
    rw [show E7 tau7 ^ M * (E7 partitionGF * ((P.coeff l : PowerSeries ℤ) * tau7 ^ l))
        = E7 partitionGF * (P.coeff l : PowerSeries ℤ) * (E7 tau7 ^ M * tau7 ^ l) by ring, E7_tau7_pow hl']
    ring
  rw [← dis7_E7_mul 0 (by norm_num), key, dis7_E7_mul 0 (by norm_num), dis7_sum7s]
  simp_rw [dis7_E7_mul 0 (by norm_num), Y7_dis]
  rw [mul_left_comm, show tau7 ^ M * Polynomial.aeval tau7 (Bform7 P)
      = Polynomial.aeval tau7 (Polynomial.X ^ M * Bform7 P) by simp, ← reindex_B7, map_sum]
  refine congrArg _ (sum_congr rfl fun l _ => ?_)
  simp only [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
  rfl

end MockTheta5.JTP
