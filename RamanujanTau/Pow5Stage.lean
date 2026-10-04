/-
# Ramanujan's conjecture for powers of 5, part 2: the stage transitions

`L_{2α} = (1/E)·Σ_s b_s τˢ`, `L_{2α+1} = (1/E(q⁵))·Σ_l a_l τˡ` with
`a_l = Σ_s b_s m_{6s+1, l+s}` and `b_s = Σ_l a_l m_{6l, s+l}`.
-/
import RamanujanTau.Pow5

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey

/-- the odd-stage coefficients from the even-stage polynomial. -/
noncomputable def Aform (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ l ∈ range (6 * P.natDegree + 2),
    Polynomial.C (∑ s ∈ range (5 * l), P.coeff s * mc (6 * s + 1) (l + s)) * Polynomial.X ^ l

/-- the even-stage coefficients from the odd-stage polynomial. -/
noncomputable def Bform (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ s ∈ range (6 * P.natDegree + 1),
    Polynomial.C (∑ l ∈ range (5 * s + 1), P.coeff l * mc (6 * l) (s + l)) * Polynomial.X ^ s

lemma coeff_Pm (k j : ℕ) : (Pm k).coeff j = mc k j := rfl

lemma coeff_Aform (P : Polynomial ℤ) (l : ℕ) :
    (Aform P).coeff l = if l < 6 * P.natDegree + 2 then ∑ s ∈ range (5 * l), P.coeff s * mc (6 * s + 1) (l + s)
      else 0 := by
  rw [Aform, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (6 * P.natDegree + 2)) l]
  simp [mem_range]

lemma coeff_Bform (P : Polynomial ℤ) (s : ℕ) :
    (Bform P).coeff s = if s < 6 * P.natDegree + 1 then ∑ l ∈ range (5 * s + 1), P.coeff l * mc (6 * l) (s + l)
      else 0 := by
  rw [Bform, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (6 * P.natDegree + 1)) s]
  simp [mem_range]

/-- the reindexing identity, even → odd. -/
lemma reindex_A (P : Polynomial ℤ) :
    ∑ s ∈ range (P.natDegree + 1), Polynomial.C (P.coeff s) * Polynomial.X ^ (P.natDegree - s) * Pm (6 * s + 1)
      = Polynomial.X ^ P.natDegree * Aform P := by
  set M := P.natDegree
  ext n
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']
  simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', coeff_Pm]
  split_ifs with hn
  · rw [coeff_Aform]
    split_ifs with hl
    · -- both sides are `Σ_s P_s m_{6s+1, n−M+s}` over different ranges
      rw [← sum_subset (s₁ := range (M + 1) ∩ range (5 * (n - M))) inter_subset_left ?_,
        ← sum_subset (s₁ := range (M + 1) ∩ range (5 * (n - M))) inter_subset_right ?_]
      · refine sum_congr rfl fun s hs => ?_
        simp only [mem_inter, mem_range] at hs
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega, mc_low _ _ (by omega), mul_zero]
    · refine sum_eq_zero fun s hs => ?_
      simp only [mem_range] at hs
      rw [if_pos (by omega), mc_high _ _ (by omega), mul_zero]
  · refine sum_eq_zero fun s hs => ?_
    simp only [mem_range] at hs
    split_ifs with h
    · rw [mc_low _ _ (by omega), mul_zero]
    · exact mul_zero _

/-- the reindexing identity, odd → even. -/
lemma reindex_B (P : Polynomial ℤ) :
    ∑ l ∈ range (P.natDegree + 1), Polynomial.C (P.coeff l) * Polynomial.X ^ (P.natDegree - l) * Pm (6 * l)
      = Polynomial.X ^ P.natDegree * Bform P := by
  set M := P.natDegree
  ext n
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']
  simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', coeff_Pm]
  split_ifs with hn
  · rw [coeff_Bform]
    split_ifs with hl
    · rw [← sum_subset (s₁ := range (M + 1) ∩ range (5 * (n - M) + 1)) inter_subset_left ?_,
        ← sum_subset (s₁ := range (M + 1) ∩ range (5 * (n - M) + 1)) inter_subset_right ?_]
      · refine sum_congr rfl fun s hs => ?_
        simp only [mem_inter, mem_range] at hs
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · intro s hs hs'
        simp only [mem_inter, mem_range, not_and] at hs hs'
        rw [if_pos (by omega), show n - (M - s) = n - M + s by omega, mc_low _ _ (by omega), mul_zero]
    · refine sum_eq_zero fun s hs => ?_
      simp only [mem_range] at hs
      rw [if_pos (by omega), mc_high _ _ (by omega), mul_zero]
  · refine sum_eq_zero fun s hs => ?_
    simp only [mem_range] at hs
    split_ifs with h
    · rw [mc_low _ _ (by omega), mul_zero]
    · exact mul_zero _

lemma dis5_zero (r : ℕ) : dis5 r (0 : PowerSeries ℤ) = 0 := by ext n; simp [dis5]

lemma dis5_sum {ι : Type*} (r : ℕ) (t : Finset ι) (f : ι → PowerSeries ℤ) :
    dis5 r (∑ i ∈ t, f i) = ∑ i ∈ t, dis5 r (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [dis5_zero]
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, dis5_add, ih]

lemma dis5_intCast_mul (r : ℕ) (c : ℤ) (F : PowerSeries ℤ) : dis5 r ((c : PowerSeries ℤ) * F) = c * dis5 r F := by
  rw [show (c : PowerSeries ℤ) = C c by simp, dis5_C_mul]

lemma inv_normQ_ne : Ring.inverse normQ ≠ 0 := by
  intro h; have := normQ_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this

lemma taus_ne : taus ≠ 0 := mul_ne_zero X_ne_zero inv_normQ_ne

/-- `q/E = y/E(q²⁵)`. -/
lemma X_mul_pGF : X * partitionGF = E5 (Ring.inverse eQ) * Ys := by
  have h := Ys_mul_E
  have h1 : E5 eQ * E5 (Ring.inverse eQ) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel _ isUnit_eQ, map_one]
  have h2 : qfacInf * partitionGF = 1 := Ring.mul_inverse_cancel _ isUnit_qfacInf
  linear_combination -(X * partitionGF) * h1 - E5 (Ring.inverse eQ) * partitionGF * h + E5 (Ring.inverse eQ) * Ys * h2

lemma E5_taus_pow {M s : ℕ} (hs : s ≤ M) : E5 taus ^ M * taus ^ s = E5 taus ^ (M - s) * Ys ^ (6 * s) := by
  rw [show E5 taus ^ M = E5 taus ^ (M - s) * E5 taus ^ s by rw [← pow_add]; congr 1; omega, mul_assoc,
    ← mul_pow, mul_comm (E5 taus), taus_mul_E5, ← pow_mul]

/-- **transition even → odd**: `U₅(q·(1/E)·P(τ)) = (1/E(q⁵))·(A P)(τ)`. -/
theorem trans_even (P : Polynomial ℤ) :
    dis5 0 (X * partitionGF * Polynomial.aeval taus P) = Ring.inverse eQ * Polynomial.aeval taus (Aform P) := by
  set M := P.natDegree
  apply mul_left_cancel₀ (pow_ne_zero M taus_ne)
  have key : E5 (taus ^ M) * (X * partitionGF * Polynomial.aeval taus P)
      = E5 (Ring.inverse eQ) * ∑ s ∈ range (M + 1), E5 ((P.coeff s : PowerSeries ℤ) * taus ^ (M - s))
        * Ys ^ (6 * s + 1) := by
    rw [Polynomial.aeval_eq_sum_range, X_mul_pGF, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun s hs => ?_
    have hs' : s ≤ M := by simp at hs; omega
    simp only [map_mul, map_pow, map_intCast, Algebra.smul_def, algebraMap_int_eq, eq_intCast]
    rw [show E5 taus ^ M * (E5 (Ring.inverse eQ) * Ys * ((P.coeff s : PowerSeries ℤ) * taus ^ s))
        = E5 (Ring.inverse eQ) * Ys * (P.coeff s : PowerSeries ℤ) * (E5 taus ^ M * taus ^ s) by ring,
      E5_taus_pow hs', pow_succ]
    ring
  rw [← dis5_E5_mul 0 (by norm_num), key, dis5_E5_mul 0 (by norm_num), dis5_sum]
  simp_rw [dis5_E5_mul 0 (by norm_num), Ys_dis]
  rw [mul_left_comm, show taus ^ M * Polynomial.aeval taus (Aform P)
      = Polynomial.aeval taus (Polynomial.X ^ M * Aform P) by simp, ← reindex_A, map_sum]
  refine congrArg _ (sum_congr rfl fun s _ => ?_)
  simp only [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
  rfl

/-- **transition odd → even**: `U₅((1/E(q⁵))·P(τ)) = (1/E)·(B P)(τ)`. -/
theorem trans_odd (P : Polynomial ℤ) :
    dis5 0 (Ring.inverse eQ * Polynomial.aeval taus P) = partitionGF * Polynomial.aeval taus (Bform P) := by
  set M := P.natDegree
  apply mul_left_cancel₀ (pow_ne_zero M taus_ne)
  have hinv : Ring.inverse eQ = E5 partitionGF := by rw [eQ, E5_inverse isUnit_qfacInf]; rfl
  have key : E5 (taus ^ M) * (Ring.inverse eQ * Polynomial.aeval taus P)
      = E5 partitionGF * ∑ l ∈ range (M + 1), E5 ((P.coeff l : PowerSeries ℤ) * taus ^ (M - l)) * Ys ^ (6 * l) := by
    rw [Polynomial.aeval_eq_sum_range, hinv, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun l hl => ?_
    have hl' : l ≤ M := by simp at hl; omega
    simp only [map_mul, map_pow, map_intCast, Algebra.smul_def, eq_intCast]
    rw [show E5 taus ^ M * (E5 partitionGF * ((P.coeff l : PowerSeries ℤ) * taus ^ l))
        = E5 partitionGF * (P.coeff l : PowerSeries ℤ) * (E5 taus ^ M * taus ^ l) by ring, E5_taus_pow hl']
    ring
  rw [← dis5_E5_mul 0 (by norm_num), key, dis5_E5_mul 0 (by norm_num), dis5_sum]
  simp_rw [dis5_E5_mul 0 (by norm_num), Ys_dis]
  rw [mul_left_comm, show taus ^ M * Polynomial.aeval taus (Bform P)
      = Polynomial.aeval taus (Polynomial.X ^ M * Bform P) by simp, ← reindex_B, map_sum]
  refine congrArg _ (sum_congr rfl fun l _ => ?_)
  simp only [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
  rfl

end MockTheta5.JTP
