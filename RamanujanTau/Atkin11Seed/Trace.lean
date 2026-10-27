/-
# Traces over the eleven conjugates and Lagrange's formula

Over `ℂ⟦q⟧` the conjugates `r_k = φ(ζᵏq)` are the eleven distinct roots of the monic modular polynomial
`P`, so `P = ∏_k (Y − r_k)` and `P'(r_k) = ∏_{j≠k}(r_k − r_j)`. Lagrange interpolation gives, for
`deg F ≤ 10` with `F(r_k) = P'(r_k)·w_k`, the identity `[Y¹⁰]F = Σ_k w_k`.

Applied to `F ≡ Y^λ S(Y) (mod P)` where `P'(φ)·g = S(φ)`, this computes the trace
`Σ_k φ(ζᵏq)^λ g(ζᵏq) = 11·(U(φ^λ g))(q¹¹)` (`trace_of_H2`).
-/
import RamanujanTau.Atkin11Seed.Eval
import RamanujanTau.Atkin11Norm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Atkin11Seed
open Atkin11 Atkin11Conj MockTheta5.JTP Finset

/-! ### Lagrange -/

section Lagrange
open Polynomial

variable {K : Type*} [CommRing K] [IsDomain K]

lemma prod_erase_monic {n : ℕ} (r : Fin n → K) (k : Fin n) :
    (∏ j ∈ univ.erase k, (X - C (r j))).Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (r j)

lemma prod_erase_natDegree {n : ℕ} (r : Fin n → K) (k : Fin n) :
    (∏ j ∈ univ.erase k, (X - C (r j))).natDegree = n - 1 := by
  rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (r j)]
  simp [card_erase_of_mem (mem_univ k)]

lemma eval_prod_erase {n : ℕ} (r : Fin n → K) (i k : Fin n) :
    (∏ j ∈ univ.erase i, (X - C (r j))).eval (r k) = if i = k then ∏ j ∈ univ.erase k, (r k - r j) else 0 := by
  rw [eval_prod]
  split_ifs with h
  · subst h; simp
  · exact prod_eq_zero (mem_erase.mpr ⟨Ne.symm h, mem_univ k⟩) (by simp)

/-- **Lagrange**: the top coefficient of an interpolant. -/
theorem lagrange_coeff {n : ℕ} (r : Fin (n + 1) → K) (hr : Function.Injective r) (F : K[X])
    (hF : F.natDegree ≤ n) (w : Fin (n + 1) → K)
    (hw : ∀ k, F.eval (r k) = (∏ j ∈ univ.erase k, (r k - r j)) * w k) :
    F.coeff n = ∑ k, w k := by
  set G : K[X] := ∑ k, C (w k) * ∏ j ∈ univ.erase k, (X - C (r j)) with hG
  have hGdeg : G.natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_le _ _).trans ?_
    rw [prod_erase_natDegree]; simp
  have hGe : ∀ k, G.eval (r k) = (∏ j ∈ univ.erase k, (r k - r j)) * w k := by
    intro k
    rw [hG, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_prod_erase]
    rw [sum_eq_single k (fun i _ hi => by rw [if_neg hi, mul_zero]) (by simp), if_pos rfl, mul_comm]
  have hD : F - G = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (F - G) hr (fun k => ?_) ?_
    · rw [eval_sub, hw, hGe, sub_self]
    · simp only [Fintype.card_fin]
      exact lt_of_le_of_lt (natDegree_sub_le_of_le hF hGdeg) (by rw [max_self]; omega)
  rw [sub_eq_zero.mp hD, hG, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul]
  have hm := prod_erase_monic r k
  have hd := prod_erase_natDegree r k
  simp only [Nat.add_sub_cancel] at hd
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [h1, mul_one]

/-- a monic polynomial of degree `n` with `n` distinct roots is `∏ (Y − r_k)`. -/
theorem eq_prod_of_roots {n : ℕ} (R : K[X]) (hm : R.Monic) (hdeg : R.natDegree = n + 1) (r : Fin (n + 1) → K)
    (hr : Function.Injective r) (hroot : ∀ k, R.eval (r k) = 0) :
    R = ∏ k, (X - C (r k)) := by
  set S : K[X] := ∏ k, (X - C (r k)) with hSdef
  have hmon : ∀ k ∈ (univ : Finset (Fin (n + 1))), (X - C (r k)).Monic := fun k _ => monic_X_sub_C (r k)
  have hSm : S.Monic := monic_prod_of_monic _ _ hmon
  have hSdeg : S.natDegree = n + 1 := by rw [hSdef, natDegree_prod_of_monic _ _ hmon]; simp
  have hDdeg : (R - S).natDegree < n + 1 := by
    have : (R - S).natDegree ≤ n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub]
      rcases Nat.lt_or_ge (n + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
      · have hNn : N = n + 1 := by omega
        rw [hNn]
        have e1 := hm.coeff_natDegree
        have e2 := hSm.coeff_natDegree
        rw [hdeg] at e1
        rw [hSdeg] at e2
        rw [e1, e2, sub_self]
    omega
  have hD0 : R - S = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hr (fun k => ?_) (by simpa using hDdeg)
    rw [eval_sub, hroot k, hSdef, eval_prod, prod_eq_zero (mem_univ k) (by simp), sub_zero]
  exact sub_eq_zero.mp hD0

/-- `P'(r_k) = ∏_{j≠k}(r_k − r_j)` for `P = ∏(Y − r_j)`. -/
theorem derivative_prod_eval {n : ℕ} (r : Fin n → K) (k : Fin n) :
    (derivative (∏ j, (X - C (r j)))).eval (r k) = ∏ j ∈ univ.erase k, (r k - r j) := by
  classical
  rw [derivative_prod_finset, eval_finsetSum]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod_erase]
  rw [sum_ite_eq' univ k]; simp

end Lagrange

/-! ### conjugation -/

open PowerSeries

/-- `f ↦ f(ζᵏq)` on `ℤ⟦q⟧ → ℂ⟦q⟧`. -/
noncomputable def cj (k : Fin 11) : PS →+* PowerSeries ℂ := (rescale (ζ ^ (k : ℕ))).comp ψC

lemma cj_apply (k : Fin 11) (f : PS) : cj k f = rescale (ζ ^ (k : ℕ)) (ψC f) := rfl

lemma cj_V (k : Fin 11) (g : PS) : cj k (V g) = ψC (V g) := rescale_ψC_V k g

lemma cj_φ (k : Fin 11) : cj k φ = rC k := rfl

/-- **the trace**: `Σ_k f(ζᵏq) = 11·(Uf)(q¹¹)`. -/
lemma sum_cj (f : PS) : ∑ k, cj k f = ψC (V (11 * U f)) := by
  simp only [cj_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => rescale (ζ ^ k) (ψC f)) 11, sum_conj]
  ext n
  rw [coeff_C_mul, coeff_expand, coeff_map, coeff_ex]
  have h11 : (11 : PS) * U f = PowerSeries.C (11 : ℤ) * U f := by simp
  split_ifs with h
  · rw [h11, coeff_C_mul, coeff_U, UC, coeff_mk, coeff_map, map_mul, mul_comm]; simp; ring
  · simp

/-! ### the monic modular polynomial over `ℂ⟦q⟧` -/

/-- `P(Y) = Y¹¹ − Σ_j (−1)^j e_{j+1}(q¹¹) Y^{10−j}`. -/
noncomputable def PC : Polynomial (PowerSeries ℂ) :=
  Polynomial.X ^ 11 - ∑ j ∈ range 11, Polynomial.C (ψC ((-1) ^ j * V (lc (eF (j + 1))))) * Polynomial.X ^ (10 - j)

lemma PC_eval (y : PowerSeries ℂ) :
    PC.eval y = y ^ 11 - ∑ j ∈ range 11, ψC ((-1) ^ j * V (lc (eF (j + 1)))) * y ^ (10 - j) := by
  simp [PC, Polynomial.eval_finsetSum]

lemma PC_natDegree_lt : (∑ j ∈ range 11, Polynomial.C (ψC ((-1) ^ j * V (lc (eF (j + 1))))) * Polynomial.X ^ (10 - j) :
    Polynomial (PowerSeries ℂ)).degree < 11 := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe 11)]
  intro j hj
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  have : 10 - j < 11 := by omega
  exact_mod_cast this

lemma PC_monic : PC.Monic := by
  rw [PC]
  exact (Polynomial.monic_X_pow 11).sub_of_left (by rw [Polynomial.degree_X_pow]; exact PC_natDegree_lt)

lemma PC_natDegree : PC.natDegree = 11 := by
  have h := PC_monic
  rw [Polynomial.natDegree_eq_of_degree_eq_some (n := 11)]
  rw [PC, Polynomial.degree_sub_eq_left_of_degree_lt (by rw [Polynomial.degree_X_pow]; exact PC_natDegree_lt),
    Polynomial.degree_X_pow]

lemma PC_root (k : Fin 11) : PC.eval (rC k) = 0 := by
  have h := congrArg (cj k) φ_isRoot
  simp only [map_pow, map_sum, map_mul, cj_φ] at h
  rw [PC_eval, h]
  refine sub_eq_zero.mpr (sum_congr rfl fun j _ => ?_)
  simp only [map_mul, map_pow, map_neg, map_one, cj_V]

lemma PC_eq_prod : PC = ∏ k, (Polynomial.X - Polynomial.C (rC k)) :=
  eq_prod_of_roots PC PC_monic PC_natDegree rC rC_injective PC_root

/-- `P'(Y) = 11Y¹⁰ − Σ_{j<10} (10−j)(−1)^j e_{j+1}(q¹¹) Y^{9−j}` on `ℤ⟦q⟧`. -/
lemma dP_eval (y : PS) : evY y dP = 11 * y ^ 10 - ∑ j ∈ range 10,
    ((10 - j : ℕ) : PS) * ((-1) ^ j * V (lc (eF (j + 1)))) * y ^ (9 - j) := by
  simp only [dP, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.singleton_append, evY_cons, evY_nil, JE.eval_smul, JE.eval_single]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [← eJ_eval 0 (by norm_num), ← eJ_eval 1 (by norm_num), ← eJ_eval 2 (by norm_num), ← eJ_eval 3 (by norm_num),
    ← eJ_eval 4 (by norm_num), ← eJ_eval 5 (by norm_num), ← eJ_eval 6 (by norm_num), ← eJ_eval 7 (by norm_num),
    ← eJ_eval 8 (by norm_num), ← eJ_eval 9 (by norm_num)]
  simp only [map_mul, map_intCast, evZ, gi, mul_zero, add_zero, mul_one, map_one]
  push_cast
  ring

lemma derivative_PC_eval (y : PowerSeries ℂ) : (Polynomial.derivative PC).eval y = 11 * y ^ 10 - ∑ j ∈ range 10,
    ((10 - j : ℕ) : PowerSeries ℂ) * ψC ((-1) ^ j * V (lc (eF (j + 1)))) * y ^ (9 - j) := by
  rw [PC, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_sum, Polynomial.eval_sub,
    Polynomial.eval_finsetSum, Finset.sum_range_succ]
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_natCast]
  norm_num
  refine sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show 10 - j - 1 = 9 - j by omega, Nat.cast_sub (by omega : j ≤ 10)]
  push_cast
  ring

/-- `P'(φ)(ζᵏq) = ∏_{j≠k}(r_k − r_j)`. -/
lemma cj_dP (k : Fin 11) : cj k (evY φ dP) = ∏ j ∈ univ.erase k, (rC k - rC j) := by
  rw [← derivative_prod_eval rC k, ← PC_eq_prod, derivative_PC_eval, dP_eval]
  simp only [map_sub, map_mul, map_pow, map_sum, map_natCast, map_ofNat, cj_φ]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, cj_V]

/-! ### polynomials from `PY` -/

noncomputable def toPol : PY → Polynomial (PowerSeries ℂ)
  | [] => 0
  | a :: f => Polynomial.C (ψC (V a.eval)) + Polynomial.X * toPol f

lemma toPol_eval (k : Fin 11) : ∀ F : PY, (toPol F).eval (rC k) = cj k (evY φ F)
  | [] => by simp [toPol, evY]
  | a :: f => by
    rw [toPol, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, toPol_eval k f, evY_cons,
      map_add, map_mul, cj_V, cj_φ]

lemma toPol_coeff : ∀ (F : PY) (n : ℕ), (toPol F).coeff n = ψC (V (F.getD n JE.zero).eval)
  | [], n => by simp [toPol, JE.eval_zero]
  | a :: f, 0 => by simp [toPol]
  | a :: f, n + 1 => by
    rw [toPol, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, Polynomial.coeff_X_mul,
      toPol_coeff f n]; rfl

lemma toPol_natDegree (F : PY) (h : F.length ≤ 11) : (toPol F).natDegree ≤ 10 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [toPol_coeff, List.getD_eq_default _ _ (by omega), JE.eval_zero, map_zero, map_zero]

/-- **the trace formula**: if `P'(φ)·g = S(φ)` and `F(φ) = φ^λ S(φ)` with `deg F ≤ 10`, then
`11·U(φ^λ g) = [Y¹⁰]F`. -/
theorem trace_of_H2 (g : PS) (S : PY) (hH : evY φ dP * g = evY φ S) (lam : ℕ) (F : PY)
    (hF : evY φ F = φ ^ lam * evY φ S) (hlen : F.length ≤ 11) :
    11 * U (φ ^ lam * g) = (F.getD 10 JE.zero).eval := by
  have hL := lagrange_coeff rC rC_injective (toPol F) (toPol_natDegree F hlen) (fun k => cj k (φ ^ lam * g))
    (fun k => by
      rw [toPol_eval, hF, ← hH]; simp only [map_mul, map_pow, cj_dP, cj_φ]; ring)
  rw [toPol_coeff, sum_cj] at hL
  exact (V_injective (ψC_injective hL)).symm

end Atkin11Seed
