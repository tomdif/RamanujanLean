/-
# Stepanov's method, part 2: the auxiliary polynomial and the one-sided bound

`T = ∑_{j<J} (r_j + s_j g) X^{pj}`, `g = f^c`, `c = (p-1)/2`, `deg r_j, s_j < A`.
* (derivative formula) `f^k (s g)^{(k)} = u_k(s) g` with `u_{k+1} = f u_k' + (c-k) f' u_k`;
* in characteristic `p`, `(P X^{pj})^{(k)} = P^{(k)} X^{pj}`;
* so for `x ∈ S_ε = {g(x) = ε}`: `f(x)^k T^{(k)}(x) = Q_k(x)` with
  `Q_k = ∑_j (f^k r_j^{(k)} + ε u_k(s_j)) X^j`, a polynomial of degree `< D`;
* (dimension count) if `ℓ D < 2JA` some nonzero `(r,s)` makes all `Q_k = 0` (`k < ℓ`);
* (multiplicity) then every `x ∈ S_ε` is a root of `T` of multiplicity `≥ ℓ` (`ℓ ≤ p`);
* (nonvanishing, `Basic.lean`) `T ≠ 0`, hence `ℓ |S_ε| ≤ deg T ≤ A-1 + cm + p(J-1)`.
-/
import RamanujanTau.Stepanov.Basic

set_option autoImplicit false

namespace RamanujanTau.Stepanov

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

/-! ### Linear operators -/

/-- `u_k`: `u_0 = id`, `u_{k+1} = f·u_k' + (c-k) f'·u_k`, with `c = (p-1)/2`. -/
noncomputable def uOp (f : F[X]) : ℕ → F[X] →ₗ[F] F[X]
  | 0 => LinearMap.id
  | k + 1 => (LinearMap.mulLeft F f ∘ₗ derivative +
      (((((p - 1) / 2 : ℕ) : F) - (k : F)) • LinearMap.mulLeft F (derivative f))) ∘ₗ uOp f k

/-- iterated derivative as a linear map. -/
noncomputable def dOp : ℕ → F[X] →ₗ[F] F[X]
  | 0 => LinearMap.id
  | k + 1 => derivative ∘ₗ dOp k

theorem dOp_apply (k : ℕ) (q : F[X]) : dOp k q = derivative^[k] q := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dOp, ih, Function.iterate_succ_apply']

theorem f_mul_derivative_pow (f : F[X]) (n : ℕ) :
    f * derivative (f ^ n) = (n : F[X]) * f ^ n * derivative f := by
  rcases n with _ | n
  · simp
  · rw [derivative_pow]; simp [pow_succ]; ring

/-- **Derivative formula**: `f^k (s f^c)^{(k)} = u_k(s) f^c`. -/
theorem derivative_formula (f : F[X]) (k : ℕ) (s : F[X]) :
    f ^ k * derivative^[k] (s * f ^ ((p - 1) / 2)) = uOp f k s * f ^ ((p - 1) / 2) := by
  induction k with
  | zero => simp [uOp]
  | succ k ih =>
    set c := (p - 1) / 2
    set W := derivative^[k] (s * f ^ c)
    set u := uOp f k s
    have hD := congrArg derivative ih
    simp only [derivative_mul] at hD
    have hk := f_mul_derivative_pow f k
    have hc := f_mul_derivative_pow f c
    rw [Function.iterate_succ_apply']
    simp only [uOp, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.mulLeft_apply]
    change f ^ (k + 1) * derivative W = (f * derivative u + (((c : ℕ) : F) - (k : F)) •
      (derivative f * u)) * f ^ c
    rw [← C_mul', map_sub, map_natCast, map_natCast]
    linear_combination f * hD + u * hc - W * hk - (k : F[X]) * derivative f * ih

theorem derivative_mul_X_pow_p (P : F[X]) (j : ℕ) :
    derivative (P * X ^ (p * j)) = derivative P * X ^ (p * j) := by
  rw [derivative_mul, derivative_X_pow]
  have hp0 : ((p : F[X])) = 0 := by rw [← map_natCast C, ZMod.natCast_self, map_zero]
  simp [Nat.cast_mul]

theorem iterate_derivative_mul_X_pow_p (P : F[X]) (j k : ℕ) :
    derivative^[k] (P * X ^ (p * j)) = derivative^[k] P * X ^ (p * j) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, derivative_mul_X_pow_p,
      Function.iterate_succ_apply']

/-! ### Coefficient vectors -/

/-- polynomial with coefficient vector `w` (degree `< A`). -/
noncomputable def coefPoly (A : ℕ) : (Fin A → F) →ₗ[F] F[X] :=
  ∑ a : Fin A, (monomial (a : ℕ)) ∘ₗ LinearMap.proj a

theorem coefPoly_apply (A : ℕ) (w : Fin A → F) :
    coefPoly A w = ∑ a : Fin A, monomial (a : ℕ) (w a) := by
  simp [coefPoly]

theorem coeff_coefPoly (A : ℕ) (w : Fin A → F) (a : Fin A) :
    (coefPoly A w).coeff a = w a := by
  rw [coefPoly_apply, finsetSum_coeff]
  simp only [coeff_monomial, Fin.val_inj]
  rw [Finset.sum_ite_eq']; simp

theorem natDegree_coefPoly_le (A : ℕ) (w : Fin A → F) : (coefPoly A w).natDegree ≤ A - 1 := by
  rw [coefPoly_apply]
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact (natDegree_monomial_le _).trans (by omega)

theorem natDegree_coefPoly_lt (A : ℕ) (hA : 1 ≤ A) (w : Fin A → F) :
    (coefPoly A w).natDegree < A := by
  have := natDegree_coefPoly_le A w; omega

/-- the unknowns: `v (j, 0, a)` = coefficient of `X^a` in `r_j`, `v (j, 1, a)` in `s_j`. -/
abbrev Unk (J A : ℕ) := Fin J × Fin 2 × Fin A → F

noncomputable def sel {J A : ℕ} (j : Fin J) (b : Fin 2) : Unk (p := p) J A →ₗ[F] (Fin A → F) :=
  LinearMap.funLeft F F (fun a => (j, b, a))

noncomputable def rPoly {J A : ℕ} (v : Unk (p := p) J A) (j : Fin J) : F[X] :=
  coefPoly A (fun a => v (j, 0, a))

noncomputable def sPoly {J A : ℕ} (v : Unk (p := p) J A) (j : Fin J) : F[X] :=
  coefPoly A (fun a => v (j, 1, a))

/-- `Q_k` as a linear map of the unknowns. -/
noncomputable def qLin (f : F[X]) (ε : F) (J A k : ℕ) : Unk (p := p) J A →ₗ[F] F[X] :=
  ∑ j : Fin J, LinearMap.mulRight F (X ^ (j : ℕ)) ∘ₗ
    (LinearMap.mulLeft F (f ^ k) ∘ₗ dOp k ∘ₗ coefPoly A ∘ₗ sel j 0 +
      ε • (uOp f k ∘ₗ coefPoly A ∘ₗ sel j 1))

theorem qLin_apply (f : F[X]) (ε : F) (J A k : ℕ) (v : Unk (p := p) J A) :
    qLin f ε J A k v = ∑ j : Fin J, (f ^ k * derivative^[k] (rPoly v j) +
      ε • uOp f k (sPoly v j)) * X ^ (j : ℕ) := by
  simp [qLin, rPoly, sPoly, sel, dOp_apply, LinearMap.funLeft]
  rfl

/-- the auxiliary polynomial. -/
noncomputable def auxT (f : F[X]) {J A : ℕ} (v : Unk (p := p) J A) : F[X] :=
  ∑ j : Fin J, (rPoly v j + sPoly v j * f ^ ((p - 1) / 2)) * X ^ (p * (j : ℕ))

/-! ### Degree bounds -/

theorem eq_zero_of_natDegree_lt_of_coeff_eq_zero_aux {q : F[X]} {D : ℕ} (hq : q.natDegree < D)
    (hc : ∀ d < D, q.coeff d = 0) : q = 0 := by
  ext d
  rw [coeff_zero]
  by_cases hd : d < D
  · exact hc d hd
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem natDegree_uOp_le (f : F[X]) {m N : ℕ} (hf : f.natDegree ≤ m) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (s : F[X]) (hs : s.natDegree ≤ N) (k : ℕ) :
    (uOp f k s).natDegree ≤ N + k * (m - 1) := by
  induction k with
  | zero => simpa [uOp] using hs
  | succ k ih =>
    simp only [uOp, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.mulLeft_apply]
    set u := uOp f k s
    have h1 : (f * derivative u).natDegree ≤ N + (k + 1) * (m - 1) := by
      refine natDegree_mul_le.trans ?_
      have := natDegree_derivative_le u
      have : (k + 1) * (m - 1) = k * (m - 1) + (m - 1) := by ring
      omega
    have h2 : (((((p - 1) / 2 : ℕ) : F) - (k : F)) • (derivative f * u)).natDegree ≤
        N + (k + 1) * (m - 1) := by
      refine (natDegree_smul_le _ _).trans (natDegree_mul_le.trans ?_)
      have := natDegree_derivative_le f
      have : (k + 1) * (m - 1) = k * (m - 1) + (m - 1) := by ring
      omega
    exact (natDegree_add_le _ _).trans (max_le h1 h2)

theorem natDegree_qLin_lt (f : F[X]) (ε : F) {J A ℓ m : ℕ} (hf : f.natDegree ≤ m) (hm : 1 ≤ m)
    (hA : 2 ≤ A) (hℓA : ℓ ≤ A) (hJ1 : 1 ≤ J) (k : ℕ) (hk : k < ℓ) (v : Unk (p := p) J A) :
    (qLin f ε J A k v).natDegree < A + J - 1 + (ℓ - 1) * (m - 1) := by
  have hkm : k * (m - 1) ≤ (ℓ - 1) * (m - 1) := Nat.mul_le_mul_right _ (by omega)
  have hkm' : k * (m - 1) + k = k * m := by
    rw [← Nat.mul_succ]; congr 1; omega
  rw [qLin_apply]
  have hle : (∑ j : Fin J, (f ^ k * derivative^[k] (rPoly v j) +
      ε • uOp f k (sPoly v j)) * X ^ (j : ℕ)).natDegree ≤ A - 1 + (ℓ - 1) * (m - 1) + (J - 1) := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    refine (natDegree_mul_le).trans ?_
    have hX : (X ^ (j : ℕ) : F[X]).natDegree ≤ J - 1 := by
      rw [natDegree_X_pow]; omega
    have h1 : (f ^ k * derivative^[k] (rPoly v j)).natDegree ≤ A - 1 + k * (m - 1) := by
      refine natDegree_mul_le.trans ?_
      have h3 := natDegree_pow_le (p := f) (n := k)
      have h4 := natDegree_iterate_derivative (rPoly v j) k
      have h5 : (rPoly v j).natDegree ≤ A - 1 := natDegree_coefPoly_le A _
      have h6 : (f ^ k).natDegree ≤ k * m := h3.trans (Nat.mul_le_mul_left _ hf)
      have := hkm'
      omega
    have h2 : (ε • uOp f k (sPoly v j)).natDegree ≤ A - 1 + k * (m - 1) :=
      (natDegree_smul_le _ _).trans
        (natDegree_uOp_le f hf hm (by omega) _ (natDegree_coefPoly_le A _) k)
    have := (natDegree_add_le _ _).trans (max_le h1 h2)
    omega
  exact lt_of_le_of_lt hle (by omega)

theorem natDegree_auxT_le (f : F[X]) {J A m : ℕ} (hf : f.natDegree ≤ m) (hA : 1 ≤ A)
    (v : Unk (p := p) J A) :
    (auxT f v).natDegree ≤ A - 1 + (p - 1) / 2 * m + p * (J - 1) := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_X_pow]
  have hj : p * (j : ℕ) ≤ p * (J - 1) := Nat.mul_le_mul_left _ (by omega)
  have h1 := natDegree_coefPoly_le A (fun a => v (j, 0, a))
  have h2 := natDegree_coefPoly_le A (fun a => v (j, 1, a))
  have h3 : (f ^ ((p - 1) / 2)).natDegree ≤ (p - 1) / 2 * m :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ hf)
  have h4 : (rPoly v j + sPoly v j * f ^ ((p - 1) / 2)).natDegree ≤
      A - 1 + (p - 1) / 2 * m := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp only [rPoly]; omega
    · refine natDegree_mul_le.trans ?_; simp only [sPoly]; omega
  omega

/-! ### Evaluation on `S_ε` -/

theorem eval_iterate_derivative_auxT (f : F[X]) (ε : F) {J A : ℕ} (v : Unk (p := p) J A)
    (k : ℕ) (x : F) (hx : (f.eval x) ^ ((p - 1) / 2) = ε) :
    (f.eval x) ^ k * (derivative^[k] (auxT f v)).eval x = (qLin f ε J A k v).eval x := by
  rw [auxT, iterate_derivative_sum, qLin_apply, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_derivative_mul_X_pow_p, ← dOp_apply, map_add, dOp_apply, dOp_apply]
  have hfk := congrArg (eval x) (derivative_formula f k (sPoly v j))
  simp only [eval_mul, eval_pow, eval_smul, eval_add, eval_X, smul_eq_mul] at hfk ⊢
  rw [pow_mul, ZMod.pow_card, hx] at *
  rw [hx] at hfk
  linear_combination (x ^ (j : ℕ)) * hfk

/-! ### The one-sided bound -/

/-- **Stepanov's one-sided bound** (combinatorial form). -/
theorem stepanov_card_le (hp2 : p ≠ 2) (f : F[X]) (hf : NotConstSq f) (hf0 : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (ε : F) (hε : ε ≠ 0) {A J ℓ : ℕ} (hA2 : 2 ≤ A) (hℓA : ℓ ≤ A)
    (hℓp : ℓ ≤ p) (hA : 2 * (A - 1) + f.natDegree < p) (hJ : J + f.natDegree ≤ p)
    (hdim : ℓ * (A + J - 1 + (ℓ - 1) * (f.natDegree - 1)) < 2 * J * A) :
    ℓ * #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = ε)) ≤
      A - 1 + (p - 1) / 2 * f.natDegree + p * (J - 1) := by
  classical
  set m := f.natDegree
  set D := A + J - 1 + (ℓ - 1) * (m - 1)
  set S := univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = ε)
  -- the linear map
  let L : Unk (p := p) J A →ₗ[F] (Fin ℓ × Fin D → F) :=
    LinearMap.pi (fun kd : Fin ℓ × Fin D => (lcoeff F (kd.2 : ℕ)) ∘ₗ qLin f ε J A kd.1)
  have hrank : Module.finrank F (Fin ℓ × Fin D → F) < Module.finrank F (Unk (p := p) J A) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    calc ℓ * D < 2 * J * A := hdim
      _ = J * (2 * A) := by ring
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp at hdim
    · exact h
  obtain ⟨v, hvker, hv0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank)
  have hQ : ∀ k < ℓ, qLin f ε J A k v = 0 := by
    intro k hk
    apply eq_zero_of_natDegree_lt_of_coeff_eq_zero_aux
    · exact natDegree_qLin_lt f ε le_rfl hm hA2 hℓA hJ1 k hk v
    · intro d hd
      have := congrFun (LinearMap.mem_ker.mp hvker) (⟨k, hk⟩, ⟨d, hd⟩)
      simpa [L] using this
  -- T ≠ 0
  have hT0 : auxT f v ≠ 0 := by
    intro hT
    have hall := stepanov_nonvanish hp2 f hf hf0 (rPoly v) (sPoly v)
      (fun j => natDegree_coefPoly_lt A (by omega) _)
      (fun j => natDegree_coefPoly_lt A (by omega) _) hA hJ hT
    apply hv0
    funext ⟨j, b, a⟩
    rcases (hall j) with ⟨hr, hs⟩
    fin_cases b
    · have := coeff_coefPoly A (fun a => v (j, 0, a)) a
      simp only [rPoly] at hr; rw [hr, coeff_zero] at this; simpa using this.symm
    · have := coeff_coefPoly A (fun a => v (j, 1, a)) a
      simp only [sPoly] at hs; rw [hs, coeff_zero] at this; simpa using this.symm
  -- multiplicity
  have hmult : ∀ x ∈ S, ℓ ≤ rootMultiplicity x (auxT f v) := by
    intro x hx
    have hx' : (f.eval x) ^ ((p - 1) / 2) = ε := (Finset.mem_filter.mp hx).2
    have hfx : f.eval x ≠ 0 := by
      intro h; rw [h, zero_pow] at hx'; exact hε hx'.symm
      have := hp.out.two_le; omega
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · omega
    have := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
      (n := ℓ - 1) (t := x) hT0 ?_ ?_
    · omega
    · intro k hk
      have h1 := eval_iterate_derivative_auxT f ε v k x hx'
      rw [hQ k (by omega), eval_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hfx)
    · apply mem_nonZeroDivisors_of_ne_zero
      rw [Ne, ZMod.natCast_eq_zero_iff, hp.out.dvd_factorial]
      omega
  -- counting
  have hle : ℓ • S.val ≤ (auxT f v).roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Multiset.count_nsmul, count_roots]
    by_cases hx : x ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup hx, mul_one]; exact hmult x hx
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using hx)]; simp
  have := Multiset.card_le_card hle
  rw [Multiset.card_nsmul] at this
  calc ℓ * #S = ℓ * Multiset.card S.val := rfl
    _ ≤ Multiset.card (auxT f v).roots := this
    _ ≤ (auxT f v).natDegree := card_roots' _
    _ ≤ _ := natDegree_auxT_le f le_rfl (by omega) v

end RamanujanTau.Stepanov
