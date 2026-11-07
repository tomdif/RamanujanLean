/-
# The Kloosterman character on monic polynomials and its degree sums

For a field `F`, an additive character `ψ`, and `a b : F`, put on a polynomial `f`
`λ(f) = 0` if `f(0) = 0`, and otherwise `λ(f) = ψ(-a·c₁ - b·(f₁/f₀))`, where `c₁` is the
next-to-leading coefficient and `f₀, f₁` are the coefficients of `X⁰, X¹`.
For monic `f = X^n + c₁X^{n-1} + ⋯ + c_n` this is `ψ(-a c₁ - b c_{n-1}/c_n)`.

* `lam_mul`: `λ` is completely multiplicative on monic polynomials.
* `degSum`: `A_n = Σ_{f monic, deg f = n} λ(f)`; over a finite field with `ψ` primitive and
  `a, b ≠ 0`: `A₀ = 1`, `A₁ = Σ_{u ∈ F^×} ψ(au + b/u)`, `A₂ = |F|`, `A_n = 0` for `n ≥ 3`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.KloostermanL

open Polynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

/-- The Kloosterman character on polynomials. -/
noncomputable def lam (ψ : AddChar F ℂ) (a b : F) (f : F[X]) : ℂ :=
  if f.coeff 0 = 0 then 0 else ψ (-(a * f.nextCoeff) - b * (f.coeff 1 / f.coeff 0))

lemma coeff_one_mul (f g : F[X]) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

variable (ψ : AddChar F ℂ) (a b : F)

theorem lam_mul {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    lam ψ a b (f * g) = lam ψ a b f * lam ψ a b g := by
  unfold lam
  rw [mul_coeff_zero]
  by_cases h0 : f.coeff 0 = 0
  · simp [h0]
  by_cases h1 : g.coeff 0 = 0
  · simp [h1]
  rw [if_neg (mul_ne_zero h0 h1), if_neg h0, if_neg h1, ← AddChar.map_add_eq_mul,
    hf.nextCoeff_mul hg, coeff_one_mul]
  congr 1
  field_simp
  ring

theorem lam_one : lam ψ a b 1 = 1 := by
  simp [lam, nextCoeff, coeff_one]

theorem lam_pow {f : F[X]} (hf : f.Monic) (n : ℕ) : lam ψ a b (f ^ n) = lam ψ a b f ^ n := by
  induction n with
  | zero => simp [lam_one]
  | succ n ih => rw [pow_succ, lam_mul ψ a b (hf.pow n) hf, ih, pow_succ]

theorem lam_X : lam ψ a b (X : F[X]) = 0 := by simp [lam]

/-! ### Finite sets of monic polynomials -/

/-- `X^n + Σ_{i<n} c_i X^i`. -/
noncomputable def mkMonic (n : ℕ) (c : Fin n → F) : F[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

lemma mkMonic_monic (n : ℕ) (c : Fin n → F) : (mkMonic n c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

lemma natDegree_mkMonic (n : ℕ) (c : Fin n → F) : (mkMonic n c).natDegree = n := by
  unfold mkMonic
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

lemma coeff_mkMonic_lt (n : ℕ) (c : Fin n → F) (j : ℕ) (hj : j < n) :
    (mkMonic n c).coeff j = c ⟨j, hj⟩ := by
  unfold mkMonic
  rw [coeff_add, coeff_X_pow, if_neg hj.ne, zero_add, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext h.symm)
  · simp

lemma mkMonic_injective (n : ℕ) : Function.Injective (mkMonic (F := F) n) := by
  intro c d h
  funext i
  have := congrArg (fun f => f.coeff i) h
  simp only [coeff_mkMonic_lt n _ i i.isLt] at this
  exact this

/-- The monic polynomials of degree `n` (finite when `F` is). -/
noncomputable def monicDeg [Fintype F] (n : ℕ) : Finset F[X] := univ.image (mkMonic n)

theorem mem_monicDeg [Fintype F] {n : ℕ} {f : F[X]} :
    f ∈ monicDeg n ↔ f.Monic ∧ f.natDegree = n := by
  unfold monicDeg
  rw [mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact ⟨mkMonic_monic n c, natDegree_mkMonic n c⟩
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, mem_univ _, ?_⟩
    unfold mkMonic
    conv_rhs => rw [hm.as_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]

/-- `A_n = Σ_{f monic of degree n} λ(f)`. -/
noncomputable def degSum [Fintype F] (n : ℕ) : ℂ := ∑ f ∈ monicDeg n, lam ψ a b f

variable [Fintype F]

/-- The Kloosterman sum `Σ_{u ∈ F^×} ψ(au + b/u)`. -/
noncomputable def klF : ℂ :=
  ∑ u : Fˣ, ψ (a * (u : F) + b * ((u⁻¹ : Fˣ) : F))

theorem degSum_eq_sum_mk (n : ℕ) :
    degSum ψ a b n = ∑ c : Fin n → F, lam ψ a b (mkMonic n c) := by
  unfold degSum monicDeg
  rw [sum_image (fun c _ d _ h => mkMonic_injective n h)]

theorem degSum_zero : degSum ψ a b 0 = 1 := by
  rw [degSum_eq_sum_mk]
  simp [mkMonic, lam_one]

/-- Sum over the nonzero elements equals the sum over units. -/
lemma sum_ne_zero_eq_sum_units (g : F → ℂ) :
    ∑ c : F, (if c = 0 then 0 else g c) = ∑ u : Fˣ, g u := by
  have h : ∀ c : F, (if c = 0 then 0 else g c) = if c ≠ 0 then g c else 0 := fun c => by
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun c _ => h c), ← Finset.sum_filter]
  refine Finset.sum_bij' (fun x hx => Units.mk0 x (Finset.mem_filter.mp hx).2)
    (fun u _ => (u : F)) (fun _ _ => mem_univ _) (fun u _ => by simp)
    (fun x _ => by simp) (fun u _ => by ext; simp) (fun _ _ => rfl)

theorem degSum_one : degSum ψ a b 1 = klF ψ a b := by
  rw [degSum_eq_sum_mk]
  have hmk : ∀ c : Fin 1 → F, mkMonic 1 c = X + C (c 0) := by
    intro c; simp [mkMonic]
  have hl : ∀ t : F, lam ψ a b (X + C t) =
      if t = 0 then 0 else ψ (-(a * t) - b * (1 / t)) := by
    intro t
    simp [lam, nextCoeff_X_add_C, coeff_X, coeff_C]
  simp_rw [hmk, hl]
  rw [← (Equiv.funUnique (Fin 1) F).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  rw [sum_ne_zero_eq_sum_units, klF]
  refine Fintype.sum_equiv (Equiv.neg Fˣ) _ _ (fun u => ?_)
  congr 1
  simp [Units.val_inv_eq_inv_val]
  ring

theorem degSum_two (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) :
    degSum ψ a b 2 = Fintype.card F := by
  rw [degSum_eq_sum_mk]
  have hl : ∀ c : Fin 2 → F, lam ψ a b (mkMonic 2 c) =
      if c 0 = 0 then 0 else ψ (c 1 * (-a - b / c 0)) := by
    intro c
    have hn : (mkMonic 2 c).nextCoeff = c 1 := by
      rw [nextCoeff_of_natDegree_pos (by rw [natDegree_mkMonic]; omega), natDegree_mkMonic]
      exact coeff_mkMonic_lt 2 c 1 (by omega)
    unfold lam
    rw [hn, coeff_mkMonic_lt 2 c 0 (by omega), coeff_mkMonic_lt 2 c 1 (by omega)]
    simp only [Fin.zero_eta, Fin.mk_one]
    split_ifs with h
    · rfl
    · congr 1; field_simp
  simp_rw [hl]
  rw [← (piFinTwoEquiv fun _ => F).symm.sum_comp, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
  have hinner : ∀ c0 : F, (∑ c1 : F, (if c0 = 0 then (0 : ℂ) else ψ (c1 * (-a - b / c0)))) =
      if c0 = -b / a then (Fintype.card F : ℂ) else 0 := by
    intro c0
    by_cases h0 : c0 = 0
    · subst h0
      rw [if_neg (Ne.symm (div_ne_zero (neg_ne_zero.2 hb) ha))]
      simp
    · simp only [if_neg h0]
      rw [AddChar.sum_mulShift _ hψ]
      have hiff : (-a - b / c0 = 0) ↔ (c0 = -b / a) := by
        constructor
        · intro h
          field_simp at h
          field_simp
          linear_combination -h
        · intro h
          subst h
          field_simp
          ring
      simp only [hiff]
      by_cases hc : c0 = -b / a <;> simp [hc]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq']
  simp

omit [Fintype F] in
/-- Translating the `X^{n-1}` coefficient. -/
lemma lam_add_shift {n : ℕ} (hn : 3 ≤ n) {f : F[X]} (hf : f.natDegree = n) (t : F) :
    lam ψ a b (f + C t * X ^ (n - 1)) = ψ (-(a * t)) * lam ψ a b f := by
  have hlt : degree (C t * X ^ (n - 1)) < degree f := by
    have hf0 : f ≠ 0 := by rintro rfl; simp at hf; omega
    rw [degree_eq_natDegree (p := f) hf0, hf]
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (by omega : n - 1 < n))
  have hdeg : (f + C t * X ^ (n - 1)).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt hlt, hf]
  have hn1 : (f + C t * X ^ (n - 1)).nextCoeff = f.nextCoeff + t := by
    rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hdeg, hf,
      coeff_add, coeff_C_mul_X_pow, if_pos rfl]
  have c0 : (f + C t * X ^ (n - 1)).coeff 0 = f.coeff 0 := by
    rw [coeff_add, coeff_C_mul_X_pow, if_neg (by omega), add_zero]
  have c1 : (f + C t * X ^ (n - 1)).coeff 1 = f.coeff 1 := by
    rw [coeff_add, coeff_C_mul_X_pow, if_neg (by omega), add_zero]
  unfold lam
  rw [c0, c1, hn1]
  split_ifs
  · simp
  · rw [← AddChar.map_add_eq_mul]
    congr 1
    ring

theorem degSum_eq_zero (hψ : ψ ≠ 1) (ha : a ≠ 0) {n : ℕ} (hn : 3 ≤ n) : degSum ψ a b n = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ (fun x => by rw [h x, AddChar.one_apply]))
  set t : F := -y / a
  have ht : -(a * t) = y := by simp only [t]; field_simp
  have hmem : ∀ (s : F) (f : F[X]), f ∈ monicDeg n → f + C s * X ^ (n - 1) ∈ monicDeg n := by
    intro s f hf
    rw [mem_monicDeg] at hf ⊢
    have hlt : degree (C s * X ^ (n - 1)) < degree f := by
      rw [degree_eq_natDegree (p := f) hf.1.ne_zero, hf.2]
      exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (by omega : n - 1 < n))
    exact ⟨hf.1.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hf.2]⟩
  have key0 : ∑ f ∈ monicDeg n, lam ψ a b (f + C t * X ^ (n - 1)) = degSum ψ a b n := by
    unfold degSum
    exact Finset.sum_nbij' (fun f => f + C t * X ^ (n - 1)) (fun f => f + C (-t) * X ^ (n - 1))
      (fun f hf => hmem t f hf) (fun f hf => hmem (-t) f hf) (fun f _ => by simp)
      (fun f _ => by simp) (fun f _ => rfl)
  have key : degSum ψ a b n = ψ y * degSum ψ a b n := by
    conv_lhs => rw [← key0]
    unfold degSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun f hf => ?_)
    rw [lam_add_shift ψ a b hn (mem_monicDeg.mp hf).2, ht]
  have : (1 - ψ y) * degSum ψ a b n = 0 := by linear_combination key
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hy
  · exact h

end RamanujanTau.KloostermanL
