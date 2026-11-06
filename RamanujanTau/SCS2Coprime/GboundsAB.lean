/-
# Item 3 (part 2): the coefficient sequence of `G_{a,b,ℓ}` and its a priori bounds

* `cR a b ℓ n = τ(n) · [a ∣ bn+ℓ] τ((bn+ℓ)/a)` (real), `Gc c W = Σ c_n e^{−nW}` for any real
  sequence, and **`GAB_eq`**: `G_{a,b,ℓ}(W) = Gc (cR a b ℓ) (bW)`;
* generic bounds for `Gc`: `norm_Gc_le`, Lipschitz `norm_Gc_sub_le`, `n_laplace_c`;
* **`cR_laplace`**: `Σ |cR n| e^{−nσ} ≤ (1 + e^{ℓσ/b} (b/a)¹²)/2 · C₀ σ^{−12}` for `ℓ ≥ 0`
  (`|τ(n)τ(m)| ≤ (τ(n)² + τ(m)²)/2`, and `n ↦ m = (bn+ℓ)/a` is injective).
-/
import RamanujanTau.SCS2Coprime.QformAB

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Complex
open RamanujanTau.SCSProof
open scoped Real

open Classical in
/-- Real version of `cA`. -/
noncomputable def cAR (a : ℕ+) (N : ℤ) : ℝ :=
  if (a : ℤ) ∣ N ∧ 0 ≤ N then ((tau (N / a).toNat : ℤ) : ℝ) else 0

lemma cA_eq (a : ℕ+) (N : ℤ) : cA a N = (cAR a N : ℂ) := by
  unfold cA cAR; split_ifs <;> simp

/-- The coefficients `τ(n) cA(a, bn+ℓ)`. -/
noncomputable def cR (a b : ℕ+) (ℓ : ℤ) (n : ℕ) : ℝ := ((tau n : ℤ) : ℝ) * cAR a ((b : ℤ) * n + ℓ)

/-- The Laplace transform of a real sequence. -/
noncomputable def Gc (c : ℕ → ℝ) (W : ℂ) : ℂ := ∑' n : ℕ, (c n : ℂ) * cexp (-(n : ℂ) * W)

lemma GAB_eq (a b : ℕ+) (ℓ : ℤ) (W : ℂ) : GAB a b ℓ W = Gc (cR a b ℓ) ((b : ℂ) * W) := by
  unfold GAB Gc cR
  refine tsum_congr fun n => ?_
  rw [cA_eq]
  push_cast
  congr 2; ring

/-! ### Generic bounds -/

section generic

variable (c : ℕ → ℝ)

lemma norm_term_c (n : ℕ) (W : ℂ) :
    ‖(c n : ℂ) * cexp (-(n : ℂ) * W)‖ = |c n| * Real.exp (-n * W.re) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have : (-(n : ℂ) * W).re = -n * W.re := by simp
  rw [this]

lemma summable_Gc_term {W : ℂ} (hs : Summable (fun n : ℕ => |c n| * Real.exp (-n * W.re))) :
    Summable (fun n : ℕ => (c n : ℂ) * cexp (-(n : ℂ) * W)) := by
  refine Summable.of_norm ?_
  simp_rw [norm_term_c]; exact hs

lemma norm_Gc_le (W : ℂ) (hs : Summable (fun n : ℕ => |c n| * Real.exp (-n * W.re))) :
    ‖Gc c W‖ ≤ ∑' n : ℕ, |c n| * Real.exp (-n * W.re) := by
  unfold Gc
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · simp_rw [norm_term_c]; exact hs
  · simp_rw [norm_term_c]

lemma n_laplace_c {σ : ℝ} (hσ : 0 < σ)
    (hs : Summable (fun n : ℕ => |c n| * Real.exp (-n * (σ / 2)))) :
    Summable (fun n : ℕ => n * |c n| * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, n * |c n| * Real.exp (-n * σ) ≤
        2 / σ * ∑' n : ℕ, |c n| * Real.exp (-n * (σ / 2)) := by
  have hpt : ∀ n : ℕ, n * |c n| * Real.exp (-n * σ) ≤
      2 / σ * (|c n| * Real.exp (-n * (σ / 2))) := by
    intro n
    have := n_exp_le n hσ
    have ha := abs_nonneg (c n)
    calc (n : ℝ) * |c n| * Real.exp (-n * σ) = |c n| * ((n : ℝ) * Real.exp (-n * σ)) := by
          ring
      _ ≤ |c n| * (2 / σ * Real.exp (-n * (σ / 2))) := by gcongr
      _ = _ := by ring
  have hnn : ∀ n : ℕ, 0 ≤ n * |c n| * Real.exp (-n * σ) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  have hsum := Summable.of_nonneg_of_le hnn hpt (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hs.mul_left _)

/-- **Lipschitz bound** for `Gc`. -/
theorem norm_Gc_sub_le {σ : ℝ} (hσ : 0 < σ) {W W' : ℂ} (hW : σ ≤ W.re) (hW' : σ ≤ W'.re)
    (hs : Summable (fun n : ℕ => n * |c n| * Real.exp (-n * σ)))
    (hs0 : Summable (fun n : ℕ => |c n| * Real.exp (-n * σ))) :
    ‖Gc c W - Gc c W'‖ ≤ ‖W - W'‖ * ∑' n : ℕ, n * |c n| * Real.exp (-n * σ) := by
  have hmono : ∀ {V : ℂ}, σ ≤ V.re → ∀ n : ℕ, |c n| * Real.exp (-n * V.re) ≤
      |c n| * Real.exp (-n * σ) := by
    intro V hV n
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsW : Summable (fun n : ℕ => |c n| * Real.exp (-n * W.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (hmono hW) hs0
  have hsW' : Summable (fun n : ℕ => |c n| * Real.exp (-n * W'.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (hmono hW') hs0
  unfold Gc
  rw [← (summable_Gc_term c hsW).tsum_sub (summable_Gc_term c hsW')]
  have hterm : ∀ n : ℕ, ‖(c n : ℂ) * cexp (-(n : ℂ) * W) - (c n : ℂ) * cexp (-(n : ℂ) * W')‖ ≤
      ‖W - W'‖ * (n * |c n| * Real.exp (-n * σ)) := by
    intro n
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hconv : Convex ℝ {c : ℂ | σ ≤ c.re} := convex_halfSpace_re_ge σ
    have hd : ∀ x ∈ {c : ℂ | σ ≤ c.re}, DifferentiableAt ℂ (fun w : ℂ => cexp (-(n : ℂ) * w)) x :=
      fun x _ => by fun_prop
    have hb : ∀ x ∈ {c : ℂ | σ ≤ c.re}, ‖deriv (fun w : ℂ => cexp (-(n : ℂ) * w)) x‖ ≤
        n * Real.exp (-n * σ) := by
      intro x hx
      have hder : deriv (fun w : ℂ => cexp (-(n : ℂ) * w)) x = -(n : ℂ) * cexp (-(n : ℂ) * x) := by
        have := ((hasDerivAt_id x).const_mul (-(n : ℂ))).cexp
        simp only [mul_one, id] at this
        rw [this.deriv]; ring
      rw [hder, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_exp]
      gcongr
      simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.neg_im,
        Complex.natCast_im, neg_zero, zero_mul, sub_zero]
      have : σ ≤ x.re := hx
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := hconv.norm_image_sub_le_of_norm_deriv_le hd hb (show W' ∈ {c : ℂ | σ ≤ c.re} from hW')
      (show W ∈ {c : ℂ | σ ≤ c.re} from hW)
    calc |c n| * ‖cexp (-(n : ℂ) * W) - cexp (-(n : ℂ) * W')‖
        ≤ |c n| * (n * Real.exp (-n * σ) * ‖W - W'‖) := by gcongr
      _ = _ := by ring
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)
  · rw [← tsum_mul_left]
    exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)).tsum_le_tsum
      hterm (hs.mul_left _)

end generic

/-! ### The trivial bound for `cR` -/

lemma cAR_sq_eq (a : ℕ+) (N : ℤ) (h : (a : ℤ) ∣ N ∧ 0 ≤ N) :
    cAR a N ^ 2 = ((tau (N / a).toNat : ℤ) : ℝ) ^ 2 := by
  unfold cAR; rw [if_pos h]

lemma cAR_eq_zero (a : ℕ+) (N : ℤ) (h : ¬ ((a : ℤ) ∣ N ∧ 0 ≤ N)) : cAR a N = 0 := by
  unfold cAR; rw [if_neg h]

/-- `Σ_n cA(a, bn+ℓ)² e^{−nσ} ≤ e^{ℓσ/b} C₀ (aσ/b)^{−12}`. -/
lemma cAR_sq_laplace {C₀ : ℝ} (hT : ∀ σ : ℝ, 0 < σ →
      Summable (fun n : ℕ => (tau n : ℝ) ^ 2 * Real.exp (-n * σ)) ∧
        ∑' n : ℕ, (tau n : ℝ) ^ 2 * Real.exp (-n * σ) ≤ C₀ * σ ^ (-(12 : ℝ)))
    (a b : ℕ+) (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => cAR a ((b : ℤ) * n + ℓ) ^ 2 * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, cAR a ((b : ℤ) * n + ℓ) ^ 2 * Real.exp (-n * σ) ≤
        Real.exp (ℓ * σ / b) * (C₀ * (a * σ / b) ^ (-(12 : ℝ))) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  have hb : (0 : ℝ) < b := by exact_mod_cast b.pos
  set S : Set ℕ := {n | (a : ℤ) ∣ (b : ℤ) * n + ℓ ∧ 0 ≤ (b : ℤ) * n + ℓ}
  set f : ℕ → ℝ := fun n => cAR a ((b : ℤ) * n + ℓ) ^ 2 * Real.exp (-n * σ)
  set g : ℕ → ℝ := fun m => (tau m : ℝ) ^ 2 * Real.exp (-m * (a * σ / b))
  obtain ⟨hgs, hgb⟩ := hT (a * σ / b) (by positivity)
  set φ : S → ℕ := fun n => (((b : ℤ) * n + ℓ) / a).toNat
  have hφ : ∀ n : S, ((φ n : ℕ) : ℤ) * a = (b : ℤ) * n + ℓ := by
    intro n
    have h1 := n.2.1; have h2 := n.2.2
    simp only [φ]
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg h2 (by positivity)), Int.ediv_mul_cancel h1]
  have hφi : Function.Injective φ := by
    intro n n' h
    have e1 := hφ n; have e2 := hφ n'
    rw [h] at e1
    have : (b : ℤ) * n = b * n' := by linarith
    have hb0 : (b : ℤ) ≠ 0 := by positivity
    exact Subtype.ext (by exact_mod_cast mul_left_cancel₀ hb0 this)
  have hfS : ∀ n : S, f n = Real.exp (ℓ * σ / b) * g (φ n) := by
    intro n
    simp only [f, g]
    rw [cAR_sq_eq a _ n.2]
    have e : (((b : ℤ) * n + ℓ) / a).toNat = φ n := rfl
    rw [e]
    have e2 : (φ n : ℝ) * a = b * n + ℓ := by exact_mod_cast hφ n
    have e3 : (ℓ : ℝ) * σ / b + -(φ n : ℝ) * (a * σ / b) = -(n : ℝ) * σ := by
      rw [show (ℓ : ℝ) * σ / b + -(φ n : ℝ) * (a * σ / b) = σ * ((ℓ : ℝ) - φ n * a) / b by ring,
        e2]
      field_simp; ring
    rw [mul_left_comm, ← Real.exp_add, e3]
  have hsupp : Function.support f ⊆ S := by
    intro n hn
    by_contra hS
    apply hn
    simp only [f]
    rw [cAR_eq_zero a _ hS]; ring
  have hfS' : Summable (f ∘ (Subtype.val : S → ℕ)) := by
    have : f ∘ (Subtype.val : S → ℕ) = fun n => Real.exp (ℓ * σ / b) * g (φ n) :=
      funext hfS
    rw [this]
    exact (hgs.comp_injective hφi).mul_left _
  have hfsum : Summable f := by
    have := summable_subtype_iff_indicator.1 hfS'
    rwa [Set.indicator_eq_self.2 hsupp] at this
  refine ⟨hfsum, ?_⟩
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  have e : ∑' n : S, f n = Real.exp (ℓ * σ / b) * ∑' n : S, g (φ n) := by
    rw [← tsum_mul_left]; exact tsum_congr hfS
  rw [e]
  gcongr
  exact (tsum_comp_le_tsum_of_inj hgs (fun m => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    hφi).trans hgb

lemma abs_cR_le (a b : ℕ+) (ℓ : ℤ) (n : ℕ) :
    |cR a b ℓ n| ≤ ((tau n : ℝ) ^ 2 + cAR a ((b : ℤ) * n + ℓ) ^ 2) / 2 := by
  unfold cR
  rw [abs_mul]
  have := sq_abs ((tau n : ℤ) : ℝ)
  have := sq_abs (cAR a ((b : ℤ) * n + ℓ))
  push_cast at *
  nlinarith [sq_nonneg (|(tau n : ℝ)| - |cAR a ((b : ℤ) * n + ℓ)|)]

/-- **Trivial bound** for the coefficients of `G_{a,b,ℓ}`. -/
theorem cR_laplace : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (a b : ℕ+) (ℓ : ℤ) (σ : ℝ), 0 < σ →
    Summable (fun n : ℕ => |cR a b ℓ n| * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, |cR a b ℓ n| * Real.exp (-n * σ) ≤
        (C₀ * σ ^ (-(12 : ℝ)) + Real.exp (ℓ * σ / b) * (C₀ * (a * σ / b) ^ (-(12 : ℝ)))) / 2 := by
  obtain ⟨C₀, hC₀, hT⟩ := tau_sq_laplace
  refine ⟨C₀, hC₀, fun a b ℓ σ hσ => ?_⟩
  obtain ⟨hs1, hb1⟩ := hT σ hσ
  obtain ⟨hs2, hb2⟩ := cAR_sq_laplace hT a b ℓ hσ
  have hmaj : Summable (fun n : ℕ => ((tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
      cAR a ((b : ℤ) * n + ℓ) ^ 2 * Real.exp (-n * σ)) / 2) := (hs1.add hs2).div_const 2
  have hpt : ∀ n : ℕ, |cR a b ℓ n| * Real.exp (-n * σ) ≤ ((tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
      cAR a ((b : ℤ) * n + ℓ) ^ 2 * Real.exp (-n * σ)) / 2 := by
    intro n
    have := abs_cR_le a b ℓ n
    have he := Real.exp_pos (-n * σ)
    calc |cR a b ℓ n| * Real.exp (-n * σ) ≤ ((tau n : ℝ) ^ 2 + cAR a ((b : ℤ) * n + ℓ) ^ 2) / 2 *
          Real.exp (-n * σ) := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun n : ℕ => |cR a b ℓ n| * Real.exp (-n * σ)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hpt hmaj
  refine ⟨hsum, (hsum.tsum_le_tsum hpt hmaj).trans ?_⟩
  rw [tsum_div_const, hs1.tsum_add hs2]
  gcongr

end RamanujanTau.SCS2Coprime
