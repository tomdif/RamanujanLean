/-
# Growth and lower bounds for `L(Δ,s)` used in the Jensen zero count

* `tauL_norm_lower` : for `Re s > 13/2`, `‖L(Δ,s)‖ ≥ exp(−K(Re s))`, uniformly in `Im s`
  (Euler product: `1/L(s) = ∏_p P_p(s)` and `‖P_p(s) − 1‖ ≤ |τ(p)|p^{−σ} + p^{11−2σ}`).
* `tauL_poly_bound` : `‖L(Δ,s)‖ ≤ A (1+‖s‖)²` on `5 ≤ Re s ≤ 9` (convexity, `HeckeConvex`).
-/
import RamanujanTau.HeckeZeros.Main
import RamanujanTau.HeckeConvex.Main

namespace RamanujanTau.ZeroCount

open Complex LSeries Filter Topology
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex RamanujanTau.HeckeZeros

/-- The real majorant `|τ(p)| p^{−σ} + p^{11−2σ}` of `‖P_p(s) − 1‖` on `Re s = σ`. -/
noncomputable def gmaj (σ : ℝ) (p : Nat.Primes) : ℝ :=
  |(tau (p : ℕ) : ℝ)| * ((p : ℕ) : ℝ) ^ (-σ) + ((p : ℕ) : ℝ) ^ (11 - 2 * σ)

lemma gmaj_nonneg (σ : ℝ) (p : Nat.Primes) : 0 ≤ gmaj σ p := by
  unfold gmaj; positivity

lemma norm_localPoly_sub_one_le (s : ℂ) (p : Nat.Primes) :
    ‖localPoly s p - 1‖ ≤ gmaj s.re p := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have e : localPoly s p - 1 = -(tauC p * (p : ℂ) ^ (-s)) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2 := by
    simp only [localPoly]; ring
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    norm_natCast_cpow_of_pos p.2.pos, neg_re]
  unfold gmaj
  congr 1
  · simp [tauC, Complex.norm_intCast]
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
    congr 1; push_cast; ring

lemma summable_gmaj {σ : ℝ} (hσ : 13 / 2 < σ) : Summable (gmaj σ) := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hA := (summable_abs_tau_div_rpow hσ).comp_injective hinj
  have hB : Summable fun n : ℕ => (n : ℝ) ^ (11 - 2 * σ) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine (hA.add (hB.comp_injective hinj)).congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  simp only [Function.comp_apply, gmaj, div_eq_mul_inv, Real.rpow_neg hp.le]

/-- The constant `K(σ) = ∑_p (|τ(p)| p^{−σ} + p^{11−2σ})`. -/
noncomputable def Kconst (σ : ℝ) : ℝ := ∑' p, gmaj σ p

/-- **Euler-product lower bound**: for `Re s > 13/2`, `exp(−K(Re s)) ≤ ‖L(Δ,s)‖`. -/
theorem tauL_norm_lower {s : ℂ} (hs : 13 / 2 < s.re) :
    Real.exp (-Kconst s.re) ≤ ‖tauL s‖ := by
  set f : Nat.Primes → ℂ := fun p => localPoly s p - 1
  have hsum := summable_localPoly_sub_one hs
  have hP : HasProd (fun p => 1 + f p) (∏' p, (1 + f p)) :=
    (multipliable_one_add_of_summable hsum).hasProd
  have hE := tauL_eulerProduct hs
  have hprod := hP.mul hE
  have h1 : (fun p : Nat.Primes => (1 + f p) *
      (1 - tauC p * (p : ℂ) ^ (-s) + (p : ℂ) ^ 11 * ((p : ℂ) ^ (-s)) ^ 2)⁻¹) = fun _ => 1 := by
    funext p
    have := localPoly_ne_zero hs p.2
    simp only [f, add_sub_cancel]
    exact mul_inv_cancel₀ this
  rw [h1] at hprod
  have hQL : (∏' p, (1 + f p)) * tauL s = 1 := hprod.unique hasProd_one
  -- norm bound for the product
  have hg := summable_gmaj hs
  have hQ : ‖∏' p, (1 + f p)‖ ≤ Real.exp (Kconst s.re) := by
    have ht : Tendsto (fun F : Finset Nat.Primes => ∏ p ∈ F, ‖1 + f p‖) atTop
        (𝓝 ‖∏' p, (1 + f p)‖) := hP.norm
    refine le_of_tendsto' ht fun F => ?_
    calc ∏ p ∈ F, ‖1 + f p‖ ≤ ∏ p ∈ F, (1 + gmaj s.re p) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ?_
          refine (norm_add_le _ _).trans ?_
          rw [norm_one]; linarith [norm_localPoly_sub_one_le s p]
      _ ≤ Real.exp (∑ p ∈ F, gmaj s.re p) :=
          Real.prod_one_add_le_exp_sum _ (gmaj_nonneg _)
      _ ≤ Real.exp (Kconst s.re) :=
          Real.exp_le_exp.mpr (hg.sum_le_tsum _ fun p _ => gmaj_nonneg _ p)
  have hn : ‖∏' p, (1 + f p)‖ * ‖tauL s‖ = 1 := by rw [← norm_mul, hQL, norm_one]
  have hQpos : 0 < ‖∏' p, (1 + f p)‖ := by
    rcases (norm_nonneg (∏' p, (1 + f p))).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hn; exact absurd hn zero_ne_one
  rw [Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  calc (1 : ℝ) = ‖∏' p, (1 + f p)‖ * ‖tauL s‖ := hn.symm
    _ ≤ Real.exp (Kconst s.re) * ‖tauL s‖ := by gcongr
    _ = _ := by ring

/-- **Polynomial growth on `5 ≤ Re s ≤ 9`**: `‖L(Δ,s)‖ ≤ A (1 + ‖s‖)²`. -/
theorem tauL_poly_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 5 ≤ s.re → s.re ≤ 9 →
    ‖tauL s‖ ≤ A * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := fC_bound (ε := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨D, hD0, hD⟩ := tauL_bounded_of_gt (σ := 7) (by norm_num)
  refine ⟨2 * Real.exp 10 * C + D, by positivity, fun s h1 h2 => ?_⟩
  have hb : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hsq : (1 : ℝ) ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ hb
  rcases le_or_gt 7 s.re with h7 | h7
  · calc ‖tauL s‖ ≤ D := hD s h7
      _ ≤ D * (1 + ‖s‖) ^ 2 := le_mul_of_one_le_right hD0 hsq
      _ ≤ _ := by
          have : 0 ≤ 2 * Real.exp 10 * C * (1 + ‖s‖) ^ 2 := by positivity
          nlinarith
  · have hL := tauL_line (ε := 1 / 2) (by norm_num) (by norm_num) hC (s := s)
      (by linarith) (by linarith)
    set θ : ℝ := 13 / 2 + 1 / 2 - s.re with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ2 : θ ≤ 2 := by rw [hθ]; linarith
    have hn : ‖s / 2‖ ≤ 1 + ‖s‖ := by
      rw [norm_div, Complex.norm_two]; linarith [norm_nonneg s]
    have hp : ‖s / 2‖ ^ θ ≤ (1 + ‖s‖) ^ 2 := by
      calc ‖s / 2‖ ^ θ ≤ (1 + ‖s‖) ^ θ := Real.rpow_le_rpow (norm_nonneg _) hn hθ0
        _ ≤ (1 + ‖s‖) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hθ2
        _ = (1 + ‖s‖) ^ 2 := by norm_cast
    calc ‖tauL s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
      _ ≤ 2 * Real.exp 10 * C * (1 + ‖s‖) ^ 2 := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hD0 (by positivity : (0:ℝ) ≤ (1 + ‖s‖) ^ 2)]

end RamanujanTau.ZeroCount
