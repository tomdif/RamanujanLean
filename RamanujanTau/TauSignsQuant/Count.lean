/-
# Counting form: `#{p < x : τ(p) > 0} ≥ x^θ` for arbitrarily large `x`, every `θ < 9/20`

General lemma `count_frequently_of_not_summable`: if `∑_{n : P n} n^{−β} = ∞` and `0 < θ < β`, then
`Nat.count P x ≥ x^θ` for arbitrarily large `x`.  Proof: otherwise `count P x < x^θ` for `x ≥ X`;
the `m`-th element `q_m = nth P m` has `count P q_m = m`, so `m < q_m^θ`, `q_m > m^{1/θ}`,
`q_m^{−β} < m^{−β/θ}`, summable since `β/θ > 1`; and `m ↦ q_m` enumerates `{P}`.
-/
import RamanujanTau.TauSignsQuant.Density

set_option autoImplicit false

namespace RamanujanTau.TauSignsQuant

open Filter Topology

lemma count_frequently_of_not_summable {P : ℕ → Prop} [DecidablePred P] {θ β : ℝ}
    (hθ : 0 < θ) (hθβ : θ < β)
    (hns : ¬ Summable (fun n : ℕ => if P n then (n : ℝ) ^ (-β) else 0)) (X : ℕ) :
    ∃ x, X ≤ x ∧ (x : ℝ) ^ θ ≤ (Nat.count P x : ℝ) := by
  by_contra hcon
  push Not at hcon
  set f : ℕ → ℝ := fun n => if P n then (n : ℝ) ^ (-β) else 0
  have hβ : 0 < β := by linarith
  -- `{P}` is infinite
  have hinf : (setOf P).Infinite := by
    intro hfin
    refine hns (summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_)
    have : ¬ P n := fun h => hn (hfin.mem_toFinset.mpr h)
    show f n = 0
    simp only [f, if_neg this]
  have hmono := Nat.nth_strictMono hinf
  set q := Nat.nth P
  -- the bound for `m ≥ X + 1`
  have hb : ∀ m : ℕ, X + 1 ≤ m → f (q m) ≤ (m : ℝ) ^ (-(β / θ)) := by
    intro m hm
    have hmq : m ≤ q m := hmono.id_le m
    have hPq : P (q m) := Nat.nth_mem_of_infinite hinf m
    have hc := hcon (q m) (by omega)
    rw [Nat.count_nth_of_infinite hinf] at hc
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hq0 : (0 : ℝ) < q m := by linarith [(by exact_mod_cast hmq : (m : ℝ) ≤ q m)]
    have h1 : (m : ℝ) ^ (1 / θ) < q m := by
      have := Real.rpow_lt_rpow (by positivity) hc (by positivity : 0 < 1 / θ)
      rwa [← Real.rpow_mul hq0.le, mul_one_div_cancel hθ.ne', Real.rpow_one] at this
    simp only [f, if_pos hPq]
    calc (q m : ℝ) ^ (-β) ≤ ((m : ℝ) ^ (1 / θ)) ^ (-β) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1.le (by linarith)
      _ = (m : ℝ) ^ (-(β / θ)) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
  have hgs : Summable fun n : ℕ => ((n + (X + 1) : ℕ) : ℝ) ^ (-(β / θ)) :=
    (summable_nat_add_iff (X + 1)).mpr
      (Real.summable_nat_rpow.mpr (by
        have : 1 < β / θ := (one_lt_div hθ).mpr hθβ
        linarith))
  have hfq : Summable (f ∘ q) := by
    refine (summable_nat_add_iff (X + 1)).mp ?_
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => hb _ (by omega)) hgs
    simp only [Function.comp, f]; split_ifs <;> positivity
  refine hns ((Nat.nth_injective hinf).summable_iff (fun n hn => ?_) |>.mp hfq)
  rw [Nat.range_nth_of_infinite hinf] at hn
  simp only [f, if_neg (show ¬ P n from hn)]

lemma count_frequently_all {P : ℕ → Prop} [DecidablePred P]
    (hns : ∀ β : ℝ, β < 9 / 20 → ¬ Summable (fun n : ℕ => if P n then (n : ℝ) ^ (-β) else 0))
    {θ : ℝ} (hθ : θ < 9 / 20) (X : ℕ) :
    ∃ x, X ≤ x ∧ (x : ℝ) ^ θ ≤ (Nat.count P x : ℝ) := by
  set θ' : ℝ := max θ (1 / 5)
  have hθ' : 0 < θ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hθ'9 : θ' < 9 / 20 := max_lt hθ (by norm_num)
  obtain ⟨x, hx, hc⟩ := count_frequently_of_not_summable (P := P) hθ'
    (show θ' < (θ' + 9 / 20) / 2 by linarith) (hns _ (by linarith)) (X + 1)
  refine ⟨x, by omega, le_trans ?_ hc⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ x)) (le_max_left _ _)

/-- **Quantitative sign changes, unconditional**: for every `θ < 9/20` there are arbitrarily
large `x` with `#{p < x prime : τ(p) > 0} ≥ x^θ`. -/
theorem tau_pos_count_frequently {θ : ℝ} (hθ : θ < 9 / 20) (X : ℕ) :
    ∃ x, X ≤ x ∧
      (x : ℝ) ^ θ ≤ (((Finset.range x).filter (fun p => p.Prime ∧ 0 < tau p)).card : ℝ) := by
  obtain ⟨x, hx, h⟩ := count_frequently_all (P := fun p => p.Prime ∧ 0 < tau p)
    (fun β hβ => not_summable_tau_pos hβ) hθ X
  exact ⟨x, hx, by rwa [Nat.count_eq_card_filter_range] at h⟩

/-- **Quantitative sign changes, unconditional**: for every `θ < 9/20` there are arbitrarily
large `x` with `#{p < x prime : τ(p) < 0} ≥ x^θ`. -/
theorem tau_neg_count_frequently {θ : ℝ} (hθ : θ < 9 / 20) (X : ℕ) :
    ∃ x, X ≤ x ∧
      (x : ℝ) ^ θ ≤ (((Finset.range x).filter (fun p => p.Prime ∧ tau p < 0)).card : ℝ) := by
  obtain ⟨x, hx, h⟩ := count_frequently_all (P := fun p => p.Prime ∧ tau p < 0)
    (fun β hβ => not_summable_tau_neg hβ) hθ X
  exact ⟨x, hx, by rwa [Nat.count_eq_card_filter_range] at h⟩

end RamanujanTau.TauSignsQuant
