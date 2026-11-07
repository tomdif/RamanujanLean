/-
# M3 step 2b: peeling a prime power from the twisted sum

`Bs u v h k α = Σ_r λ(hr)λ(kr) r^{−1} r^{iv} W̃_{u,u+v}(αr²)`.  For a prime `p ∤ h'k`
(`HafnerBridge2.T_peel`: `λ(p^a h' r)λ(kr) = Σ_{p^j ∣ r} g_j λ(h' r/p^j)λ(k r/p^j)`):

    Bs (p^a h') k α = Σ_j g_j (p^{−(1−iv)})^j · Bs h' k (α p^{2j})      (`Bs_peel`).

Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.BaseFull
import RamanujanTau.SelbergKeyDiag2.EvalC
import RamanujanTau.HafnerBridge2.Twisted

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology Finset RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2 RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2
open scoped Real

/-- The twisted sum `Σ_r λ(hr)λ(kr) r^{−1} · r^{iv} W̃(αr²)`. -/
noncomputable def Bs (u v : ℝ) (h k : ℕ) (α : ℝ) : ℂ :=
  ∑' r : ℕ, ((T h k r / r : ℝ) : ℂ) * ft u v α r

lemma abs_lam_le_lin {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
    (n : ℕ) : |lam n| ≤ C * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lam_zero]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  refine (hC n hn).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  calc (n : ℝ) ^ (11 / 40 : ℝ) ≤ (n : ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    _ = n := Real.rpow_one _

lemma abs_T_le {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
    (h k m : ℕ) : |T h k m| ≤ C ^ 2 * (h * k : ℕ) * (m : ℝ) ^ 2 := by
  unfold T
  rw [abs_mul]
  have h1 := abs_lam_le_lin hC1 hC (h * m)
  have h2 := abs_lam_le_lin hC1 hC (k * m)
  calc |lam (h * m)| * |lam (k * m)| ≤ (C * (h * m : ℕ)) * (C * (k * m : ℕ)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

lemma ft_bound3 : ∃ K : ℝ, 0 ≤ K ∧ ∀ u v α t : ℝ, 0 < α → 0 < t →
    ‖ft u v α t‖ ≤ K * (TT u v / α) ^ 3 * t⁻¹ ^ 6 := by
  obtain ⟨C, hC0, hC⟩ := Wsh_bound (A := 3) (by norm_num)
  refine ⟨C, hC0, fun u v α t hα ht => ?_⟩
  rw [norm_ft_eq u v ht]
  have hT := TT_pos u v
  have hx : 0 < α * t ^ 2 / TT u v := by positivity
  have h := hC u (u + v) (α * t ^ 2) (by positivity)
  have h3 : (1 + α * t ^ 2 / TT u v) ^ (-(3:ℝ)) ≤ (α * t ^ 2 / TT u v)⁻¹ ^ 3 := by
    rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hx.le (by linarith) 3)
  unfold TT at h3 hx
  refine h.trans ((mul_le_mul_of_nonneg_left h3 hC0).trans (le_of_eq ?_))
  unfold TT
  have := Tq_pos u; have := Tq_pos (u + v)
  field_simp

/-- The rescaling identity `p^{−j}(p^j r)^{iv} = (p^{−(1−iv)})^j r^{iv}`. -/
lemma ft_rescale (u v : ℝ) {p : ℕ} (hp : p.Prime) (α : ℝ) (j r : ℕ) (hr : 1 ≤ r) (F : ℝ) :
    ((F / ((p ^ j * r : ℕ) : ℝ) : ℝ) : ℂ) * ft u v α ((p ^ j * r : ℕ) : ℝ) =
      ((p : ℂ) ^ (-(1 - (v : ℂ) * I))) ^ j * (((F / r : ℝ) : ℂ) * ft u v (α * (p : ℝ) ^ (2 * j)) r) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hpj : (0:ℝ) < (p : ℝ) ^ j := by positivity
  unfold ft
  have e1 : (((p ^ j * r : ℕ) : ℝ) : ℂ) ^ ((v : ℂ) * I) =
      cexp (((j : ℝ) * Real.log p : ℝ) * ((v : ℂ) * I)) * ((r : ℝ) : ℂ) ^ ((v : ℂ) * I) := by
    rw [cpow_eq_exp (by push_cast; positivity), cpow_eq_exp hr0, ← Complex.exp_add]
    congr 1
    push_cast
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_pow]
    push_cast; ring
  have e2 : ((p : ℂ) ^ (-(1 - (v : ℂ) * I))) ^ j =
      cexp ((-(j : ℝ) * Real.log p : ℝ) * (1 - (v : ℂ) * I)) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, cpow_eq_exp hp0, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : α * (((p ^ j * r : ℕ) : ℝ)) ^ 2 = α * (p : ℝ) ^ (2 * j) * (r : ℝ) ^ 2 := by
    push_cast; ring
  rw [e1, e2, e3]
  have e4 : ((F / ((p ^ j * r : ℕ) : ℝ) : ℝ) : ℂ) =
      cexp ((-(j : ℝ) * Real.log p : ℝ)) * ((F / r : ℝ) : ℂ) := by
    have hr4 : F / ((p ^ j * r : ℕ) : ℝ) = Real.exp (-(j : ℝ) * Real.log p) * (F / r) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp0]
      push_cast; field_simp
    rw [hr4, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [e4]
  have e5 : cexp ((-(j : ℝ) * Real.log p : ℝ) * (1 - (v : ℂ) * I)) =
      cexp ((-(j : ℝ) * Real.log p : ℝ)) * cexp (((j : ℝ) * Real.log p : ℝ) * ((v : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e5]
  ring

/-- **Peeling identity** (exact). -/
theorem Bs_peel (u v : ℝ) {p a h' k : ℕ} (hp : p.Prime) (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k) {α : ℝ}
    (hα : 0 < α) :
    Bs u v (p ^ a * h') k α = ∑' j : ℕ, ((gseq p a j : ℝ) : ℂ) * ((p : ℂ) ^ (-(1 - (v : ℂ) * I))) ^ j *
      Bs u v h' k (α * (p : ℝ) ^ (2 * j)) := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  obtain ⟨K3, hK30, hK3⟩ := ft_bound3
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  set x : ℂ := (p : ℂ) ^ (-(1 - (v : ℂ) * I)) with hx
  set D : ℕ → ℕ → ℂ := fun j r => if p ^ j ∣ r then
    ((gseq p a j : ℝ) : ℂ) * ((T h' k (r / p ^ j) / r : ℝ) : ℂ) * ft u v α r else 0 with hD
  -- step 1: each term is a finite sum over `j`
  have hterm : ∀ r : ℕ, ((T (p ^ a * h') k r / r : ℝ) : ℂ) * ft u v α r = ∑' j, D j r := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hD]
    rw [tsum_eq_sum (s := Finset.range (r + 1)) (fun j hj => ?_)]
    · rw [T_peel hp hph hpk hr, conv, Finset.sum_div, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hD]
      split_ifs <;> push_cast <;> ring
    · rw [Finset.mem_range, not_lt] at hj
      simp only [hD]
      rw [if_neg]
      intro hd
      have h1 := Nat.le_of_dvd hr hd
      have h2 : j < p ^ j := Nat.lt_pow_self hp.one_lt
      omega
  -- summability of the double series
  set G : ℝ := (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a))
  have hG0 : 0 ≤ G := by positivity
  have hg : ∀ j : ℕ, |gseq p a j| ≤ G * ((j + 1) * (p : ℝ) ^ j) := by
    intro j
    have h0 := abs_gseq_le hC1 hC hp a j
    have hpw : (p : ℝ) ^ ((11 / 20 : ℝ) * j) ≤ (p : ℝ) ^ j := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by have := Nat.cast_nonneg (α := ℝ) j; nlinarith)
    refine h0.trans ?_
    calc ((j : ℝ) + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) *
          (p : ℝ) ^ ((11 / 20 : ℝ) * j))
        ≤ ((j : ℝ) + 1) * (4 + 2 * lam p ^ 2) * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * (p : ℝ) ^ j) := by
          gcongr
      _ = _ := by simp only [G]; ring
  set M : ℝ := G * (C ^ 2 * (h' * k : ℕ)) * (K3 * (TT u v / α) ^ 3)
  have hM0 : 0 ≤ M := by have := TT_pos u v; positivity
  have hDb : ∀ j r : ℕ, ‖D j r‖ ≤ M * (((j + 1) * (1 / 4 : ℝ) ^ j) * ((r : ℝ) ^ 2)⁻¹) := by
    intro j r
    simp only [hD]
    split_ifs with hd
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      have hr0 : (0:ℝ) < r := by linarith
      have hpj : (p : ℝ) ^ j ≤ r := by exact_mod_cast Nat.le_of_dvd hr hd
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_div, Nat.abs_cast]
      have h1 := hg j
      have h2 := abs_T_le hC1 hC h' k (r / p ^ j)
      have h2' : ((r / p ^ j : ℕ) : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
        gcongr; exact_mod_cast Nat.div_le_self r (p ^ j)
      have h3 := hK3 u v α r hα hr0
      have hpj0 : (0:ℝ) < (p : ℝ) ^ j := by positivity
      -- `(j+1) p^j r^{−5} ≤ (j+1) 4^{−j} r^{−2}`
      have key : (p : ℝ) ^ j * (r : ℝ) * ((r : ℝ)⁻¹ ^ 6) ≤ (1 / 4 : ℝ) ^ j * ((r : ℝ) ^ 2)⁻¹ := by
        have e : (p : ℝ) ^ j * r * (r : ℝ)⁻¹ ^ 6 = (p : ℝ) ^ j * ((r : ℝ) ^ 3)⁻¹ * ((r : ℝ) ^ 2)⁻¹ := by
          field_simp
        rw [e]
        gcongr
        have hr3 : ((p : ℝ) ^ j) ^ 3 ≤ (r : ℝ) ^ 3 := by gcongr
        rw [mul_inv_le_iff₀ (by positivity)]
        calc (p : ℝ) ^ j ≤ (p : ℝ) ^ j * ((p : ℝ) ^ j) ^ 2 * (1 / 4) ^ j := by
              have : (1:ℝ) ≤ ((p : ℝ) ^ j) ^ 2 * (1 / 4) ^ j := by
                rw [← pow_mul, show (p : ℝ) ^ (j * 2) = ((p : ℝ) ^ 2) ^ j by ring, ← mul_pow]
                exact one_le_pow₀ (by nlinarith)
              nlinarith
          _ = (1 / 4) ^ j * ((p : ℝ) ^ j) ^ 3 := by ring
          _ ≤ (1 / 4) ^ j * (r : ℝ) ^ 3 := by gcongr
      calc |gseq p a j| * (|T h' k (r / p ^ j)| / r) * ‖ft u v α r‖
          ≤ (G * ((j + 1) * (p : ℝ) ^ j)) * (C ^ 2 * (h' * k : ℕ) * (r : ℝ) ^ 2 / r) *
              (K3 * (TT u v / α) ^ 3 * (r : ℝ)⁻¹ ^ 6) := by
            gcongr
            exact h2.trans (by gcongr)
        _ = M * ((j + 1) * ((p : ℝ) ^ j * r * (r : ℝ)⁻¹ ^ 6)) := by
            simp only [M]; field_simp
        _ ≤ M * ((j + 1) * ((1 / 4 : ℝ) ^ j * ((r : ℝ) ^ 2)⁻¹)) := by gcongr
        _ = _ := by ring
    · simp; positivity
  have hs1 : Summable fun j : ℕ => ((j : ℝ) + 1) * (1 / 4 : ℝ) ^ j := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)
    have h2 := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)
    exact (h1.add h2).congr fun j => by simp; ring
  have hs2 : Summable fun r : ℕ => ((r : ℝ) ^ 2)⁻¹ := Real.summable_nat_pow_inv.2 (by norm_num)
  have hprod := (Summable.mul_of_nonneg hs1 hs2 (fun j => by positivity) (fun r => by positivity)).mul_left M
  have hsumm : Summable (Function.uncurry D) := by
    refine Summable.of_norm_bounded hprod (fun q => ?_)
    obtain ⟨j, r⟩ := q
    exact hDb j r
  -- assemble
  unfold Bs
  rw [tsum_congr hterm, hsumm.tsum_comm]
  refine tsum_congr fun j => ?_
  have hinj : Function.Injective fun r' : ℕ => p ^ j * r' :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) h
  rw [← hinj.tsum_eq (f := fun r => D j r) (fun r hr => ?_)]
  · rw [← tsum_mul_left]
    refine tsum_congr fun r' => ?_
    simp only [hD]
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos hp.pos j)]
    rcases Nat.eq_zero_or_pos r' with rfl | hr'
    · simp [T, lam_zero]
    rw [mul_assoc, ft_rescale u v hp α j r' hr' (T h' k r')]
    ring
  · rw [Function.mem_support] at hr
    simp only [hD] at hr
    split_ifs at hr with hd
    · obtain ⟨r', rfl⟩ := hd; exact ⟨r', rfl⟩
    · exact absurd rfl hr

end RamanujanTau.SelbergKeyDiag2
