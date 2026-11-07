/-
# A real-variable Selberg–Delange theorem for logarithmic means

**Theorem** (`logmean_LSD`).  Let `f, g` be real arithmetic functions with
`f(n) log n = (g ∗ f)(n)` (`g = Λ_f`), let `−1 < κ`, `0 < σ < 1`, `σ ≤ 1 + κ`, and suppose

* (Mertens with error) `|Σ_{m≤y} g(m)/m − κ log y − c₀| ≤ B/(1 + log y)` for `y ≥ 1`;
* (density of `|f|`) `Σ_{n≤y} |f(n)| ≤ K y (1 + log y)^{σ−1}` for `y ≥ 1`.

Then there are `C₁, K₁, X₀` with, for `x ≥ X₀`,

  `|Σ_{n≤x} f(n)/n − C₁ (log x − c₀)^κ| ≤ K₁ (1 + log(1 + log x)) (log x)^{κ−1}`.

Proof: `key_identity` gives `(t − c₀)Ŝ = (1+κ)Î + R̂` (`t = log x`), so
`ψ(t) = Î(t)(t − c₀)^{−(1+κ)}` has right derivative `R̂(t)(t−c₀)^{−2−κ}`;
`|R̂| ≤ B·W ≪ (1+log t) t^{σ−1}` (`weight_bound`); `limit_of_deriv_bound` gives
`ψ = C + O((1+log t)t^{−(2+κ−σ)})`; finally `Ŝ = ((1+κ)Î + R̂)/(t−c₀)`.
-/
import RamanujanTau.SelbergDelange2.ODE
import RamanujanTau.SelbergDelange2.Weight

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange2

open Finset Set Filter Topology ArithmeticFunction

/-- `|R(x)| ≤ B·W(x)`. -/
lemma Rsum_bound (f g : ℕ → ℝ) {κ c₀ B : ℝ}
    (hM : ∀ y : ℝ, 1 ≤ y → |Err g κ c₀ y| ≤ B / (1 + Real.log y)) {x : ℝ} (hx : 1 ≤ x) :
    |Rsum f g κ c₀ x| ≤ B * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |f n| / n / (1 + Real.log (x / n)) := by
  have hx0 : 0 < x := by linarith
  rw [Rsum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
  have hxn : 1 ≤ x / n := by
    rw [le_div_iff₀ hn0, one_mul]
    exact (Nat.cast_le.2 (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le hx0.le)
  have hl : 0 ≤ Real.log (x / n) := Real.log_nonneg hxn
  rw [abs_mul, abs_div, Nat.abs_cast]
  have := hM (x / n) hxn
  calc |f n| / n * |Err g κ c₀ (x / n)| ≤ |f n| / n * (B / (1 + Real.log (x / n))) := by
        gcongr
    _ = B * (|f n| / n / (1 + Real.log (x / n))) := by ring

lemma rpow_shift_le {κ c₀ t : ℝ} (ht : 2 * |c₀| + 2 ≤ t) :
    (t - c₀) ^ κ ≤ ((1 / 2) ^ κ + (3 / 2) ^ κ) * t ^ κ := by
  have ht0 : 0 < t := by linarith [abs_nonneg c₀]
  have hc := le_abs_self c₀
  have hc' := neg_abs_le c₀
  have h1 : t / 2 ≤ t - c₀ := by linarith
  have h2 : t - c₀ ≤ 3 / 2 * t := by linarith
  have e1 : (t / 2) ^ κ = (1 / 2) ^ κ * t ^ κ := by
    rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) ht0.le]; norm_num
  have e2 : (3 / 2 * t) ^ κ = (3 / 2) ^ κ * t ^ κ := Real.mul_rpow (by norm_num) ht0.le
  have p1 : 0 ≤ (1 / 2 : ℝ) ^ κ * t ^ κ := by positivity
  have p2 : 0 ≤ (3 / 2 : ℝ) ^ κ * t ^ κ := by positivity
  rcases le_or_gt 0 κ with hk | hk
  · have := Real.rpow_le_rpow (by linarith) h2 hk
    rw [e2] at this; nlinarith
  · have := Real.rpow_le_rpow_of_nonpos (by positivity) h1 hk.le
    rw [e1] at this; nlinarith

set_option maxHeartbeats 4000000 in
/-- **Real-variable Selberg–Delange theorem for logarithmic means.** -/
theorem logmean_LSD (f g : ArithmeticFunction ℝ) {κ c₀ σ B K : ℝ} (hκ : -1 < κ) (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hσκ : σ ≤ 1 + κ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hconv : ∀ n : ℕ, 0 < n → f n * Real.log n = (g * f) n)
    (hM : ∀ y : ℝ, 1 ≤ y → |Err g κ c₀ y| ≤ B / (1 + Real.log y))
    (hC : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |f n| ≤ K * y * (1 + Real.log y) ^ (σ - 1)) :
    ∃ C₁ K₁ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      |Ssum f x - C₁ * (Real.log x - c₀) ^ κ| ≤
        K₁ * (1 + Real.log (1 + Real.log x)) * Real.log x ^ (κ - 1) := by
  set β : ℝ := 2 + κ - σ with hβ
  have hβ1 : 1 ≤ β := by linarith
  have hβ0 : 0 < β := by linarith
  set a₀ : ℝ := 2 * |c₀| + 2 with ha₀
  have ha₀2 : 2 ≤ a₀ := by have := abs_nonneg c₀; linarith
  set E : ℝ := Real.exp 1 * K * (2 + 2 / σ) with hE
  have hE0 : 0 ≤ E := by positivity
  -- `|R(e^t)| ≤ B E (1+log(1+t)) t^{σ−1}`
  have hR : ∀ t : ℝ, 2 ≤ t →
      |Rsum f g κ c₀ (Real.exp t)| ≤ B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 1)) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hx1 : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
    have h1 := Rsum_bound f g hM hx1
    have h2 := weight_bound f hσ0 hσ1 hK hC hx1
    rw [Real.log_exp] at h2
    have hlog : 1 ≤ Real.log (1 + t) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
    have h3 : (2 + t) ^ (σ - 1) ≤ t ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
    have h4 : 2 * (1 + Real.log (1 + t)) + 2 / σ ≤ (2 + 2 / σ) * (1 + Real.log (1 + t)) := by
      have : 0 ≤ 2 / σ := by positivity
      nlinarith
    have hp : 0 ≤ (2 + t) ^ (σ - 1) := by positivity
    have h5 : (2 * (1 + Real.log (1 + t)) + 2 / σ) * (2 + t) ^ (σ - 1) ≤
        (2 + 2 / σ) * ((1 + Real.log (1 + t)) * t ^ (σ - 1)) := by
      calc (2 * (1 + Real.log (1 + t)) + 2 / σ) * (2 + t) ^ (σ - 1)
          ≤ ((2 + 2 / σ) * (1 + Real.log (1 + t))) * t ^ (σ - 1) := by
            apply mul_le_mul h4 h3 hp; positivity
        _ = _ := by ring
    calc |Rsum f g κ c₀ (Real.exp t)| ≤ B * (Real.exp 1 * K *
          ((2 * (1 + Real.log (1 + t)) + 2 / σ) * (2 + t) ^ (σ - 1))) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hB)
      _ ≤ B * (Real.exp 1 * K * ((2 + 2 / σ) * ((1 + Real.log (1 + t)) * t ^ (σ - 1)))) := by
          gcongr
      _ = B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 1)) := by rw [hE]; ring
  -- the function ψ
  set p : ℝ := -(1 + κ) with hp
  set ψ : ℝ → ℝ := fun u => Isum f (Real.exp u) * (u - c₀) ^ p with hψ
  set ψ' : ℝ → ℝ := fun u => Rsum f g κ c₀ (Real.exp u) * (u - c₀) ^ (p - 1) with hψ'
  have hshift : ∀ t, a₀ ≤ t → t / 2 ≤ t - c₀ := by
    intro t ht; have := le_abs_self c₀; linarith
  have hder : ∀ t, a₀ ≤ t → HasDerivWithinAt ψ (ψ' t) (Ici t) t := by
    intro t ht
    have hpos : 0 < t - c₀ := by have := hshift t ht; linarith
    have h1 := Ihat_hasDeriv f t
    have h2 : HasDerivAt (fun u : ℝ => (u - c₀) ^ p) (1 * p * (t - c₀) ^ (p - 1)) t :=
      ((hasDerivAt_id t).sub_const c₀).rpow_const (Or.inl hpos.ne')
    have h3 := h1.mul h2.hasDerivWithinAt
    refine h3.congr_deriv ?_
    have hx1 : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
    have hid := key_identity f g hconv κ c₀ hx1
    rw [Real.log_exp] at hid
    have e : (t - c₀) ^ p = (t - c₀) * (t - c₀) ^ (p - 1) := by
      rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one hpos.ne']; ring_nf
    simp only [hψ']
    rw [e]
    have : Ssum f (Real.exp t) * ((t - c₀) * (t - c₀) ^ (p - 1)) +
        Isum f (Real.exp t) * (1 * p * (t - c₀) ^ (p - 1)) =
        ((t - c₀) * Ssum f (Real.exp t) + p * Isum f (Real.exp t)) * (t - c₀) ^ (p - 1) := by ring
    rw [this, hid, hp]; ring
  have hcont : ∀ b, ContinuousOn ψ (Icc a₀ b) := by
    intro b
    refine (Ihat_continuousOn f a₀ b).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_id.sub continuousOn_const) fun u hu => Or.inl ?_
    have := hshift u hu.1
    have h2 : a₀ ≤ u := hu.1
    have h : (0 : ℝ) < u - c₀ := by linarith
    exact h.ne'
  set D : ℝ := B * E * 2 ^ (2 + κ) with hD
  have hD0 : 0 ≤ D := by positivity
  have hbd : ∀ t, a₀ ≤ t → |ψ' t| ≤ D * ((1 + Real.log (1 + t)) * t ^ (-β - 1)) := by
    intro t ht
    have ht2 : 2 ≤ t := ha₀2.trans ht
    have ht0 : 0 < t := by linarith
    have hpos : 0 < t - c₀ := by have := hshift t ht; linarith
    have hq : (t - c₀) ^ (p - 1) ≤ 2 ^ (2 + κ) * t ^ (-2 - κ) := by
      have hpm : p - 1 = -2 - κ := by rw [hp]; ring
      rw [hpm]
      have := Real.rpow_le_rpow_of_nonpos (by positivity) (hshift t ht) (by linarith : -2 - κ ≤ 0)
      refine this.trans (le_of_eq ?_)
      rw [div_eq_mul_inv, Real.mul_rpow ht0.le (by norm_num), mul_comm, Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      ring_nf
    have hlog0 : 0 ≤ 1 + Real.log (1 + t) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + t by linarith); linarith
    have hexp : t ^ (σ - 1) * t ^ (-2 - κ) = t ^ (-β - 1) := by
      rw [← Real.rpow_add ht0, hβ]; ring_nf
    simp only [hψ']
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    calc |Rsum f g κ c₀ (Real.exp t)| * (t - c₀) ^ (p - 1)
        ≤ (B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 1))) * (2 ^ (2 + κ) * t ^ (-2 - κ)) := by
          apply mul_le_mul (hR t ht2) hq (by positivity) (by positivity)
      _ = D * ((1 + Real.log (1 + t)) * (t ^ (σ - 1) * t ^ (-2 - κ))) := by rw [hD]; ring
      _ = D * ((1 + Real.log (1 + t)) * t ^ (-β - 1)) := by rw [hexp]
  obtain ⟨C, hCψ⟩ := limit_of_deriv_bound ha₀2 hβ1 hD0 hcont hder hbd
  -- assemble
  set A : ℝ := (1 / 2) ^ κ + (3 / 2) ^ κ with hA
  have hA0 : 0 ≤ A := by positivity
  have h1κ : 0 < 1 + κ := by linarith
  refine ⟨(1 + κ) * C, (1 + κ) * (2 * D / β) * A + 2 * B * E, Real.exp a₀, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set t := Real.log x with ht
  have hta : a₀ ≤ t := by rw [ht, Real.le_log_iff_exp_le hx0]; exact hx
  have ht2 : 2 ≤ t := ha₀2.trans hta
  have ht0 : 0 < t := by linarith
  have hpos : 0 < t - c₀ := by have := hshift t hta; linarith
  have hxe : Real.exp t = x := Real.exp_log hx0
  have hx1 : 1 ≤ x := by rw [← hxe]; exact Real.one_le_exp ht0.le
  have hid := key_identity f g hconv κ c₀ hx1
  rw [← ht] at hid
  have hI : Isum f x = ψ t * (t - c₀) ^ (1 + κ) := by
    have h1 : (t - c₀) ^ p * (t - c₀) ^ (1 + κ) = 1 := by
      rw [← Real.rpow_add hpos, hp]; simp
    calc Isum f x = Isum f x * ((t - c₀) ^ p * (t - c₀) ^ (1 + κ)) := by rw [h1, mul_one]
      _ = ψ t * (t - c₀) ^ (1 + κ) := by simp only [hψ]; rw [hxe]; ring
  have hψC := hCψ t hta
  have hRt := hR t ht2
  rw [hxe] at hRt
  have hlog0 : 0 ≤ 1 + Real.log (1 + t) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + t by linarith); linarith
  have hkey : (t - c₀) * (Ssum f x - (1 + κ) * C * (t - c₀) ^ κ) =
      (1 + κ) * (ψ t - C) * (t - c₀) ^ (1 + κ) + Rsum f g κ c₀ x := by
    have e : (t - c₀) * (t - c₀) ^ κ = (t - c₀) ^ (1 + κ) := by
      rw [Real.rpow_add hpos, Real.rpow_one]
    rw [mul_sub, hid, hI, ← e]; ring
  have hshp : (t - c₀) ^ (1 + κ) = (t - c₀) * (t - c₀) ^ κ := by
    rw [Real.rpow_add hpos, Real.rpow_one]
  have hdiff : |Ssum f x - (1 + κ) * C * (t - c₀) ^ κ| ≤
      (1 + κ) * |ψ t - C| * (t - c₀) ^ κ + |Rsum f g κ c₀ x| / (t - c₀) := by
    have h := congrArg abs hkey
    rw [abs_mul, abs_of_pos hpos] at h
    have hb := abs_add_le ((1 + κ) * (ψ t - C) * (t - c₀) ^ (1 + κ)) (Rsum f g κ c₀ x)
    rw [abs_mul, abs_mul, abs_of_pos h1κ, abs_of_pos (Real.rpow_pos_of_pos hpos _), hshp] at hb
    rw [hshp] at h
    rw [← h] at hb
    have key : (t - c₀) * |Ssum f x - (1 + κ) * C * (t - c₀) ^ κ| ≤
        (t - c₀) * ((1 + κ) * |ψ t - C| * (t - c₀) ^ κ + |Rsum f g κ c₀ x| / (t - c₀)) := by
      rw [mul_add, mul_div_cancel₀ _ hpos.ne']
      linarith
    exact le_of_mul_le_mul_left key hpos
  -- bound the two pieces by `t^{σ−2}`
  have hsk : t ^ (σ - 2) ≤ t ^ (κ - 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hp1 : (1 + κ) * |ψ t - C| * (t - c₀) ^ κ ≤
      (1 + κ) * (2 * D / β) * A * ((1 + Real.log (1 + t)) * t ^ (σ - 2)) := by
    have hsh := rpow_shift_le (κ := κ) hta
    have hG : Gfun β t * t ^ κ = (1 + Real.log (1 + t)) * t ^ (σ - 2) := by
      unfold Gfun
      rw [mul_assoc, ← Real.rpow_add ht0, hβ]; ring_nf
    have hc0 : 0 ≤ 2 * D / β := by positivity
    calc (1 + κ) * |ψ t - C| * (t - c₀) ^ κ ≤ (1 + κ) * (2 * D / β * Gfun β t) * (A * t ^ κ) := by
          apply mul_le_mul (by gcongr) hsh (Real.rpow_nonneg hpos.le _)
            (mul_nonneg h1κ.le (mul_nonneg hc0 (Gfun_nonneg β ht0)))
      _ = (1 + κ) * (2 * D / β) * A * (Gfun β t * t ^ κ) := by ring
      _ = _ := by rw [hG]
  have hp2 : |Rsum f g κ c₀ x| / (t - c₀) ≤ 2 * B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 2)) := by
    rw [div_le_iff₀ hpos]
    have e : t ^ (σ - 1) = t * t ^ (σ - 2) := by
      rw [show σ - 1 = (σ - 2) + 1 by ring, Real.rpow_add_one ht0.ne']; ring
    have hsh := hshift t hta
    have : 0 ≤ (1 + Real.log (1 + t)) * t ^ (σ - 2) := by positivity
    rw [e] at hRt
    have hBE : 0 ≤ B * E := by positivity
    have hm : B * E * ((1 + Real.log (1 + t)) * (t * t ^ (σ - 2))) ≤
        2 * B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 2)) * (t - c₀) := by
      calc B * E * ((1 + Real.log (1 + t)) * (t * t ^ (σ - 2)))
          = (B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 2))) * t := by ring
        _ ≤ (B * E * ((1 + Real.log (1 + t)) * t ^ (σ - 2))) * (2 * (t - c₀)) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hBE this)
        _ = _ := by ring
    linarith
  have hfin : |Ssum f x - (1 + κ) * C * (t - c₀) ^ κ| ≤
      ((1 + κ) * (2 * D / β) * A + 2 * B * E) * ((1 + Real.log (1 + t)) * t ^ (σ - 2)) := by
    have := hdiff.trans (add_le_add hp1 hp2); linarith
  have hfin2 : ((1 + κ) * (2 * D / β) * A + 2 * B * E) * ((1 + Real.log (1 + t)) * t ^ (σ - 2)) ≤
      ((1 + κ) * (2 * D / β) * A + 2 * B * E) * (1 + Real.log (1 + t)) * t ^ (κ - 1) := by
    have hK0 : 0 ≤ (1 + κ) * (2 * D / β) * A + 2 * B * E := by positivity
    calc ((1 + κ) * (2 * D / β) * A + 2 * B * E) * ((1 + Real.log (1 + t)) * t ^ (σ - 2))
        = (((1 + κ) * (2 * D / β) * A + 2 * B * E) * (1 + Real.log (1 + t))) * t ^ (σ - 2) := by ring
      _ ≤ (((1 + κ) * (2 * D / β) * A + 2 * B * E) * (1 + Real.log (1 + t))) * t ^ (κ - 1) :=
          mul_le_mul_of_nonneg_left hsk (mul_nonneg hK0 hlog0)
  have e : (1 + κ) * C * (t - c₀) ^ κ = (1 + κ) * C * (Real.log x - c₀) ^ κ := by rw [ht]
  rw [← e]
  exact hfin.trans hfin2

end RamanujanTau.SelbergDelange2
