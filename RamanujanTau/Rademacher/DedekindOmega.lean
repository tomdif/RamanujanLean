/-
# The multiplier is `ω_{h,k} = e^{πi s(h,k)}`

The canonical multiplier `omega h k` (from `Integrand`) is identified with Dedekind's `e^{πi s(h,k)}`:

1. `ω` is unique, depends only on `h mod k`, and `ω_{0,1} = 1` (the `S`-transformation `F_modular`).
2. **reciprocity of `ω`**: for coprime `h, k ≥ 1` and `H ≡ −k (mod h)`,
   `ω_{h,k} = ω_{H,h} · e^{−πi/4} · e^{πi(h/k + k/h + 1/(hk))/12}`.
   This compares the transformation at `h/k` (at `z = 1`), the `S`-transformation at `τ = (h+i)/k`, and the
   transformation at `H/h` (at `Z = k/(h+i)`): all three land on the same far point `(h'+i)/k`.
3. Dedekind's reciprocity law (`Dedekind`) says `e^{πi s}` obeys the same recursion, so induction along the
   Euclidean algorithm gives `ω_{h,k} = e^{πi s(h,k)}`.
-/
import RamanujanTau.Rademacher.Integrand
import RamanujanTau.Rademacher.Dedekind

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Metric
open scoped Real

noncomputable section

lemma F_ne_zero {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : F q ≠ 0 := inv_ne_zero (Pq_ne_zero hq)

lemma far_mem (h' : ℤ) (k : ℕ) (hk : 0 < k) {z : ℂ} (hz : 0 < z.re) :
    cexp (2 * π * I * ((h' + I / z) / k)) ∈ ball (0 : ℂ) 1 := by
  apply cexp_mem_ball
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have : ((h' + I / z) / k).im = z.re / Complex.normSq z / k := by
    rw [show ((h' : ℂ) + I / z) / k = ((h' + I / z) / (k : ℝ) : ℂ) by push_cast; rfl, div_ofReal_im]
    simp [div_im]
  rw [this]
  exact div_pos (div_pos hz (Complex.normSq_pos.mpr hz0)) hkr

lemma exists_inv {h k : ℕ} (hcop : Nat.Coprime h k) : ∃ a b : ℤ, (k : ℤ) * b - h * a = 1 := by
  obtain ⟨x, y, hxy⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (h : ℤ) k)
  exact ⟨-x, y, by linarith⟩

/-- **uniqueness of the multiplier**. -/
lemma isMult_unique {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) {ω₁ ω₂ : ℂ}
    (h₁ : IsMult h k ω₁) (h₂ : IsMult h k ω₂) : ω₁ = ω₂ := by
  obtain ⟨a, b, hab⟩ := exists_inv hcop
  have hd : (k : ℤ) ∣ h * a + 1 := ⟨b, by linarith⟩
  have e1 := h₁.2 a hd 1 (by simp)
  have e2 := h₂.2 a hd 1 (by simp)
  have hF := F_ne_zero (far_mem a k hk (z := 1) (by simp))
  rw [e1] at e2
  simp only [sqrt_one, mul_one, sub_self, mul_zero, zero_div, Complex.exp_zero, div_one] at e2 hF
  exact mul_right_cancel₀ hF e2

lemma coprime_mod {h k : ℕ} (hcop : Nat.Coprime h k) : Nat.Coprime (h % k) k := by
  unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcop

lemma re_div_hI {h k : ℝ} (hh : 0 < h) (hk : 0 < k) : 0 < ((k : ℂ) / (h + I)).re := by
  rw [div_re]
  have : Complex.normSq ((h : ℂ) + I) = h ^ 2 + 1 := by rw [normSq_apply]; simp; ring
  rw [this]; simp; positivity

lemma omega_eq_of_isMult {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) {ω : ℂ} (hω : IsMult h k ω) :
    omega h k = ω :=
  isMult_unique hk hcop (omega_spec hk hcop) hω

/-- `ω_{h,k}` depends only on `h mod k`. -/
lemma omega_mod {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) : omega h k = omega (h % k) k := by
  have hcop' : Nat.Coprime (h % k) k := coprime_mod hcop
  refine (omega_eq_of_isMult hk hcop' ⟨(omega_spec hk hcop).1, fun h' hh' z hz => ?_⟩).symm
  have hmod : (k : ℤ) ∣ (h : ℤ) - ((h % k : ℕ) : ℤ) := by
    rw [Int.natCast_mod]; exact Int.dvd_self_sub_emod
  have hh'' : (k : ℤ) ∣ h * h' + 1 := by
    have : (h : ℤ) * h' + 1 = ((h % k : ℕ) : ℤ) * h' + 1 + (h - (h % k : ℕ)) * h' := by ring
    rw [this]; exact dvd_add hh' (dvd_mul_of_dvd_left hmod _)
  have := (omega_spec hk hcop).2 h' hh'' z hz
  have hp := F_periodic hk ((h % k : ℕ) : ℤ) h (by rw [← neg_sub]; exact dvd_neg.mpr hmod) (I * z)
  simp only [Int.cast_natCast] at hp
  rw [hp, this]

/-- `ω_{0,1} = 1`: the `S`-transformation. -/
lemma omega_zero_one : omega 0 1 = 1 := by
  refine omega_eq_of_isMult one_pos (Nat.coprime_zero_left 1 |>.mpr rfl) ⟨by simp, fun h' _ z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw : 0 < (2 * π * z).re := by
    rw [show (2 * π * z : ℂ) = ((2 * π : ℝ) : ℂ) * z by push_cast; ring, re_ofReal_mul]
    exact mul_pos (by positivity) hz
  have hm := F_modular hw
  have e1 : cexp (2 * π * I * ((((0 : ℕ) : ℂ) + I * z) / ((1 : ℕ) : ℂ))) = cexp (-(2 * π * z)) := by
    congr 1; push_cast; ring_nf; rw [I_sq]; ring
  have e2 : cexp (2 * π * I * ((h' + I / z) / ((1 : ℕ) : ℂ))) = cexp (-(4 * π ^ 2 / (2 * π * z))) := by
    rw [show 2 * π * I * ((h' + I / z) / ((1 : ℕ) : ℂ)) = -(4 * π ^ 2 / (2 * π * z)) + h' * (2 * π * I) by
      push_cast; field_simp; ring_nf; rw [I_sq]; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e3 : HardyRamanujan.sq (2 * π * z) = sqrt z := by
    rw [HardyRamanujan.sq, sqrt_eq_exp hz0]; congr 3; field_simp
  have e4 : cexp (π ^ 2 / (6 * (2 * π * z)) - 2 * π * z / 24) = cexp (π * (1 / z - z) / (12 * ((1 : ℕ) : ℂ))) := by
    congr 1; push_cast; field_simp; ring
  rw [e1, e2, hm, e3, e4, one_mul]

lemma re_pos_of_arg {u : ℂ} (hu : 0 < u.re) : -π < u.arg + 0 ∧ u.arg ≤ π := by
  have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)); rw [abs_lt] at this
  constructor <;> linarith [Real.pi_pos]

/-- the branch product `√((1−ih)/k) · √(k/(h+i)) = e^{−πi/4}`. -/
lemma sqrt_prod {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    cexp (log ((1 - I * h) / k) / 2) * cexp (log (k / (h + I)) / 2) = cexp (-(π * I / 4)) := by
  have hhI : (h : ℂ) + I ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hu0 : (1 - I * h) / k ≠ 0 := by
    refine div_ne_zero (fun h0 => ?_) hk0; have := congrArg Complex.re h0; simp at this
  have hZ0 : (k : ℂ) / (h + I) ≠ 0 := div_ne_zero hk0 hhI
  have hure : 0 < ((1 - I * h) / k).re := by
    rw [show ((1 - I * h) / k : ℂ) = ((1 - I * h) / (k : ℝ) : ℂ) from rfl, div_ofReal_re]; simp [hk]
  have hZre : 0 < ((k : ℂ) / (h + I)).re := re_div_hI hh hk
  have hprod : (1 - I * h) / k * (k / (h + I)) = -I := by
    field_simp; ring_nf; rw [I_sq]; ring
  have hlog : log ((1 - I * h) / k) + log (k / (h + I)) = log (-I) := by
    rw [← hprod]
    refine ((log_mul_eq_add_log_iff hu0 hZ0).mpr ?_).symm
    have a1 := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hure)); rw [abs_lt] at a1
    have a2 := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hZre)); rw [abs_lt] at a2
    rw [Set.mem_Ioc]; constructor <;> linarith [Real.pi_pos]
  rw [← Complex.exp_add, ← add_div, hlog, log_neg_I]
  congr 1; ring

/-- the exponent identity at `z = 1`. -/
lemma exponent_id {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    (π : ℂ) ^ 2 / (6 * (2 * π * (1 - I * h) / k)) - 2 * π * (1 - I * h) / k / 24 +
      π * (1 / (k / (h + I)) - k / (h + I)) / (12 * h) =
    π * I * ((h / k + k / h + 1 / (h * k)) / 12) := by
  have hhI : (h : ℂ) + I ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (1 : ℂ) - I * h = -I * (h + I) := by ring_nf; rw [I_sq]; ring
  rw [h1]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, I_pow_four]
  ring

/-- **reciprocity of the multiplier**. -/
theorem omega_recip {h k H : ℕ} (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) (hH : h ∣ H + k) :
    omega h k = omega H h * cexp (-(π * I / 4)) *
      cexp (π * I * (((h : ℂ) / k + k / h + 1 / (h * k)) / 12)) := by
  obtain ⟨a, b, hab⟩ := exists_inv hcop
  have hcH : Nat.Coprime H h := coprime_of_dvd_add hcop.symm hH
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hhI : (h : ℂ) + I ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this
  -- (A) the transformation at `h/k`, `z = 1`
  have hA := (omega_spec hk hcop).2 a ⟨b, by linarith⟩ 1 (by simp)
  -- (B) the transformation at `H/h`, `Z = k/(h+i)`
  set Z : ℂ := (k : ℂ) / (h + I) with hZ
  have hZre : 0 < Z.re := re_div_hI hhr hkr
  have hdB : (h : ℤ) ∣ H * b + 1 := by
    obtain ⟨c, hc⟩ := hH
    exact ⟨c * b - a, by
      have : ((H + k : ℕ) : ℤ) = h * c := by exact_mod_cast hc
      push_cast at this; linear_combination b * this - hab⟩
  have hB := (omega_spec hh hcH).2 b hdB Z hZre
  -- (C) the `S`-transformation at `w = 2π(1 − ih)/k`
  set w : ℂ := 2 * π * (1 - I * h) / k with hw
  have hwre : 0 < w.re := by
    rw [hw, show (2 * π * (1 - I * h) / k : ℂ) = ((2 * π / k : ℝ) : ℂ) * (1 - I * h) by push_cast; ring,
      re_ofReal_mul]
    simp; positivity
  have hC := F_modular hwre
  -- identify the points
  have p1 : cexp (-w) = cexp (2 * π * I * ((h + I * 1) / k)) := by
    congr 1; rw [hw]; field_simp; ring_nf; rw [I_sq]; ring
  have p2 : F (cexp (-(4 * π ^ 2 / w))) = F (cexp (2 * π * I * ((H + I * Z) / h))) := by
    have hp := F_periodic hh (H : ℤ) (-(k : ℤ)) (by rw [sub_neg_eq_add]; exact_mod_cast hH) (I * Z)
    push_cast at hp
    rw [hp]
    congr 2
    rw [hw, hZ]
    have h1 : (1 : ℂ) - I * h = -I * (h + I) := by ring_nf; rw [I_sq]; ring
    rw [h1]; field_simp; ring_nf; rw [I_sq]; ring
  have p3 : cexp (2 * π * I * ((b + I / Z) / h)) = cexp (2 * π * I * ((a + I / 1) / k)) := by
    congr 2
    have : (k : ℂ) * b - h * a = 1 := by exact_mod_cast hab
    rw [hZ]; field_simp; ring_nf; rw [I_sq]; linear_combination this
  rw [p1, p2, hB, p3] at hC
  rw [hA] at hC
  have hF := F_ne_zero (far_mem a k hk (z := 1) (by simp))
  -- cancel `F(far)` and simplify
  have hsq : HardyRamanujan.sq w * sqrt Z = cexp (-(π * I / 4)) := by
    have hZ0 : Z ≠ 0 := div_ne_zero hk0 hhI
    rw [HardyRamanujan.sq, sqrt_eq_exp hZ0, show w / (2 * π) = (1 - I * h) / k by rw [hw]; field_simp]
    exact sqrt_prod hhr hkr
  have hexp : cexp (π ^ 2 / (6 * w) - w / 24) * cexp (π * (1 / Z - Z) / (12 * h)) =
      cexp (π * I * (((h : ℂ) / k + k / h + 1 / (h * k)) / 12)) := by
    rw [← Complex.exp_add, hw, hZ]
    have := exponent_id hhr hkr
    push_cast at this
    rw [← this]
  have : omega h k * F (cexp (2 * π * I * ((a + I / 1) / k))) =
      (omega H h * (HardyRamanujan.sq w * sqrt Z) * (cexp (π ^ 2 / (6 * w) - w / 24) * cexp (π * (1 / Z - Z) / (12 * h)))) *
        F (cexp (2 * π * I * ((a + I / 1) / k))) := by
    simp only [sqrt_one, mul_one, div_one, sub_self, mul_zero, zero_div, Complex.exp_zero] at hC ⊢
    rw [hC]; ring
  rw [hsq, hexp] at this
  exact mul_right_cancel₀ hF this

/-- **`ω_{h,k} = e^{πi s(h,k)}`**. -/
theorem omega_eq_dsum : ∀ k : ℕ, 0 < k → ∀ h : ℕ, Nat.Coprime h k → omega h k = cexp (π * I * dsum h k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk h hcop
  rw [omega_mod hk hcop, dsum_mod hk]
  have hcop0 : Nat.Coprime (h % k) k := coprime_mod hcop
  set h₀ := h % k with hh₀
  rcases Nat.eq_zero_or_pos h₀ with h0 | hpos
  · rw [h0] at hcop0 ⊢
    have : k = 1 := (Nat.coprime_zero_left k).mp hcop0
    subst this
    rw [omega_zero_one, dsum_zero_one]; simp
  have hlt : h₀ < k := Nat.mod_lt _ hk
  set H := (h₀ - 1) * k % h₀ with hHdef
  have hH : h₀ ∣ H + k := by
    apply Nat.dvd_of_mod_eq_zero
    rw [hHdef, Nat.mod_add_mod, show (h₀ - 1) * k + k = h₀ * k by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos], Nat.mul_mod_right]
  have hcH : Nat.Coprime H h₀ := coprime_of_dvd_add hcop0.symm hH
  rw [omega_recip hpos hk hcop0 hH, ih h₀ hlt hpos H hcH, dsum_neg hpos hcop0.symm hH]
  have hrec := dsum_reciprocity hpos hk hcop0
  have hrecC : (dsum h₀ k : ℂ) = -(dsum k h₀ : ℂ) + (((h₀ : ℂ) / k + k / h₀ + 1 / (h₀ * k)) / 12 - 1 / 4) := by
    have : dsum h₀ k = -dsum k h₀ + (((h₀ : ℝ) / k + k / h₀ + 1 / (h₀ * k)) / 12 - 1 / 4) := by linarith
    rw [this]; push_cast; ring
  rw [← Complex.exp_add, ← Complex.exp_add, hrecC]
  congr 1
  push_cast
  ring

/-- **`A_k(n) = Σ_{h mod k, (h,k)=1} e^{πi s(h,k) − 2πinh/k}`** — Rademacher's Kloosterman sum. -/
theorem Ak_eq_dedekind (k n : ℕ) (hk : 0 < k) :
    Ak k n = ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
      cexp (π * I * dsum h k - 2 * π * I * n * h / k) := by
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [omega_eq_dsum k hk h (Finset.mem_filter.mp hh).2, ← Complex.exp_add, ← sub_eq_add_neg]

end

end Rademacher
