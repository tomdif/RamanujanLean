/-
# `SvStripC` (S2): the exact twisted identities (unconditional)

* **`SvC_eq_SvBil`** (all `z`): `𝒮(z) = Σ_{P,Q≤y²} x_z(P) x_z(Q) K^{[1−iz]}(P,Q)`, from
  `κ e_z = β(a)β(c)c^{−iz} · β(b)β(d)b^{−iz} · [P,Q]^{−s}` (`term_eq`: `e_z = (ad/g)^{iz}`,
  `[P,Q] = P₁ b d`).
* **`SvBil_diag`** (`Im z > −1`): `SvBil = Σ_{d≤y²} W^{[s]}(d) y_d(z)²` (`SvStripA.qDecompC`).
* **`qFactorC`**: `α(n₁)α(n₂) G^z_d(n₁,n₂) = Σ_{u₁|n₁,u₂|n₂} Γ^z_d(u₁,u₂) F_z(n₁/u₁) F(n₂/u₂)`
  (`FizA_mul_FzA`: `Fi_z ∗ F_z = 1`, twisting by the completely multiplicative `m^{iz}`).
* **`Yd_eq_YdJ`** (`y ≥ 2`): `y_d(z) = (log y)^{−2} Σ_{u₁,u₂≤y} Γ^z_d(u₁,u₂) J_z(y/u₁) J_0(y/u₂)`.
  The `c^{−iz}` of `x_z` cancels against `U^{[s]}`'s `p^{−s}` in the sense that it is absorbed into
  `G^z`, and only `J_0` occurs on the `n₂ = c` side.
* **`SvC_eq_diag`**: `𝒮(z) = Σ_{d≤y²} W^{[1−iz]}(d) · YdJ y z d²` (`Im z > −1`, `y ≥ 2`).
-/
import RamanujanTau.SvStripC.Defs

set_option autoImplicit false

namespace RamanujanTau.SvStripC

open Complex Finset ArithmeticFunction
open RamanujanTau.SvStripA (UdC LcC WdC KqC SvC evz rhoCF Ω re_s_pos qDecompC)
open RamanujanTau.SvStripB (Jz)
open RamanujanTau.QFProof (Fm Icc_one_eq βSel_in divisors_sub)
open RamanujanTau.QFProof3 (Fi Fi_mul_F)
open RamanujanTau.SelbergCoeffs (alpha)
open RamanujanTau.HafnerMV2 (βSel)
open RamanujanTau.SelbergKey (sum4 kap P1 Q1)
open RamanujanTau.SelbergDelange2 (divN)
open RamanujanTau.SelbergDelange3 (fR)

/-! ### The twist -/

lemma clog_nat (m : ℕ) : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
  rw [← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg m)]

lemma tw_mul (z : ℂ) (a b : ℕ) : tw z (a * b) = tw z a * tw z b := by
  unfold tw; rw [Nat.cast_mul, natCast_mul_natCast_cpow]

lemma tw_one (z : ℂ) : tw z 1 = 1 := by simp [tw]

lemma tw_zero_left (m : ℕ) : tw 0 m = 1 := by simp [tw]

lemma tw_eq_exp (z : ℂ) {m : ℕ} (hm : 0 < m) : tw z m = cexp (I * z * (Real.log m : ℂ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold tw; rw [cpow_def_of_ne_zero hm0, clog_nat]; ring_nf

lemma Fiz_zero (m : ℕ) : Fiz 0 m = (Fi m : ℂ) := by simp [Fiz, tw_zero_left]

lemma Fz_zero (m : ℕ) : Fz 0 m = (Fm m : ℂ) := by simp [Fz, tw_zero_left]

/-! ### `Fi_z ∗ F_z = 1` and the inversion formulas -/

/-- `F_z` as an arithmetic function. -/
noncomputable def FzA (z : ℂ) : ArithmeticFunction ℂ := ⟨fun m => Fz z m, by simp [Fz, Fm]⟩

/-- `Fi_z` as an arithmetic function. -/
noncomputable def FizA (z : ℂ) : ArithmeticFunction ℂ := ⟨fun m => Fiz z m, by simp [Fiz]⟩

lemma FizA_mul_FzA (z : ℂ) : FizA z * FzA z = 1 := by
  ext n
  have hR := congrArg (fun f : ArithmeticFunction ℝ => f n) Fi_mul_F
  simp only at hR
  rw [mul_apply] at hR
  rw [mul_apply]
  calc ∑ x ∈ n.divisorsAntidiagonal, FizA z x.1 * FzA z x.2
      = ∑ x ∈ n.divisorsAntidiagonal, ((Fi x.1 * divN fR x.2 : ℝ) : ℂ) * tw z n := by
        refine sum_congr rfl fun x hx => ?_
        have := (Nat.mem_divisorsAntidiagonal.1 hx).1
        simp only [FizA, FzA, Fiz, Fz, coe_mk]
        rw [← this, tw_mul, show Fm x.2 = divN fR x.2 from rfl]
        push_cast; ring
    _ = ((∑ x ∈ n.divisorsAntidiagonal, Fi x.1 * divN fR x.2 : ℝ) : ℂ) * tw z n := by
        rw [ofReal_sum, sum_mul]
    _ = _ := by
        rw [hR]
        rcases eq_or_ne n 1 with rfl | h
        · simp [tw_one]
        · simp [ArithmeticFunction.one_apply_ne h]

/-- One-variable inversion with the twisted pair `(Fi_z, F_z)`. -/
lemma one_invC (z : ℂ) (g : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    ∑ u ∈ n.divisors, (∑ v ∈ u.divisors, g v * Fiz z (u / v)) * Fz z (n / u) = g n := by
  set G : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else g n, by simp⟩ with hG
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) (show (G * FizA z) * FzA z = G by
    rw [mul_assoc, FizA_mul_FzA, mul_one])
  simp only at h
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => (G * FizA z) a * FzA z b)] at h
  have hGn : G n = g n := by simp [hG, hn.ne']
  rw [← hGn, ← h]
  refine sum_congr rfl fun u hu => ?_
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => G a * FizA z b)]
  simp only [FzA, FizA, coe_mk]
  congr 1
  refine sum_congr rfl fun v hv => ?_
  have : v ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv)
  simp [hG, this]

/-- Two-variable inversion (twist `z₁` on the first variable, `z₂` on the second). -/
lemma two_invC (z₁ z₂ : ℂ) (G : ℕ → ℕ → ℂ) {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors,
      (∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fiz z₁ (u₁ / v₁) * Fiz z₂ (u₂ / v₂)) *
        Fz z₁ (n₁ / u₁) * Fz z₂ (n₂ / u₂) = G n₁ n₂ := by
  have step : ∀ u₁, ∑ u₂ ∈ n₂.divisors,
      (∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fiz z₁ (u₁ / v₁) * Fiz z₂ (u₂ / v₂)) *
        Fz z₁ (n₁ / u₁) * Fz z₂ (n₂ / u₂) =
      (∑ v₁ ∈ u₁.divisors, (∑ u₂ ∈ n₂.divisors,
        (∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fiz z₂ (u₂ / v₂)) * Fz z₂ (n₂ / u₂)) * Fiz z₁ (u₁ / v₁)) *
          Fz z₁ (n₁ / u₁) := by
    intro u₁
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun v₁ _ => ?_
    refine sum_congr rfl fun u₂ _ => ?_
    refine sum_congr rfl fun v₂ _ => ?_
    ring
  rw [sum_congr rfl fun u₁ _ => step u₁]
  simp only [one_invC z₂ (G _) h₂]
  rw [← one_invC z₁ (fun v => G v n₂) h₁]

/-- **The twisted factorization** `α(n₁)α(n₂)G^z_d(n₁,n₂) = Σ Γ^z_d(u₁,u₂) F_z(n₁/u₁) F(n₂/u₂)`. -/
theorem qFactorC (z : ℂ) (d : ℕ) {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ((alpha n₁ * alpha n₂ : ℝ) : ℂ) * Gz z d n₁ n₂ =
      ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γz z d u₁ u₂ * Fz z (n₁ / u₁) * Fz 0 (n₂ / u₂) := by
  refine (two_invC z 0 (fun v₁ v₂ => ((alpha v₁ * alpha v₂ : ℝ) : ℂ) * Gz z d v₁ v₂) h₁ h₂).symm.trans ?_
  simp only [Γz, Fiz_zero]

/-! ### Smoothing -/

lemma sum_antidiag_reindexC (φ : ℕ → ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, φ x.1 x.2 =
      ∑ u ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / u), φ u m := by
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, φ x.1 x.2
  · refine sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  trans ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, φ x.1 x.2
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => (by simp_all)
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun n hn => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by lia)]
  · intro hm
    grw [hm]
    simp [Nat.mul_div_le, Nat.div_le_self]

lemma Jz_eqC (w : ℂ) (y u : ℕ) :
    Jz w ((y : ℝ) / u) = ∑ m ∈ Ioc 0 (y / u), Fz w m * (Real.log ((y : ℝ) / (u * m)) : ℂ) := by
  unfold Jz
  rw [Nat.floor_div_eq_div]
  refine sum_congr rfl fun m hm => ?_
  rw [Fz, tw_eq_exp w (mem_Ioc.1 hm).1, div_div, Fm]

lemma smooth_oneC (w : ℂ) (y : ℕ) (b : ℕ → ℂ) :
    ∑ n ∈ Ioc 0 y, (Real.log ((y : ℝ) / n) : ℂ) * ∑ u ∈ n.divisors, b u * Fz w (n / u) =
      ∑ u ∈ Ioc 0 y, b u * Jz w ((y : ℝ) / u) := by
  have h1 : ∀ n ∈ Ioc 0 y, (Real.log ((y : ℝ) / n) : ℂ) * ∑ u ∈ n.divisors, b u * Fz w (n / u) =
      ∑ x ∈ n.divisorsAntidiagonal, b x.1 * (Fz w x.2 * (Real.log ((y : ℝ) / (x.1 * x.2)) : ℂ)) := by
    intro n _
    rw [← Nat.sum_divisorsAntidiagonal (fun i j => b i * Fz w j), mul_sum]
    refine sum_congr rfl fun x hx => ?_
    have := (Nat.mem_divisorsAntidiagonal.1 hx).1
    rw [← this]; push_cast; ring
  rw [sum_congr rfl h1, sum_antidiag_reindexC
    (fun u m => b u * (Fz w m * (Real.log ((y : ℝ) / (u * m)) : ℂ))) y]
  refine sum_congr rfl fun u _ => ?_
  rw [Jz_eqC, mul_sum]

lemma smooth_twoC (z : ℂ) (y : ℕ) (Γ : ℕ → ℕ → ℂ) :
    ∑ n₁ ∈ Ioc 0 y, ∑ n₂ ∈ Ioc 0 y,
      (Real.log ((y : ℝ) / n₁) : ℂ) * (Real.log ((y : ℝ) / n₂) : ℂ) *
        ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fz z (n₁ / u₁) * Fz 0 (n₂ / u₂) =
      ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Jz z ((y : ℝ) / u₁) * Jz 0 ((y : ℝ) / u₂) := by
  set B : ℕ → ℂ := fun u₁ => ∑ u₂ ∈ Ioc 0 y, Γ u₁ u₂ * Jz 0 ((y : ℝ) / u₂) with hB
  have hin : ∀ u₁, ∑ n₂ ∈ Ioc 0 y, (Real.log ((y : ℝ) / n₂) : ℂ) *
      ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fz 0 (n₂ / u₂) = B u₁ := fun u₁ => smooth_oneC 0 y (Γ u₁)
  have step : ∀ n₁ ∈ Ioc 0 y, ∑ n₂ ∈ Ioc 0 y,
      (Real.log ((y : ℝ) / n₁) : ℂ) * (Real.log ((y : ℝ) / n₂) : ℂ) *
        ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γ u₁ u₂ * Fz z (n₁ / u₁) * Fz 0 (n₂ / u₂) =
      (Real.log ((y : ℝ) / n₁) : ℂ) * ∑ u₁ ∈ n₁.divisors, B u₁ * Fz z (n₁ / u₁) := by
    intro n₁ _
    simp_rw [← hin]
    calc _ = ∑ n₂ ∈ Ioc 0 y, ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors,
          (Real.log ((y : ℝ) / n₁) : ℂ) * ((Real.log ((y : ℝ) / n₂) : ℂ) *
            (Γ u₁ u₂ * Fz 0 (n₂ / u₂)) * Fz z (n₁ / u₁)) := by
          refine sum_congr rfl fun n₂ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun u₁ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun u₂ _ => ?_
          ring
      _ = ∑ u₁ ∈ n₁.divisors, ∑ n₂ ∈ Ioc 0 y, ∑ u₂ ∈ n₂.divisors,
          (Real.log ((y : ℝ) / n₁) : ℂ) * ((Real.log ((y : ℝ) / n₂) : ℂ) *
            (Γ u₁ u₂ * Fz 0 (n₂ / u₂)) * Fz z (n₁ / u₁)) := sum_comm
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun u₁ _ => ?_
          rw [sum_mul, mul_sum]
          refine sum_congr rfl fun n₂ _ => ?_
          rw [mul_sum, sum_mul, mul_sum]
  rw [sum_congr rfl step, smooth_oneC z y B]
  refine sum_congr rfl fun u₁ _ => ?_
  rw [hB, sum_mul]
  refine sum_congr rfl fun u₂ _ => ?_
  ring

/-- **`y_d(z) = (log y)^{−2} Σ_{u₁,u₂≤y} Γ^z_d(u₁,u₂) J_z(y/u₁) J_0(y/u₂)`** (exact, `y ≥ 2`). -/
theorem Yd_eq_YdJ (z : ℂ) {y : ℕ} (hy : 1 < y) (d : ℕ) : Yd y z d = YdJ y z d := by
  have hl : (Real.log y : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.log_pos (by exact_mod_cast hy)).ne'
  unfold YdJ Yd
  rw [← smooth_twoC z y (Γz z d), sum_div, Icc_one_eq]
  refine sum_congr rfl fun n₁ hn₁ => ?_
  rw [sum_div]
  refine sum_congr rfl fun n₂ hn₂ => ?_
  rw [βSel_in hy hn₁, βSel_in hy hn₂, ← qFactorC z d (mem_Ioc.1 hn₁).1 (mem_Ioc.1 hn₂).1]
  push_cast
  field_simp

/-! ### The bilinear form -/

lemma xz_sum (y : ℕ) (z : ℂ) (f : ℕ → ℂ) :
    ∑ P ∈ Icc 1 (y ^ 2), xz y z P * f P =
      ∑ a ∈ Icc 1 y, ∑ c ∈ Icc 1 y, ((βSel y a * βSel y c : ℝ) : ℂ) * tw (-z) c * f (a * c) := by
  unfold xz
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c hc => ?_
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq]
  have h1 := mem_Icc.1 ha
  have h2 := mem_Icc.1 hc
  rw [if_pos (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
    by rw [sq]; exact Nat.mul_le_mul h1.2 h2.2⟩)]

/-- The single-term identity `κ e_z ρ(P₁)ρ(Q₁) = β(a)β(c)c^{−iz} · β(d)β(b)b^{−iz} · K^{[s]}(ac, bd)`. -/
lemma term_eq (y : ℕ) (z : ℂ) {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (kap y a b c d : ℂ) * evz a b c d z * rhoCF (P1 a b c d) (1 - z * I) *
        rhoCF (Q1 a b c d) (1 - z * I) =
      ((βSel y a * βSel y c : ℝ) : ℂ) * tw (-z) c *
        (((βSel y d * βSel y b : ℝ) : ℂ) * tw (-z) b * KqC (1 - z * I) (a * c) (b * d)) := by
  set g := Nat.gcd (a * c) (b * d) with hg
  set L := Nat.lcm (a * c) (b * d) with hLdef
  have hac : 0 < a * c := Nat.mul_pos ha hc
  have hbd : 0 < b * d := Nat.mul_pos hb hd
  have hgd : g ∣ a * c := Nat.gcd_dvd_left _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hac
  have hP : 0 < P1 a b c d := Nat.div_pos (Nat.le_of_dvd hac hgd) hg0
  have hLn : L = P1 a b c d * b * d := by
    rw [mul_assoc, P1, ← hg, Nat.div_mul_right_comm hgd]; rfl
  have hL0 : 0 < L := by rw [hLn]; positivity
  have hlogL : Real.log L = Real.log (P1 a b c d) + Real.log b + Real.log d := by
    rw [hLn]; push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hcp : ((L : ℕ) : ℂ) ^ (-(1 - z * I)) = ((L : ℝ)⁻¹ : ℂ) * cexp (z * I * (Real.log L : ℂ)) := by
    have hL0' : ((L : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    rw [cpow_def_of_ne_zero hL0', clog_nat,
      show (Real.log L : ℂ) * -(1 - z * I) = -(Real.log L : ℂ) + z * I * (Real.log L : ℂ) by ring,
      Complex.exp_add, ← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log (by exact_mod_cast hL0)]
    push_cast; ring
  have hE : cexp (z * I * ((Real.log (P1 a b c d) + Real.log d - Real.log c : ℝ) : ℂ)) =
      cexp (I * -z * (Real.log c : ℂ)) * cexp (I * -z * (Real.log b : ℂ)) *
        cexp (z * I * (Real.log L : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hlogL]
    congr 1
    push_cast; ring
  unfold KqC kap evz
  rw [tw_eq_exp _ hc, tw_eq_exp _ hb, hcp, hE]
  have hPQ : P1 a b c d = a * c / g := rfl
  have hQ : Q1 a b c d = b * d / g := rfl
  rw [← hPQ, ← hQ, ← hLdef]
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  push_cast
  field_simp

/-- **The bilinear form**: `𝒮(z) = Σ_{P,Q≤y²} x_z(P) x_z(Q) K^{[1−iz]}(P,Q)` (all `z`). -/
theorem SvC_eq_SvBil (y : ℕ) (z : ℂ) : SvC y z = SvBil y z := by
  unfold SvBil
  simp_rw [mul_assoc (xz y z _), ← mul_sum]
  rw [xz_sum y z (fun P => ∑ Q ∈ Icc 1 (y ^ 2), xz y z Q * KqC (1 - z * I) P Q)]
  simp_rw [xz_sum y z (fun Q => KqC (1 - z * I) _ Q), mul_sum]
  unfold SvC sum4
  refine sum_congr rfl fun a ha => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c hc => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  refine sum_congr rfl fun b hb => ?_
  simp only
  rw [term_eq y z (mem_Icc.1 ha).1 (mem_Icc.1 hb).1 (mem_Icc.1 hc).1 (mem_Icc.1 hd).1,
    mul_comm d b]

/-! ### Diagonalization -/

lemma bilinC (S D : Finset ℕ) (x c : ℕ → ℂ) (f g : ℕ → ℕ → ℂ) :
    ∑ h ∈ S, ∑ k ∈ S, x h * x k * ∑ d ∈ D, c d * f h d * g k d =
      ∑ d ∈ D, c d * (∑ h ∈ S, x h * f h d) * (∑ k ∈ S, x k * g k d) := by
  have e : ∀ h k, x h * x k * ∑ d ∈ D, c d * f h d * g k d =
      ∑ d ∈ D, c d * (x h * f h d) * (x k * g k d) := by
    intro h k; rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
  simp_rw [e]
  rw [sum_congr rfl fun h _ => (sum_comm : ∑ k ∈ S, ∑ d ∈ D, c d * (x h * f h d) * (x k * g k d) =
    ∑ d ∈ D, ∑ k ∈ S, c d * (x h * f h d) * (x k * g k d))]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_assoc, sum_mul_sum, mul_sum]
  exact sum_congr rfl fun h _ => by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring

lemma xz_U (y : ℕ) (z : ℂ) (d : ℕ) :
    ∑ P ∈ Icc 1 (y ^ 2), xz y z P * UdC (1 - z * I) P d = Yd y z d := by
  rw [xz_sum y z (fun P => UdC (1 - z * I) P d)]
  unfold Yd Gz
  refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => by ring

/-- **`SvBil = Σ_{d≤y²} W^{[s]}(d) y_d(z)²`** for `Im z > −1`. -/
theorem SvBil_diag (y : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    SvBil y z = ∑ d ∈ Icc 1 (y ^ 2), WdC (1 - z * I) d * Yd y z d ^ 2 := by
  have hD := qDecompC (re_s_pos hz)
  have hK : ∀ h ∈ Icc 1 (y ^ 2), ∀ k ∈ Icc 1 (y ^ 2), xz y z h * xz y z k * KqC (1 - z * I) h k =
      xz y z h * xz y z k * ∑ d ∈ Icc 1 (y ^ 2),
        WdC (1 - z * I) d * UdC (1 - z * I) h d * UdC (1 - z * I) k d := by
    intro h hh k hk
    rw [hD.2 h k (by have := (mem_Icc.1 hh).1; omega) (by have := (mem_Icc.1 hk).1; omega)]
    congr 1
    refine sum_subset (divisors_sub hh) fun d _ hd => ?_
    have hh0 : h ≠ 0 := by have := (mem_Icc.1 hh).1; omega
    have : ¬ d ∣ h := fun hdv => hd (Nat.mem_divisors.2 ⟨hdv, hh0⟩)
    rw [hD.1 h d this]; ring
  unfold SvBil
  rw [sum_congr rfl fun h hh => sum_congr rfl fun k hk => hK h hh k hk, bilinC]
  refine sum_congr rfl fun d _ => ?_
  rw [xz_U]; ring

/-- **`𝒮(z) = Σ_{d≤y²} W^{[1−iz]}(d) · y_d(z)²`, `y_d(z) = (log y)^{−2} Σ Γ^z_d J_z J_0`**
(`Im z > −1`, `y ≥ 2`). -/
theorem SvC_eq_diag {y : ℕ} (hy : 1 < y) {z : ℂ} (hz : z ∈ Ω) :
    SvC y z = ∑ d ∈ Icc 1 (y ^ 2), WdC (1 - z * I) d * YdJ y z d ^ 2 := by
  rw [SvC_eq_SvBil, SvBil_diag y hz]
  exact sum_congr rfl fun d _ => by rw [Yd_eq_YdJ z hy]

end RamanujanTau.SvStripC
