import RamanujanTau.ThetaLift.SeedTaylor

/-!
# Bounds on the kernel that are uniform in the generating parameter

The lattice terms and their Poisson duals are dominated, for `σ` in a ball, by one summable family
on `ℤ³`. This allows termwise extraction of Taylor coefficients on both sides of the kernel identity.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open scoped Real

noncomputable section

/-- A Gaussian dominating `hG K L` for every `|L| ≤ R`. -/
def hS (K R x : ℝ) : ℝ := hG K R x + hG K (-R) x

lemma hS_pos (K R x : ℝ) : 0 < hS K R x := add_pos (hG_pos _ _ _) (hG_pos _ _ _)

lemma hG_le_hS (K : ℝ) {L R : ℝ} (hL : |L| ≤ R) (x : ℝ) : hG K L x ≤ hS K R x := by
  unfold hS hG
  have hxL : L * x ≤ R * |x| := by
    calc L * x ≤ |L * x| := le_abs_self _
      _ = |L| * |x| := abs_mul _ _
      _ ≤ R * |x| := by gcongr
  rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩
  · have : Real.exp (-K * x ^ 2 + L * x) ≤ Real.exp (-K * x ^ 2 + R * x) := by
      apply Real.exp_le_exp.mpr
      rw [h] at hxL
      linarith
    have := Real.exp_pos (-K * x ^ 2 + -R * x)
    linarith
  · have : Real.exp (-K * x ^ 2 + L * x) ≤ Real.exp (-K * x ^ 2 + -R * x) := by
      apply Real.exp_le_exp.mpr
      rw [h] at hxL
      linarith
    have := Real.exp_pos (-K * x ^ 2 + R * x)
    linarith

/-- The dominating family on `ℤ³`. -/
theorem summable_triple_S {K₁ K₂ K₃ : ℝ} (h₁ : 0 < K₁) (h₂ : 0 < K₂) (h₃ : 0 < K₃)
    (R₁ R₂ R₃ p q r : ℝ) :
    Summable fun x : ℤ × ℤ × ℤ =>
      hS K₁ R₁ (x.2.2 + (q * x.1 + r * x.2.1)) * hS K₂ R₂ (x.2.1 + p * x.1) * hS K₃ R₃ x.1 := by
  have S := fun (a b c : ℝ) => summable_triple h₁ h₂ h₃ a b c p q r
  have h := (((S R₁ R₂ R₃).add (S R₁ R₂ (-R₃))).add ((S R₁ (-R₂) R₃).add (S R₁ (-R₂) (-R₃)))).add
    (((S (-R₁) R₂ R₃).add (S (-R₁) R₂ (-R₃))).add ((S (-R₁) (-R₂) R₃).add (S (-R₁) (-R₂) (-R₃))))
  refine h.congr fun x => ?_
  unfold hS
  ring

namespace KData
variable (D : KData)

/-- The same data at another value of the generating parameter. -/
def atσ (τ : ℂ) : KData := { D with σ := τ }

/-- The real part of `s`, the imaginary part of `s`, and their bound on a ball. -/
lemma s_atσ (τ : ℂ) : (D.atσ τ).s = I * τ / (D.N * D.z * D.y) := rfl

lemma sBound_norm {τ : ℂ} {R : ℝ} (hτ : ‖τ‖ ≤ R) :
    ‖(D.atσ τ).s‖ ≤ R * ‖((D.N : ℂ) * D.z * D.y)⁻¹‖ := by
  rw [s_atσ, div_eq_mul_inv, norm_mul, norm_mul, Complex.norm_I, one_mul]
  gcongr

/-- The dual exponent in norm. -/
theorem norm_dualF (a b m : ℤ) :
    ‖D.dualF a b m‖ = |((chiZ (D.N * b) : ℤ) : ℝ)| * Real.exp ((D.s.re ^ 2 - D.s.im ^ 2) / (4 * D.κ)) *
      (hG (π ^ 2 / D.κ) (π * D.s.im / D.κ) (m + D.Zc.re * a) *
      hG (π * D.vt * D.N / 12) (D.s.im * (D.N * D.y)) (b + 12 * D.ξ * a) *
      hG (6 * π * D.vt * D.N * D.y ^ 2) (-(D.s.re * (6 * D.N * D.y ^ 2))) a) := by
  have hκ := D.κ_pos
  have hκ' := D.κ_mul
  have hy := D.hy
  have hπ := Real.pi_pos
  set r := D.Zc.re with hr
  have hZ : D.Zc = (r : ℂ) - I * D.vt := by
    apply Complex.ext
    · simp [hr]
    · simp [D.Zc_im]
  set M : ℝ := m + r * a with hM
  have hW : (a : ℂ) * D.Zc + m = (M : ℂ) - I * (a * D.vt : ℝ) := by
    rw [hZ, hM]
    push_cast
    ring
  set t : ℝ := D.κ⁻¹ with ht
  have htκ : t * D.κ = 1 := inv_mul_cancel₀ hκ.ne'
  have htC : (D.κ : ℂ)⁻¹ = (t : ℂ) := by rw [ht]; push_cast; rfl
  set W : ℂ := (M : ℂ) - I * (a * D.vt : ℝ) with hWdef
  have hE : 2 * π * I * (D.N * b ^ 2 / 24) * D.Zc + D.dualE a b m =
      ((2 * π * (D.N * b ^ 2 / 24) : ℝ) : ℂ) * (I * D.Zc) + D.s * (I * (D.τ₂ a b : ℝ)) -
        ((D.κ * D.τ₂ a b ^ 2 : ℝ) : ℂ) + ((2 * π * D.τ₁ a b : ℝ) : ℂ) * (I * W) +
        (D.s * D.s) * ((t / 4 : ℝ) : ℂ) - ((π * t : ℝ) : ℂ) * (I * D.s * W) -
        ((π ^ 2 * t : ℝ) : ℂ) * (W * W) := by
    unfold dualE
    have hκC : (D.κ : ℂ) ≠ 0 := D.κ_ne
    rw [hW]
    push_cast
    rw [← htC]
    field_simp
    ring
  have hIZ : (I * D.Zc).re = D.vt := by
    simp [D.Zc_im]
  have hIW : (I * W).re = a * D.vt := by
    simp [hWdef]
  have hWW : (W * W).re = M ^ 2 - (a * D.vt) ^ 2 := by
    simp [hWdef, pow_two]
  have hIsW : (I * D.s * W).re = -D.s.im * M + D.s.re * (a * D.vt) := by
    simp [hWdef]
  have hre : (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc + D.dualE a b m).re =
      (D.s.re ^ 2 - D.s.im ^ 2) / (4 * D.κ) +
      (-(π ^ 2 / D.κ) * (m + D.Zc.re * a) ^ 2 + π * D.s.im / D.κ * (m + D.Zc.re * a)) +
      (-(π * D.vt * D.N / 12) * (b + 12 * D.ξ * a) ^ 2 +
        D.s.im * (D.N * D.y) * (b + 12 * D.ξ * a)) +
      (-(6 * π * D.vt * D.N * D.y ^ 2) * (a : ℝ) ^ 2 +
        -(D.s.re * (6 * D.N * D.y ^ 2)) * a) := by
    rw [hE]
    simp only [add_re, sub_re, Complex.re_ofReal_mul, hIZ, hIW, hWW, hIsW, ofReal_re]
    have hτ : (D.s * (I * (D.τ₂ a b : ℝ))).re = -D.s.im * D.τ₂ a b := by simp
    have hss : ((D.s * D.s) * ((t / 4 : ℝ) : ℂ)).re = (D.s.re ^ 2 - D.s.im ^ 2) * (t / 4) := by
      rw [Complex.re_mul_ofReal]
      simp [pow_two]
    rw [hτ, hss]
    simp only [← hr, ← hM]
    have e1 : (D.s.re ^ 2 - D.s.im ^ 2) / (4 * D.κ) = (D.s.re ^ 2 - D.s.im ^ 2) * (t / 4) := by
      rw [ht]; field_simp
    have e2 : π ^ 2 / D.κ = π ^ 2 * t := by rw [ht, div_eq_mul_inv]
    have e3 : π * D.s.im / D.κ = π * D.s.im * t := by rw [ht, div_eq_mul_inv]
    rw [e1, e2, e3]
    unfold τ₁ τ₂
    set b₂ : ℝ := b + 12 * D.ξ * a with hb₂
    have hbb : (b : ℝ) = b₂ - 12 * D.ξ * a := by rw [hb₂]; ring
    rw [hbb]
    set A : ℝ := a ^ 2 * (π * D.vt) - D.s.re * a with hA
    linear_combination (-(D.N * b₂ ^ 2 / 6) - A * t) * hκ' + (A * (6 * D.N * D.y ^ 2)) * htκ
  unfold dualF
  rw [norm_mul, Complex.norm_exp, hre]
  have hχ : ‖((chiZ (D.N * b) : ℤ) : ℂ)‖ = |((chiZ (D.N * b) : ℤ) : ℝ)| := by
    simp [Complex.norm_intCast]
  rw [hχ, mul_assoc (|((chiZ (D.N * b) : ℤ) : ℝ)|)]
  congr 1
  unfold hG
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The constants of the dominating Gaussians. -/
lemma K₂_pos : 0 < π * D.vt * D.N / 12 := by
  have := D.NR_pos
  have := D.vt_pos
  have := Real.pi_pos
  positivity

lemma K₃_pos : 0 < 6 * π * D.vt * D.N * D.y ^ 2 := by
  have := D.NR_pos
  have := D.vt_pos
  have := Real.pi_pos
  have := D.hy
  positivity

lemma K₁'_pos : 0 < π ^ 2 / D.κ := by
  have := D.κ_pos
  have := Real.pi_pos
  positivity

/-- The bound on `s` on the ball of radius `R`. -/
def sB₀ (R : ℝ) : ℝ := R * ‖((D.N : ℂ) * D.z * D.y)⁻¹‖

lemma s_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) : ‖(D.atσ τ).s‖ ≤ (D.sB₀ R) := by
  have h : ‖τ‖ ≤ R := by
    have : ‖τ‖ < R := by simpa using hτ
    exact this.le
  exact D.sBound_norm h

lemma abs_re_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) : |(D.atσ τ).s.re| ≤ (D.sB₀ R) :=
  (Complex.abs_re_le_norm _).trans (D.s_le hτ)

lemma abs_im_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) : |(D.atσ τ).s.im| ≤ (D.sB₀ R) :=
  (Complex.abs_im_le_norm _).trans (D.s_le hτ)

/-- The dominating family of the lattice terms. -/
def uLat (R : ℝ) (x : ℤ × ℤ × ℤ) : ℝ :=
  hS D.κ (D.sB₀ R) (x.2.2 + (6 * D.N * D.ξ ^ 2 * x.1 + D.N * D.ξ * x.2.1)) *
  hS (π * D.vt * D.N / 12) ((D.sB₀ R) * (D.N * D.y)) (x.2.1 + 12 * D.ξ * x.1) *
  hS (6 * π * D.vt * D.N * D.y ^ 2) ((D.sB₀ R) * (6 * D.N * D.y ^ 2)) x.1

lemma summable_uLat (R : ℝ) : Summable (D.uLat R) :=
  summable_triple_S D.κ_pos D.K₂_pos D.K₃_pos _ _ _ _ _ _

lemma norm_latTerm_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) (x : ℤ × ℤ × ℤ) :
    ‖(D.atσ τ).latTerm x.1 x.2.1 x.2.2‖ ≤ D.uLat R x := by
  have hN := D.NR_pos
  have hy := D.hy
  have hre := D.abs_re_le hτ
  have him := D.abs_im_le hτ
  rw [(D.atσ τ).norm_latTerm]
  change hG D.κ (D.atσ τ).s.re _ * hG (π * D.vt * D.N / 12) ((D.atσ τ).s.im * (D.N * D.y)) _ *
    hG (6 * π * D.vt * D.N * D.y ^ 2) (-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2))) _ ≤ _
  unfold uLat
  have h1 := hG_le_hS D.κ hre (x.2.2 + (6 * D.N * D.ξ ^ 2 * x.1 + D.N * D.ξ * x.2.1))
  have h2 : |(D.atσ τ).s.im * (D.N * D.y)| ≤ (D.sB₀ R) * (D.N * D.y) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (D.N : ℝ) * D.y)]
    gcongr
  have h3 : |-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2))| ≤ (D.sB₀ R) * (6 * D.N * D.y ^ 2) := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 6 * (D.N : ℝ) * D.y ^ 2)]
    gcongr
  have g2 := hG_le_hS (π * D.vt * D.N / 12) h2 (x.2.1 + 12 * D.ξ * x.1)
  have g3 := hG_le_hS (6 * π * D.vt * D.N * D.y ^ 2) h3 x.1
  have p1 := (hG_pos D.κ (D.atσ τ).s.re (x.2.2 + (6 * D.N * D.ξ ^ 2 * x.1 + D.N * D.ξ * x.2.1))).le
  have p2 := (hG_pos (π * D.vt * D.N / 12) ((D.atσ τ).s.im * (D.N * D.y))
    (x.2.1 + 12 * D.ξ * x.1)).le
  have p3 := (hG_pos (6 * π * D.vt * D.N * D.y ^ 2) (-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2)))
    x.1).le
  have q1 := (hS_pos D.κ (D.sB₀ R) (x.2.2 + (6 * D.N * D.ξ ^ 2 * x.1 + D.N * D.ξ * x.2.1))).le
  have q2 := (hS_pos (π * D.vt * D.N / 12) ((D.sB₀ R) * (D.N * D.y)) (x.2.1 + 12 * D.ξ * x.1)).le
  exact mul_le_mul (mul_le_mul h1 g2 p2 q1) g3 p3 (mul_nonneg q1 q2)

/-- The dominating family of the dual terms. -/
def uDual (R : ℝ) (x : ℤ × ℤ × ℤ) : ℝ :=
  Real.exp ((D.sB₀ R) ^ 2 / (4 * D.κ)) *
  (hS (π ^ 2 / D.κ) (π * (D.sB₀ R) / D.κ) (x.2.2 + (D.Zc.re * x.1 + 0 * x.2.1)) *
  hS (π * D.vt * D.N / 12) ((D.sB₀ R) * (D.N * D.y)) (x.2.1 + 12 * D.ξ * x.1) *
  hS (6 * π * D.vt * D.N * D.y ^ 2) ((D.sB₀ R) * (6 * D.N * D.y ^ 2)) x.1)

lemma summable_uDual (R : ℝ) : Summable (D.uDual R) :=
  (summable_triple_S D.K₁'_pos D.K₂_pos D.K₃_pos _ _ _ _ _ _).mul_left _

lemma norm_dualF_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) (x : ℤ × ℤ × ℤ) :
    ‖(D.atσ τ).dualF x.1 x.2.1 x.2.2‖ ≤ D.uDual R x := by
  have hN := D.NR_pos
  have hy := D.hy
  have hκ := D.κ_pos
  have hπ := Real.pi_pos
  have hre := D.abs_re_le hτ
  have him := D.abs_im_le hτ
  rw [(D.atσ τ).norm_dualF]
  change |((chiZ (D.N * x.2.1) : ℤ) : ℝ)| * Real.exp (((D.atσ τ).s.re ^ 2 - (D.atσ τ).s.im ^ 2) /
      (4 * D.κ)) * (hG (π ^ 2 / D.κ) (π * (D.atσ τ).s.im / D.κ) (x.2.2 + D.Zc.re * x.1) *
    hG (π * D.vt * D.N / 12) ((D.atσ τ).s.im * (D.N * D.y)) (x.2.1 + 12 * D.ξ * x.1) *
    hG (6 * π * D.vt * D.N * D.y ^ 2) (-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2))) x.1) ≤ _
  unfold uDual
  have hc : |((chiZ (D.N * x.2.1) : ℤ) : ℝ)| * Real.exp (((D.atσ τ).s.re ^ 2 - (D.atσ τ).s.im ^ 2) /
      (4 * D.κ)) ≤ Real.exp ((D.sB₀ R) ^ 2 / (4 * D.κ)) := by
    have h0 := chiZ_abs_le (D.N * x.2.1)
    have h1 : Real.exp (((D.atσ τ).s.re ^ 2 - (D.atσ τ).s.im ^ 2) / (4 * D.κ)) ≤
        Real.exp ((D.sB₀ R) ^ 2 / (4 * D.κ)) := by
      apply Real.exp_le_exp.mpr
      have h2 : (D.atσ τ).s.re ^ 2 ≤ (D.sB₀ R) ^ 2 := sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
      have h3 := sq_nonneg (D.atσ τ).s.im
      gcongr
      linarith
    calc _ ≤ 1 * Real.exp ((D.sB₀ R) ^ 2 / (4 * D.κ)) :=
          mul_le_mul h0 h1 (Real.exp_pos _).le zero_le_one
      _ = _ := one_mul _
  have h1 : |π * (D.atσ τ).s.im / D.κ| ≤ π * (D.sB₀ R) / D.κ := by
    rw [abs_div, abs_mul, abs_of_pos hπ, abs_of_pos hκ]
    gcongr
  have h2 : |(D.atσ τ).s.im * (D.N * D.y)| ≤ (D.sB₀ R) * (D.N * D.y) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (D.N : ℝ) * D.y)]
    gcongr
  have h3 : |-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2))| ≤ (D.sB₀ R) * (6 * D.N * D.y ^ 2) := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 6 * (D.N : ℝ) * D.y ^ 2)]
    gcongr
  have g1 := hG_le_hS (π ^ 2 / D.κ) h1 (x.2.2 + D.Zc.re * x.1)
  have g2 := hG_le_hS (π * D.vt * D.N / 12) h2 (x.2.1 + 12 * D.ξ * x.1)
  have g3 := hG_le_hS (6 * π * D.vt * D.N * D.y ^ 2) h3 x.1
  have e0 : (x.2.2 : ℝ) + (D.Zc.re * x.1 + 0 * x.2.1) = x.2.2 + D.Zc.re * x.1 := by ring
  rw [e0]
  have p1 := (hG_pos (π ^ 2 / D.κ) (π * (D.atσ τ).s.im / D.κ) (x.2.2 + D.Zc.re * x.1)).le
  have p2 := (hG_pos (π * D.vt * D.N / 12) ((D.atσ τ).s.im * (D.N * D.y))
    (x.2.1 + 12 * D.ξ * x.1)).le
  have p3 := (hG_pos (6 * π * D.vt * D.N * D.y ^ 2) (-((D.atσ τ).s.re * (6 * D.N * D.y ^ 2)))
    x.1).le
  have q1 := (hS_pos (π ^ 2 / D.κ) (π * (D.sB₀ R) / D.κ) (x.2.2 + D.Zc.re * x.1)).le
  have q2 := (hS_pos (π * D.vt * D.N / 12) ((D.sB₀ R) * (D.N * D.y)) (x.2.1 + 12 * D.ξ * x.1)).le
  have hG3 := mul_le_mul (mul_le_mul g1 g2 p2 q1) g3 p3 (mul_nonneg q1 q2)
  exact mul_le_mul hc hG3 (mul_nonneg (mul_nonneg p1 p2) p3) (Real.exp_pos _).le

end KData

end

end RamanujanTau.ThetaLift
