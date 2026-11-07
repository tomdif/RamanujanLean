import RamanujanTau.ThetaLift.KernelTerms

/-!
# Summability of the kernel on ℤ³

The real exponent of a lattice term is a sum of three squares in sheared coordinates, plus a linear
form. A Gaussian bound that is uniform under real shifts then gives summability on ℤ³.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Real
open scoped Real

noncomputable section

/-- A Gaussian with a linear term. -/
def hG (K L x : ℝ) : ℝ := Real.exp (-K * x ^ 2 + L * x)

lemma hG_pos (K L x : ℝ) : 0 < hG K L x := Real.exp_pos _

lemma summable_gauss_int {K : ℝ} (hK : 0 < K) :
    Summable fun n : ℤ => Real.exp (-K * (n : ℝ) ^ 2) := by
  have hτ : 0 < ((K / π : ℝ) * I : ℂ).im := by
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    positivity
  have h := ((summable_jacobiTheta₂_term_iff 0 _).mpr hτ).norm
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term]
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero, zero_im]
  congr 1
  have := Real.pi_ne_zero
  field_simp
  ring

/-- **The shift-uniform Gaussian bound.** -/
lemma gauss_uniform {K : ℝ} (hK : 0 < K) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, Summable (fun n : ℤ => hG K L (n + u)) ∧
      ∑' n : ℤ, hG K L (n + u) ≤ C := by
  let M := Real.exp (L ^ 2 / (2 * K) + K / 8)
  let G := ∑' n : ℤ, Real.exp (-(K / 4) * (n : ℝ) ^ 2)
  have hsum := summable_gauss_int (K := K / 4) (by positivity)
  refine ⟨M * G, mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le), ?_⟩
  intro u
  let k : ℤ := round u
  let r : ℝ := u - k
  have hr : |r| ≤ 1 / 2 := abs_sub_round u
  have hr2 : r ^ 2 ≤ 1 / 4 := by
    have := sq_abs r
    nlinarith [abs_nonneg r]
  have hbound : ∀ n : ℤ, hG K L (n + u) ≤ M * Real.exp (-(K / 4) * (((n + k : ℤ) : ℝ)) ^ 2) := by
    intro n
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    set x : ℝ := n + u with hx
    have hxm : x = ((n + k : ℤ) : ℝ) + r := by
      simp only [hx, r]
      push_cast
      ring
    set t : ℝ := ((n + k : ℤ) : ℝ) with ht
    have h1 : t ^ 2 / 2 - r ^ 2 ≤ x ^ 2 := by
      rw [hxm]
      nlinarith [sq_nonneg (t + 2 * r)]
    have h2 : L * x ≤ L ^ 2 / (2 * K) + K * x ^ 2 / 2 := by
      have hk : 0 ≤ (L - K * x) ^ 2 / (2 * K) := by positivity
      have e : (L - K * x) ^ 2 / (2 * K) = L ^ 2 / (2 * K) - L * x + K * x ^ 2 / 2 := by
        field_simp
        ring
      linarith
    have h3 : K * (t ^ 2 / 2 - r ^ 2) ≤ K * x ^ 2 := mul_le_mul_of_nonneg_left h1 hK.le
    have h4 : K * r ^ 2 ≤ K * (1 / 4) := mul_le_mul_of_nonneg_left hr2 hK.le
    nlinarith
  have hs2 : Summable fun n : ℤ => M * Real.exp (-(K / 4) * (((n + k : ℤ) : ℝ)) ^ 2) :=
    ((Equiv.addRight k).summable_iff.mpr hsum).mul_left M
  have hs1 : Summable fun n : ℤ => hG K L (n + u) :=
    Summable.of_nonneg_of_le (fun _ => (hG_pos _ _ _).le) hbound hs2
  refine ⟨hs1, ?_⟩
  calc ∑' n : ℤ, hG K L (n + u) ≤ ∑' n : ℤ, M * Real.exp (-(K / 4) * (((n + k : ℤ) : ℝ)) ^ 2) :=
        hs1.tsum_le_tsum hbound hs2
    _ = M * G := by
        rw [tsum_mul_left]
        congr 1
        exact (Equiv.addRight k).tsum_eq fun n : ℤ => Real.exp (-(K / 4) * (n : ℝ) ^ 2)

/-- Iterated summability for a triangular product. -/
theorem summable_triple_abstract {F : ℤ → ℤ → ℤ → ℝ} {G : ℤ → ℤ → ℝ} {H : ℤ → ℝ} {C₁ C₂ : ℝ}
    (hF0 : ∀ a b c, 0 ≤ F a b c) (hG0 : ∀ a b, 0 ≤ G a b) (hH0 : ∀ a, 0 ≤ H a)
    (hC₁ : 0 ≤ C₁) (hF : ∀ a b, Summable (F a b) ∧ ∑' c, F a b c ≤ C₁)
    (hG : ∀ a, Summable (G a) ∧ ∑' b, G a b ≤ C₂) (hH : Summable H) :
    Summable fun x : ℤ × ℤ × ℤ => F x.1 x.2.1 x.2.2 * G x.1 x.2.1 * H x.1 := by
  have hfix : ∀ a : ℤ, Summable (fun y : ℤ × ℤ => F a y.1 y.2 * G a y.1) ∧
      ∑' y : ℤ × ℤ, F a y.1 y.2 * G a y.1 ≤ C₁ * C₂ := by
    intro a
    have hi : ∀ b : ℤ, Summable fun c : ℤ => F a b c * G a b := fun b => (hF a b).1.mul_right _
    have ht : ∀ b : ℤ, ∑' c : ℤ, F a b c * G a b ≤ C₁ * G a b := by
      intro b
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (hF a b).2 (hG0 a b)
    have hsb : Summable fun b : ℤ => C₁ * G a b := (hG a).1.mul_left C₁
    have hso : Summable fun b : ℤ => ∑' c : ℤ, F a b c * G a b :=
      Summable.of_nonneg_of_le (fun b => tsum_nonneg fun c => mul_nonneg (hF0 _ _ _) (hG0 _ _)) ht hsb
    have hprod : Summable (fun y : ℤ × ℤ => F a y.1 y.2 * G a y.1) :=
      (summable_prod_of_nonneg fun y => mul_nonneg (hF0 _ _ _) (hG0 _ _)).mpr ⟨hi, hso⟩
    refine ⟨hprod, ?_⟩
    have e : ∑' y : ℤ × ℤ, F a y.1 y.2 * G a y.1 = ∑' b : ℤ, ∑' c : ℤ, F a b c * G a b :=
      hprod.tsum_prod' hi
    rw [e]
    calc _ ≤ ∑' b : ℤ, C₁ * G a b := hso.tsum_le_tsum ht hsb
      _ ≤ C₁ * C₂ := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hG a).2 hC₁
  have h1 : ∀ a : ℤ, Summable fun y : ℤ × ℤ => F a y.1 y.2 * G a y.1 * H a :=
    fun a => (hfix a).1.mul_right _
  have hb : ∀ a : ℤ, ∑' y : ℤ × ℤ, F a y.1 y.2 * G a y.1 * H a ≤ C₁ * C₂ * H a := by
    intro a
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hfix a).2 (hH0 a)
  have h2 : Summable fun a : ℤ => ∑' y : ℤ × ℤ, F a y.1 y.2 * G a y.1 * H a :=
    Summable.of_nonneg_of_le (fun a => tsum_nonneg fun y => mul_nonneg
      (mul_nonneg (hF0 _ _ _) (hG0 _ _)) (hH0 _)) hb (hH.mul_left _)
  have hnn : 0 ≤ fun x : ℤ × ℤ × ℤ => F x.1 x.2.1 x.2.2 * G x.1 x.2.1 * H x.1 :=
    fun x => mul_nonneg (mul_nonneg (hF0 _ _ _) (hG0 _ _)) (hH0 _)
  exact (summable_prod_of_nonneg hnn).mpr ⟨h1, h2⟩

/-- **Summability on ℤ³ in triangular coordinates.** -/
theorem summable_triple {K₁ K₂ K₃ : ℝ} (h₁ : 0 < K₁) (h₂ : 0 < K₂) (h₃ : 0 < K₃)
    (L₁ L₂ L₃ p q r : ℝ) :
    Summable fun x : ℤ × ℤ × ℤ =>
      hG K₁ L₁ (x.2.2 + (q * x.1 + r * x.2.1)) * hG K₂ L₂ (x.2.1 + p * x.1) * hG K₃ L₃ x.1 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := gauss_uniform h₁ L₁
  obtain ⟨C₂, hC₂, hb₂⟩ := gauss_uniform h₂ L₂
  obtain ⟨C₃, -, hb₃⟩ := gauss_uniform h₃ L₃
  have hH : Summable fun a : ℤ => hG K₃ L₃ a := by
    have := (hb₃ 0).1
    simpa only [add_zero] using this
  exact summable_triple_abstract (F := fun a b c => hG K₁ L₁ (c + (q * a + r * b)))
    (G := fun a b => hG K₂ L₂ (b + p * a)) (H := fun a => hG K₃ L₃ a)
    (fun _ _ _ => (hG_pos _ _ _).le) (fun _ _ => (hG_pos _ _ _).le) (fun _ => (hG_pos _ _ _).le) hC₁
    (fun _ _ => hb₁ _) (fun _ => hb₂ _) hH

namespace KData
variable (D : KData)

/-- The shear coordinates and the exact norm of a lattice term. -/
lemma Zc_im : D.Zc.im = -D.vt := by
  have hz := D.z_ne
  have hzb := D.zb_ne
  have hN := D.N_ne
  have he : D.Zc = -((D.vt : ℂ) / D.v) * D.z := by
    rw [D.vt_cast]
    unfold Zc
    have hv := D.v_ne
    field_simp
  rw [he]
  have hr : ((D.vt : ℂ) / D.v) = ((D.vt / D.v : ℝ) : ℂ) := by push_cast; ring
  rw [hr]
  simp only [neg_mul, neg_im, im_ofReal_mul]
  have hv := D.v_pos
  have : D.z.im = D.v := rfl
  rw [this]
  field_simp

/-- The positive constants in the three squares. -/
lemma κ_mul : D.κ * (6 * D.N * D.y ^ 2) = π * D.vt := by
  have hN := D.NR_pos
  have hy := D.hy
  unfold κ
  field_simp

/-- **The norm of a lattice term.** -/
theorem norm_latTerm (a b c : ℤ) :
    ‖D.latTerm a b c‖ =
      hG D.κ D.s.re (c + (6 * D.N * D.ξ ^ 2 * a + D.N * D.ξ * b)) *
      hG (π * D.vt * D.N / 12) (D.s.im * (D.N * D.y)) (b + 12 * D.ξ * a) *
      hG (6 * π * D.vt * D.N * D.y ^ 2) (-(D.s.re * (6 * D.N * D.y ^ 2))) a := by
  set A : ℝ := c + D.τ₁ a b with hA
  set B : ℝ := D.τ₂ a b with hB
  set X : ℝ := D.N * b ^ 2 / 24 - a * c with hX
  have hw : D.s * (c + D.τ₁ a b + I * D.τ₂ a b) - D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2) +
      2 * π * I * (D.N * b ^ 2 / 24 - a * c) * D.Zc =
      D.s * ((A : ℂ) + I * B) - ((D.κ * (A ^ 2 + B ^ 2) : ℝ) : ℂ) +
        ((2 * π * X : ℝ) : ℂ) * (I * D.Zc) := by
    simp only [hA, hB, hX]
    push_cast
    ring
  have hre : (D.s * ((A : ℂ) + I * B) - ((D.κ * (A ^ 2 + B ^ 2) : ℝ) : ℂ) +
      ((2 * π * X : ℝ) : ℂ) * (I * D.Zc)).re =
      D.s.re * A - D.s.im * B - D.κ * (A ^ 2 + B ^ 2) + 2 * π * X * D.vt := by
    simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im, D.Zc_im]
    ring
  unfold latTerm
  rw [hw, Complex.norm_exp, hre]
  unfold hG
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [hA, hB, hX, τ₁, τ₂]
  push_cast
  have h := D.κ_mul
  set c₂ : ℝ := c + (6 * D.N * D.ξ ^ 2 * a + D.N * D.ξ * b) with hc₂
  set b₂ : ℝ := b + 12 * D.ξ * a with hb₂
  linear_combination (2 * a * c₂ - 6 * D.N * a ^ 2 * D.y ^ 2 - D.N * b₂ ^ 2 / 6) * h

/-- **The lattice terms are summable on ℤ³.** -/
theorem summable_latTerm : Summable fun x : ℤ × ℤ × ℤ => D.latTerm x.1 x.2.1 x.2.2 := by
  have hN := D.NR_pos
  have hvt := D.vt_pos
  have hy := D.hy
  have hπ := Real.pi_pos
  apply Summable.of_norm
  have h := summable_triple D.κ_pos (K₂ := π * D.vt * D.N / 12) (by positivity)
    (K₃ := 6 * π * D.vt * D.N * D.y ^ 2) (by positivity) D.s.re (D.s.im * (D.N * D.y))
    (-(D.s.re * (6 * D.N * D.y ^ 2))) (12 * D.ξ) (6 * D.N * D.ξ ^ 2) (D.N * D.ξ)
  exact h.congr fun x => (D.norm_latTerm x.1 x.2.1 x.2.2).symm

end KData

end

end RamanujanTau.ThetaLift
