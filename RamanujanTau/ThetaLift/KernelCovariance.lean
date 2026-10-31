import RamanujanTau.ThetaLift.KernelSummable

/-!
# Covariance of the Shimura kernel in `w`

Γ₀(6N) acts on the binary forms `6Na X² + Nb X + c`. The action is a bijection of ℤ³ preserving the
discriminant, the character `χ₁₂(Nb)`, and `ψ(a)` for quadratic `ψ` modulo `N`. Reindexing the lattice
sum therefore gives weight `2λ` in `w`, with no convergence input.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex ComplexConjugate Rademacher MatrixGroups
open scoped Real

noncomputable section

/-- The action on coefficient triples, with `C = 6NE`. -/
def rhoFun (N A B E D : ℤ) (x : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 * A ^ 2 + N * x.2.1 * A * E + 6 * N * x.2.2 * E ^ 2,
   12 * x.1 * A * B + x.2.1 * (A * D + 6 * N * B * E) + 12 * x.2.2 * E * D,
   6 * N * x.1 * B ^ 2 + N * x.2.1 * B * D + x.2.2 * D ^ 2)

/-- The action is a bijection when the determinant is one. -/
def rhoEquiv (N A B E D : ℤ) (h : A * D - 6 * N * B * E = 1) : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ where
  toFun := rhoFun N A B E D
  invFun := rhoFun N D (-B) (-E) A
  left_inv := by
    rintro ⟨a, b, c⟩
    simp only [rhoFun, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (A*D*a - 6*B*E*N*a + a) * h
    · linear_combination (A*D*b - 6*B*E*N*b + b) * h
    · linear_combination (A*D*c - 6*B*E*N*c + c) * h
  right_inv := by
    rintro ⟨a, b, c⟩
    simp only [rhoFun, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (A*D*a - 6*B*E*N*a + a) * h
    · linear_combination (A*D*b - 6*B*E*N*b + b) * h
    · linear_combination (A*D*c - 6*B*E*N*c + c) * h

/-- The discriminant is invariant. -/
lemma disc_rho (N A B E D a b c : ℤ) (h : A * D - 6 * N * B * E = 1) :
    (N * (12 * a * A * B + b * (A * D + 6 * N * B * E) + 12 * c * E * D) ^ 2 : ℤ) -
        24 * ((a * A ^ 2 + N * b * A * E + 6 * N * c * E ^ 2) *
          (6 * N * a * B ^ 2 + N * b * B * D + c * D ^ 2)) = N * b ^ 2 - 24 * (a * c) := by
  linear_combination (A * D * N * b ^ 2 - 24 * A * D * a * c - 6 * B * E * N ^ 2 * b ^ 2 +
    144 * B * E * N * a * c + N * b ^ 2 - 24 * a * c) * h

/-- The form `6Na w̄² + Nb w̄ + c`. -/
def kQ (N a b c : ℤ) (w : ℂ) : ℂ := 6 * N * a * conj w ^ 2 + N * b * conj w + c

/-- One term of the kernel, in `w`, for fixed `vt` and `Zc`. -/
def kTerm (ψ : ℤ → ℂ) (N : ℤ) (vt : ℝ) (Zc : ℂ) (lam : ℕ) (w : ℂ) (x : ℤ × ℤ × ℤ) : ℂ :=
  ψ x.1 * (chiZ (N * x.2.1) : ℂ) * kQ N x.1 x.2.1 x.2.2 w ^ lam *
    cexp (-((π * vt / (6 * N * w.im ^ 2) * normSq (kQ N x.1 x.2.1 x.2.2 w) : ℝ) : ℂ) +
      2 * π * I * ((N * x.2.1 ^ 2 - 24 * (x.1 * x.2.2) : ℤ) / 24) * Zc)

/-- **The kernel.** -/
def kernel (ψ : ℤ → ℂ) (N : ℤ) (vt : ℝ) (Zc : ℂ) (lam : ℕ) (w : ℂ) : ℂ :=
  ((w.im : ℂ) ^ (2 * lam))⁻¹ * ∑' x : ℤ × ℤ × ℤ, kTerm ψ N vt Zc lam w x

lemma conj_mob (γ : SL(2, ℤ)) (w : ℂ) :
    conj (mob γ w) = ((γ 0 0 : ℂ) * conj w + γ 0 1) / conj (lin γ w) := by
  unfold mob lin
  simp

lemma conj_lin (γ : SL(2, ℤ)) (w : ℂ) : conj (lin γ w) = (γ 1 0 : ℂ) * conj w + γ 1 1 := by
  unfold lin
  simp

/-- The form transforms by `conj(j)⁻²`. -/
lemma kQ_mob (N : ℤ) (γ : SL(2, ℤ)) {E : ℤ} (hE : γ 1 0 = 6 * N * E) {w : ℂ} (hw : 0 < w.im)
    (x : ℤ × ℤ × ℤ) :
    kQ N x.1 x.2.1 x.2.2 (mob γ w) = (conj (lin γ w))⁻¹ ^ 2 *
      (let y := rhoFun N (γ 0 0) (γ 0 1) E (γ 1 1) x; kQ N y.1 y.2.1 y.2.2 w) := by
  have hj : lin γ w ≠ 0 := denom_ne_zero' γ hw
  have hjb : conj (lin γ w) ≠ 0 := by simpa using hj
  have hc : conj (lin γ w) = 6 * N * E * conj w + γ 1 1 := by
    rw [conj_lin, hE]
    push_cast
    ring
  unfold kQ rhoFun
  rw [conj_mob]
  simp only
  generalize hG : conj (lin γ w) = J at *
  push_cast
  field_simp
  rw [hc]
  ring

lemma mob_im' (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    (mob γ w).im = w.im / normSq (lin γ w) := by
  have h := mob_im γ hw
  rw [Complex.mul_conj] at h
  exact_mod_cast h

/-- **Covariance of the kernel in weight `2λ`.** -/
theorem kernel_covariant (ψ : ℤ → ℂ) (N : ℤ) (hN : N ≠ 0) (vt : ℝ) (Zc : ℂ) (lam : ℕ)
    (hψ : ∀ a A k : ℤ, IsCoprime A N → ψ (a * A ^ 2 + N * k) = ψ a)
    (γ : SL(2, ℤ)) {E : ℤ} (hE : γ 1 0 = 6 * N * E) {w : ℂ} (hw : 0 < w.im) :
    kernel ψ N vt Zc lam (mob γ w) = lin γ w ^ (2 * lam) * kernel ψ N vt Zc lam w := by
  have hdet : γ 0 0 * γ 1 1 - 6 * N * γ 0 1 * E = 1 := by
    have h := γ.property
    rw [Matrix.det_fin_two, hE] at h
    linear_combination h
  have hj : lin γ w ≠ 0 := denom_ne_zero' γ hw
  have hjb : conj (lin γ w) ≠ 0 := by simpa using hj
  have hn : 0 < normSq (lin γ w) := Complex.normSq_pos.mpr hj
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hw0 : w.im ≠ 0 := hw.ne'
  have hterm : ∀ x : ℤ × ℤ × ℤ, kTerm ψ N vt Zc lam (mob γ w) x =
      (conj (lin γ w))⁻¹ ^ (2 * lam) *
        kTerm ψ N vt Zc lam w (rhoEquiv N (γ 0 0) (γ 0 1) E (γ 1 1) hdet x) := by
    rintro ⟨a, b, c⟩
    set A := γ 0 0
    set B := γ 0 1
    set D := γ 1 1
    change _ = _ * kTerm ψ N vt Zc lam w (rhoFun N A B E D (a, b, c))
    have hQ := kQ_mob N γ hE hw (a, b, c)
    simp only at hQ
    set y := rhoFun N A B E D (a, b, c) with hy
    have hψy : ψ y.1 = ψ a := by
      have := hψ a A (b * A * E + 6 * c * E ^ 2) ⟨D, -(6 * B * E), by linear_combination hdet⟩
      rw [← this]
      congr 1
      simp only [hy, rhoFun]
      ring
    have hχ : chiZ (N * y.2.1) = chiZ (N * b) := by
      have e : N * y.2.1 = N * b + 12 * (N * a * A * B + N * b * (N * B * E) + N * c * E * D) := by
        simp only [hy, rhoFun]
        linear_combination (N * b) * hdet
      rw [e, chiZ_add_mul]
    have hdisc : N * y.2.1 ^ 2 - 24 * (y.1 * y.2.2) = N * b ^ 2 - 24 * (a * c) := by
      simp only [hy, rhoFun]
      exact disc_rho N A B E D a b c hdet
    have hκ : π * vt / (6 * N * (mob γ w).im ^ 2) * normSq (kQ N a b c (mob γ w)) =
        π * vt / (6 * N * w.im ^ 2) * normSq (kQ N y.1 y.2.1 y.2.2 w) := by
      rw [hQ, mob_im' γ hw, map_mul, map_pow, map_inv₀, Complex.normSq_conj]
      field_simp
    unfold kTerm
    simp only
    rw [hκ, hψy, hχ, hdisc, hQ, mul_pow, ← pow_mul]
    ring
  unfold kernel
  have hsum : ∑' x : ℤ × ℤ × ℤ, kTerm ψ N vt Zc lam (mob γ w) x =
      (conj (lin γ w))⁻¹ ^ (2 * lam) * ∑' x : ℤ × ℤ × ℤ, kTerm ψ N vt Zc lam w x := by
    rw [tsum_congr hterm, tsum_mul_left]
    congr 1
    exact (rhoEquiv N (γ 0 0) (γ 0 1) E (γ 1 1) hdet).tsum_eq _
  rw [hsum]
  have him : (((mob γ w).im : ℝ) : ℂ) = (w.im : ℂ) / (lin γ w * conj (lin γ w)) := by
    rw [mob_im' γ hw, Complex.mul_conj]
    push_cast
    rfl
  rw [him, div_pow, inv_div, mul_pow]
  have hc : conj (lin γ w) ^ (2 * lam) * (conj (lin γ w))⁻¹ ^ (2 * lam) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hjb, one_pow]
  rw [div_eq_mul_inv]
  linear_combination (lin γ w ^ (2 * lam) * ((w.im : ℂ) ^ (2 * lam))⁻¹ *
    ∑' x : ℤ × ℤ × ℤ, kTerm ψ N vt Zc lam w x) * hc

end

end RamanujanTau.ThetaLift
