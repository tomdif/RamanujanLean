import RamanujanTau.ThetaLift.KernelPoisson

/-!
# The terms of the Shimura kernel

For fixed `z`, `w = ξ + iy`, a level `N`, and a generating parameter `σ`, this file defines the lattice
term and its Poisson dual, and identifies the sum over `b` with the Jacobi theta function `Θ`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex ComplexConjugate
open scoped Real

noncomputable section

/-- `χ₁₂` is multiplicative. -/
lemma chiZ_mul (x y : ℤ) : chiZ (x * y) = chiZ x * chiZ y := by
  have hx0 := Int.emod_nonneg x (by norm_num : (12 : ℤ) ≠ 0)
  have hx1 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 12)
  have hy0 := Int.emod_nonneg y (by norm_num : (12 : ℤ) ≠ 0)
  have hy1 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 12)
  have hm : (x * y) % 12 = ((x % 12) * (y % 12)) % 12 := Int.mul_emod x y 12
  unfold chiZ
  rw [hm]
  generalize x % 12 = r at *
  generalize y % 12 = t at *
  interval_cases r <;> interval_cases t <;> norm_num

/-- The parameters of the kernel at a point. -/
structure KData where
  N : ℕ
  z : ℂ
  ξ : ℝ
  y : ℝ
  σ : ℂ
  hN : N ≠ 0
  hz : 0 < z.im
  hy : 0 < y

namespace KData
variable (D : KData)

def v : ℝ := D.z.im
def zb : ℂ := conj D.z
def vt : ℝ := D.v / (D.N * normSq D.z)
def zt : ℂ := -1 / (D.N * D.z)
def Zc : ℂ := -1 / (D.N * D.zb)
def κ : ℝ := π * D.vt / (6 * D.N * D.y ^ 2)
def s : ℂ := I * D.σ / (D.N * D.z * D.y)
def τ₁ (a b : ℤ) : ℝ := 6 * D.N * a * (D.ξ ^ 2 - D.y ^ 2) + D.N * b * D.ξ
def τ₂ (a b : ℤ) : ℝ := -(D.N * D.y * (b + 12 * a * D.ξ))

lemma z_ne : D.z ≠ 0 := fun h => by have := D.hz; simp [h] at this
lemma zb_ne : D.zb ≠ 0 := by simpa [zb] using D.z_ne
lemma N_ne : (D.N : ℂ) ≠ 0 := by exact_mod_cast D.hN
lemma NR_pos : (0 : ℝ) < D.N := by exact_mod_cast Nat.pos_of_ne_zero D.hN
lemma v_pos : 0 < D.v := D.hz
lemma vt_pos : 0 < D.vt := by
  have := D.NR_pos
  have hn : 0 < normSq D.z := Complex.normSq_pos.mpr D.z_ne
  have hv := D.v_pos
  unfold vt
  positivity
lemma κ_pos : 0 < D.κ := by
  have := D.NR_pos
  have := D.vt_pos
  have := D.hy
  have := Real.pi_pos
  unfold κ
  positivity
lemma y_ne : (D.y : ℂ) ≠ 0 := by exact_mod_cast D.hy.ne'
lemma v_ne : (D.v : ℂ) ≠ 0 := by exact_mod_cast D.v_pos.ne'
lemma κ_ne : (D.κ : ℂ) ≠ 0 := by exact_mod_cast D.κ_pos.ne'

lemma z_mul_zb : D.z * D.zb = (normSq D.z : ℂ) := by
  simp [zb, Complex.mul_conj]

lemma sub_zb : D.z - D.zb = 2 * I * D.v := by
  simp only [zb, v, Complex.sub_conj]
  push_cast
  ring

lemma vt_cast : (D.vt : ℂ) = D.v / (D.N * (D.z * D.zb)) := by
  rw [z_mul_zb]
  simp [vt]

lemma zt_sub : D.zt - D.Zc = 2 * I * D.vt := by
  have hz := D.z_ne
  have hzb := D.zb_ne
  have hN := D.N_ne
  rw [vt_cast]
  unfold zt Zc
  field_simp
  linear_combination (1 : ℂ) * D.sub_zb

lemma κ_cast : (D.κ : ℂ) = π * D.v / (6 * D.N ^ 2 * D.y ^ 2 * D.z * D.zb) := by
  have hz := D.z_ne
  have hzb := D.zb_ne
  have hN := D.N_ne
  have hy := D.y_ne
  unfold κ
  push_cast
  rw [vt_cast]
  field_simp

/-- The lattice term, with `Q^λ` replaced by an exponential. -/
def latTerm (a b c : ℤ) : ℂ :=
  cexp (D.s * (c + D.τ₁ a b + I * D.τ₂ a b) -
    D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2) +
    2 * π * I * (D.N * b ^ 2 / 24 - a * c) * D.Zc)

/-- The exponent of the Poisson dual term. -/
def dualE (a b m : ℤ) : ℂ :=
  D.s * I * D.τ₂ a b - D.κ * D.τ₂ a b ^ 2 + 2 * π * I * D.τ₁ a b * (a * D.Zc + m) +
    D.s ^ 2 / (4 * D.κ) - π * I * D.s * (a * D.Zc + m) / D.κ -
    π ^ 2 * (a * D.Zc + m) ^ 2 / D.κ

/-- Poisson summation for the lattice term. -/
theorem tsum_latTerm (a b : ℤ) :
    ∑' c : ℤ, D.latTerm a b c = cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc) *
      (((√(π / D.κ) : ℝ) : ℂ) * ∑' m : ℤ, cexp (D.dualE a b m)) := by
  have h := poisson_c D.κ_pos (D.τ₁ a b) (D.τ₂ a b) D.s ((a : ℂ) * D.Zc)
  have hterm : ∀ c : ℤ, D.latTerm a b c = cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc) *
      cexp (D.s * (c + D.τ₁ a b + I * D.τ₂ a b) - D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2) -
        2 * π * I * c * ((a : ℂ) * D.Zc)) := by
    intro c
    rw [← Complex.exp_add]
    unfold latTerm
    congr 1
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, h]
  rfl

/-- The elliptic variable of the `b`-sum. -/
def nω (a m : ℤ) : ℂ := D.N * (D.ξ * (a * D.zt + m) - D.y * D.s / (2 * π))

/-- Separating the `b`-dependence of the dual exponent. -/
theorem dualE_b (a b m : ℤ) :
    2 * π * I * (D.N * b ^ 2 / 24) * D.Zc + D.dualE a b m =
      D.dualE a 0 m + (2 * π * I * b * D.nω a m + π * I * b ^ 2 * (D.N * D.zt / 12)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hκ : (D.κ : ℂ) * (6 * D.N * D.y ^ 2) = π * D.vt := by
    have hN := D.N_ne
    have hy := D.y_ne
    unfold κ
    push_cast
    field_simp
  have hrel := D.zt_sub
  have hI := Complex.I_sq
  have ht : 2 * (π : ℂ) * (D.y * D.s / (2 * π)) = D.y * D.s := by field_simp
  have hszt : D.zt = D.Zc + 2 * I * D.vt := by rw [← hrel]; ring
  unfold dualE nω τ₁ τ₂
  push_cast
  rw [hszt]
  generalize D.y * D.s / (2 * (π : ℂ)) = t at ht ⊢
  linear_combination (I * b * D.N) * ht -
    ((D.N : ℂ) * b ^ 2 / 6 + 4 * D.N * a * D.ξ * b) * hκ -
    (π * D.vt * ((D.N : ℂ) * b ^ 2 / 6 + 4 * D.N * a * D.ξ * b)) * hI

/-- The linear form `Nmz - a`. -/
def L (a m : ℤ) : ℂ := D.N * m * D.z - a
/-- Its conjugate. -/
def Lb (a m : ℤ) : ℂ := D.N * m * D.zb - a
/-- The elliptic variable after inversion. -/
def ζ₀ (a m : ℤ) : ℂ := D.ξ * D.L a m + D.σ / (2 * π * I)

lemma N_zt : (D.N : ℂ) * D.zt = -1 / D.z := by
  have hz := D.z_ne
  have hN := D.N_ne
  unfold zt
  field_simp

lemma nω_eq (a m : ℤ) : D.nω a m = D.ζ₀ a m / D.z := by
  have hz := D.z_ne
  have hN := D.N_ne
  have hy := D.y_ne
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold nω ζ₀ L s zt
  field_simp
  linear_combination (-D.σ) * Complex.I_sq

/-- The Poincaré exponent. -/
def pE (a m : ℤ) : ℂ :=
  6 * D.y * D.σ * D.Lb a m / D.v - 3 * D.σ ^ 2 * D.Lb a m / (2 * π * D.L a m * D.v) -
    6 * π * D.y ^ 2 * D.L a m * D.Lb a m / D.v +
    2 * π * I * (6 * (D.N * m) * D.ζ₀ a m ^ 2 / D.L a m)

/-- The term indexed by `(a,m)`. -/
def pTerm (a m : ℤ) : ℂ := cexp (D.pE a m) * chiTheta D.z (D.ζ₀ a m)

/-- The dual exponent at `b = 0` plus the inversion exponent is the Poincaré exponent. -/
theorem dualE_add (a m : ℤ) (hL : D.L a m ≠ 0) :
    D.dualE a 0 m + 2 * π * I * (6 * D.ζ₀ a m ^ 2 / D.z) = D.pE a m := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz := D.z_ne
  have hzb := D.zb_ne
  have hN := D.N_ne
  have h := exponent_identity (z := D.z) (zb := D.zb) (v := D.v) (ξ := D.ξ) (y := D.y) (σ := D.σ)
    (a := a) (n := D.N * m) (N := D.N) (p := π) hz hzb D.v_ne D.y_ne hN hπ D.sub_zb hL
  have hW : (a : ℂ) * D.Zc + m = D.Lb a m / (D.N * D.zb) := by
    unfold Zc Lb
    field_simp
    ring
  have h1 : ((D.τ₁ a 0 : ℝ) : ℂ) = 6 * D.N * a * (D.ξ ^ 2 - D.y ^ 2) := by
    unfold τ₁
    push_cast
    ring
  have h2 : ((D.τ₂ a 0 : ℝ) : ℂ) = -12 * D.N * a * D.y * D.ξ := by
    unfold τ₂
    push_cast
    ring
  unfold dualE pE
  rw [hW, h1, h2, D.κ_cast]
  exact h

/-- The sum over `b` at fixed `(a,m)`. -/
theorem tsum_b (a m : ℤ) :
    ∑' b : ℤ, (chiZ (D.N * b) : ℂ) * cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc + D.dualE a b m) =
      chiZ D.N * cexp (D.dualE a 0 m) * chiTheta (-1 / D.z) (D.ζ₀ a m / D.z) := by
  rw [chiTheta, ← D.nω_eq, ← D.N_zt, ← tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [D.dualE_b, Complex.exp_add, chiZ_mul]
  unfold jacobiTheta₂_term
  push_cast
  ring

/-- Inversion at fixed `(a,m)`. -/
theorem dual_inverted (a m : ℤ) (hL : D.L a m ≠ 0) :
    cexp (D.dualE a 0 m) * chiTheta (-1 / D.z) (D.ζ₀ a m / D.z) =
      sqrt D.z * e24 (-3) * D.pTerm a m := by
  rw [chiTheta_inversion _ D.hz, pTerm, ← D.dualE_add a m hL, Complex.exp_add]
  ring

/-- The dual term at `b = 0` is a theta term in `m`. -/
lemma dualE_m (a m : ℤ) :
    D.dualE a 0 m = D.dualE a 0 0 + (2 * π * I * m *
      (D.τ₁ a 0 - D.s / (2 * D.κ) + I * π * (a * D.Zc) / D.κ) + π * I * m ^ 2 * (I * π / D.κ)) := by
  have hκ := D.κ_ne
  unfold dualE
  push_cast
  field_simp
  linear_combination (-(π ^ 2 * (2 * (a : ℂ) * D.Zc * m + m ^ 2) * 2 * 2) ) * Complex.I_sq

lemma summable_exp_dualE (a : ℤ) : Summable fun m : ℤ => cexp (D.dualE a 0 m) := by
  have hκ := D.κ_pos
  have hτ : 0 < (I * (π : ℂ) / D.κ).im := by
    have : (I * (π : ℂ) / D.κ) = (((π / D.κ : ℝ) : ℂ)) * I := by
      push_cast
      ring
    rw [this]
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    have := Real.pi_pos
    positivity
  have h := ((summable_jacobiTheta₂_term_iff (D.τ₁ a 0 - D.s / (2 * D.κ) +
    I * π * (a * D.Zc) / D.κ) (I * π / D.κ)).mpr hτ).mul_left (cexp (D.dualE a 0 0))
  refine h.congr fun m => ?_
  rw [D.dualE_m a m, Complex.exp_add]
  rfl

lemma im_Nzt : 0 < ((D.N : ℂ) * D.zt / 12).im := by
  rw [D.N_zt]
  have hn : 0 < normSq D.z := Complex.normSq_pos.mpr D.z_ne
  have h : (-1 / D.z).im = D.z.im / normSq D.z := by
    simp [neg_div, inv_im]
  have h12 : (-1 / D.z / 12).im = (-1 / D.z).im / 12 := by simp
  rw [h12, h]
  have := D.hz
  positivity

lemma nω_im (a m : ℤ) : (D.nω a m).im = (D.nω a 0).im := by
  unfold nω
  simp

/-- The doubly indexed term of the Poisson dual. -/
def dualF (a : ℤ) (b m : ℤ) : ℂ :=
  (chiZ (D.N * b) : ℂ) * cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc + D.dualE a b m)

lemma chiZ_norm (x : ℤ) : ‖((chiZ x : ℤ) : ℂ)‖ ≤ 1 := by
  unfold chiZ
  split_ifs <;> simp

lemma summable_dualF (a : ℤ) : Summable fun p : ℤ × ℤ => D.dualF a p.1 p.2 := by
  have hB : Summable fun b : ℤ => ‖jacobiTheta₂_term b (D.nω a 0) ((D.N : ℂ) * D.zt / 12)‖ :=
    ((summable_jacobiTheta₂_term_iff _ _).mpr D.im_Nzt).norm
  have hA : Summable fun m : ℤ => ‖cexp (D.dualE a 0 m)‖ := (D.summable_exp_dualE a).norm
  have hp := hB.mul_of_nonneg hA (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_norm_bounded hp fun p => ?_
  unfold dualF
  rw [D.dualE_b, Complex.exp_add, norm_mul, norm_mul]
  have hterm : ‖cexp (2 * π * I * p.1 * D.nω a p.2 + π * I * p.1 ^ 2 * ((D.N : ℂ) * D.zt / 12))‖ =
      ‖jacobiTheta₂_term p.1 (D.nω a 0) ((D.N : ℂ) * D.zt / 12)‖ := by
    have := norm_jacobiTheta₂_term p.1 (D.nω a p.2) ((D.N : ℂ) * D.zt / 12)
    rw [D.nω_im, ← norm_jacobiTheta₂_term] at this
    exact this
  rw [hterm]
  calc _ ≤ 1 * (‖cexp (D.dualE a 0 p.2)‖ * ‖jacobiTheta₂_term p.1 (D.nω a 0) ((D.N : ℂ) * D.zt / 12)‖) :=
        mul_le_mul_of_nonneg_right (chiZ_norm _) (by positivity)
    _ = _ := by ring

/-- **The kernel identity at fixed `a`.** -/
theorem lattice_a (a : ℤ) (hL : ∀ m, D.L a m ≠ 0) :
    ∑' b : ℤ, ∑' c : ℤ, (chiZ (D.N * b) : ℂ) * D.latTerm a b c =
      chiZ D.N * ((√(π / D.κ) : ℝ) : ℂ) * (sqrt D.z * e24 (-3)) * ∑' m : ℤ, D.pTerm a m := by
  have h1 : ∀ b : ℤ, ∑' c : ℤ, (chiZ (D.N * b) : ℂ) * D.latTerm a b c =
      ((√(π / D.κ) : ℝ) : ℂ) * ∑' m : ℤ, D.dualF a b m := by
    intro b
    have hF : ∀ m : ℤ, D.dualF a b m = ((chiZ (D.N * b) : ℂ) *
        cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc)) * cexp (D.dualE a b m) := by
      intro m
      unfold dualF
      rw [Complex.exp_add]
      ring
    have hS : ∑' m : ℤ, D.dualF a b m = ((chiZ (D.N * b) : ℂ) *
        cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc)) * ∑' m : ℤ, cexp (D.dualE a b m) := by
      rw [← tsum_mul_left]
      exact tsum_congr hF
    rw [hS, tsum_mul_left, D.tsum_latTerm]
    ring
  have h2 : ∀ m : ℤ, ∑' b : ℤ, D.dualF a b m =
      (chiZ D.N : ℂ) * (sqrt D.z * e24 (-3)) * D.pTerm a m := by
    intro m
    unfold dualF
    rw [D.tsum_b a m, mul_assoc, D.dual_inverted a m (hL m)]
    ring
  have hswap : ∑' b : ℤ, ∑' m : ℤ, D.dualF a b m = ∑' m : ℤ, ∑' b : ℤ, D.dualF a b m :=
    (Summable.tsum_comm (f := fun b m => D.dualF a b m) (D.summable_dualF a)).symm
  rw [tsum_congr h1, tsum_mul_left, hswap, tsum_congr h2, tsum_mul_left]
  ring

/-- `L ≠ 0` when `a ≠ 0`. -/
lemma L_ne (a m : ℤ) (ha : a ≠ 0) : D.L a m ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  unfold L at him hre
  simp at him hre
  have hv := D.hz
  have hNm : m = 0 := by
    rcases him with h1 | h1
    · rcases h1 with h1 | h1
      · exact absurd h1 D.hN
      · exact h1
    · exact absurd h1 hv.ne'
  rw [hNm] at h
  unfold L at h
  apply ha
  have h0 : ((a : ℤ) : ℂ) = 0 := by simpa using h
  exact_mod_cast h0

end KData

open Rademacher ModularForm MatrixGroups
open UpperHalfPlane hiding I

/-- The generating Poincaré seed `𝔾_g`. -/
def seed (ξ y : ℝ) (g : ℤ) (z σ : ℂ) : ℂ :=
  cexp (6 * g * y * σ / z.im - 3 * σ ^ 2 / (2 * π * z.im) - 6 * π * g ^ 2 * y ^ 2 / z.im) *
    chiTheta z (g * ξ + σ / (2 * π * I))

/-- The imaginary part under `γ`. -/
lemma mob_im (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((mob γ z).im : ℂ) = z.im / (lin γ z * conj (lin γ z)) := by
  have h := ModularGroup.im_smul_eq_div_normSq γ (⟨z, hz⟩ : ℍ)
  have hm := mob_eq γ (⟨z, hz⟩ : ℍ)
  have hmob : mob γ z = (((γ • (⟨z, hz⟩ : ℍ)) : ℍ) : ℂ) := hm
  rw [hmob, Complex.mul_conj]
  have hd : UpperHalfPlane.denom γ (⟨z, hz⟩ : ℍ) = lin γ z := by simp [UpperHalfPlane.denom, lin]
  rw [hd] at h
  have him : (((γ • (⟨z, hz⟩ : ℍ)) : ℍ) : ℂ).im = (γ • (⟨z, hz⟩ : ℍ) : ℍ).im := rfl
  rw [him, h]
  push_cast
  rfl

/-- **Each term `(a,m)` is a translate of the seed.** -/
theorem KData.pTerm_eq (D : KData) (γ : SL(2, ℤ)) (g a m : ℤ) (hg : g ≠ 0)
    (hc : (D.N : ℤ) * m = g * γ 1 0) (hd : a = -g * γ 1 1) :
    D.pTerm a m * η (mob γ D.z) = seed D.ξ D.y g (mob γ D.z) (D.σ / lin γ D.z) * η D.z := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have hj : lin γ D.z ≠ 0 := denom_ne_zero' γ D.hz
  have hjb : conj (lin γ D.z) ≠ 0 := by simpa using hj
  have hv := D.v_ne
  have hL : D.L a m = g * lin γ D.z := by
    have hcC : (D.N : ℂ) * m = g * γ 1 0 := by exact_mod_cast hc
    have hdC : (a : ℂ) = -g * γ 1 1 := by exact_mod_cast hd
    unfold KData.L lin
    rw [hcC, hdC]
    ring
  have hLb : D.Lb a m = g * conj (lin γ D.z) := by
    have hcC : (D.N : ℂ) * m = g * γ 1 0 := by exact_mod_cast hc
    have hdC : (a : ℂ) = -g * γ 1 1 := by exact_mod_cast hd
    unfold KData.Lb KData.zb lin
    rw [hcC, hdC]
    simp
    ring
  have hζ : D.ζ₀ a m / lin γ D.z = g * D.ξ + D.σ / lin γ D.z / (2 * π * I) := by
    unfold KData.ζ₀
    rw [hL]
    field_simp
  have hn : (D.N : ℂ) * m = g * γ 1 0 := by exact_mod_cast hc
  have hE : D.pE a m =
      (6 * g * D.y * (D.σ / lin γ D.z) / (mob γ D.z).im -
        3 * (D.σ / lin γ D.z) ^ 2 / (2 * π * (mob γ D.z).im) -
        6 * π * g ^ 2 * D.y ^ 2 / (mob γ D.z).im) +
      2 * π * I * (6 * (γ 1 0 : ℂ) * D.ζ₀ a m ^ 2 / lin γ D.z) := by
    rw [mob_im γ D.hz]
    unfold KData.pE
    rw [hL, hLb, hn]
    have hvz : ((D.z.im : ℝ) : ℂ) = D.v := rfl
    rw [hvz]
    field_simp
  have hlaw := thetaLaw γ D.z (D.ζ₀ a m) D.hz
  rw [hζ] at hlaw
  unfold KData.pTerm seed
  rw [hE, Complex.exp_add]
  linear_combination (-cexp (6 * g * D.y * (D.σ / lin γ D.z) / (mob γ D.z).im -
        3 * (D.σ / lin γ D.z) ^ 2 / (2 * π * (mob γ D.z).im) -
        6 * π * g ^ 2 * D.y ^ 2 / (mob γ D.z).im)) * hlaw

end

end RamanujanTau.ThetaLift
