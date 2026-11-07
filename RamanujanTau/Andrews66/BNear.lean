/-
# Andrews 1966, M-a (second half): the multiplier of `b` at `h/2k`, `b(q') → 1`, and the hypothesis `Hb`

* `bE_near`: `‖b(q) − 1‖ ≤ C_b ‖q‖` for `‖q‖ ≤ 1/2` (`b − 1` is holomorphic on the disc and vanishes at `0`;
  `dslope` is continuous on the closed disc of radius `1/2`).
* `omegaB h k`: the canonical multiplier of `b` at the cusp `h/2k` (independent of the choice of `h'`), with
  `b(e^{2πi(h+iz)/2k}) = ω_b(h,k) z^{−1/2} e^{π(1/z−z)/(24k)} b(e^{2πi(h'+i/z)/2k})` for every `h'` with
  `hh' ≡ −1 (mod 2k)` (`omegaB_spec`).
* `Hb C D`: **the named hypothesis** (M-b): near every cusp `h/K`, in the region `Re(1/z) ≥ K/2` (the disc
  `|z − 1/K| ≤ 1/K`, i.e. twice the Ford disc), `‖f(q) − ε_K b(q)‖ ≤ C‖z‖^{−D}` where `q = e^{2πi(h+iz)/K}`,
  `ε_K = (−1)^{K/2}` for even `K` and `ε_K = 0` for odd `K`.
-/
import RamanujanTau.Andrews66.Cusps
import RamanujanTau.MockTheta3Radial
import RamanujanTau.HardyRamanujan.Bounds

set_option autoImplicit false

namespace Andrews66
open Complex Metric Filter
open scoped Real Topology

noncomputable section

lemma F_zero : HardyRamanujan.F 0 = 1 := by
  have h := HardyRamanujan.F_sub_one (w := 0) (by simp)
  rw [norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

lemma bE_zero : bE 0 = 1 := by simp [bE, F_zero]

lemma sq_mem_ball {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : q ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at *
  rw [norm_pow]
  nlinarith [norm_nonneg q]

lemma bE_diff : DifferentiableOn ℂ bE (ball 0 1) := by
  intro q hq
  have h1 : DifferentiableAt ℂ HardyRamanujan.F q :=
    HardyRamanujan.F_diff.differentiableAt (isOpen_ball.mem_nhds hq)
  have h2 : DifferentiableAt ℂ (fun q : ℂ => HardyRamanujan.F (q ^ 2)) q :=
    DifferentiableAt.comp (f := fun x : ℂ => x ^ 2) (g := HardyRamanujan.F) q
      (HardyRamanujan.F_diff.differentiableAt (isOpen_ball.mem_nhds (sq_mem_ball hq))) (differentiableAt_pow 2)
  have hne : HardyRamanujan.F q ^ 3 ≠ 0 := pow_ne_zero _ (Rademacher.F_ne_zero hq)
  exact ((h2.pow 2).div (h1.pow 3) hne).differentiableWithinAt

/-- **`b(q) = 1 + O(q)`** near `0`. -/
theorem bE_near : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℂ, ‖q‖ ≤ 1 / 2 → ‖bE q - 1‖ ≤ C * ‖q‖ := by
  set g : ℂ → ℂ := fun q => bE q - 1 with hgdef
  have hg : DifferentiableOn ℂ g (ball 0 1) := bE_diff.sub_const 1
  have hd : DifferentiableOn ℂ (dslope g 0) (ball 0 1) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr hg
  have hK : IsCompact (closedBall (0 : ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hd.continuousOn.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun q hq => ?_⟩
  have h0 : g 0 = 0 := by simp [hgdef, bE_zero]
  have e := sub_smul_dslope_of_zero h0 q
  rw [sub_zero, smul_eq_mul] at e
  rw [show bE q - 1 = g q from rfl, ← e, norm_mul, mul_comm]
  gcongr
  exact (hC q (mem_closedBall_zero_iff.mpr hq)).trans (le_max_left _ _)

/-! ### the canonical multiplier of `b` at `h/2k` -/

lemma qp_periodic {K : ℕ} (hK : 0 < K) (h₁ h₂ : ℤ) (hmod : (K : ℤ) ∣ h₁ - h₂) (w : ℂ) :
    Rademacher.qp h₁ K w = Rademacher.qp h₂ K w := by
  obtain ⟨m, hm⟩ := hmod
  have hk0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold Rademacher.qp
  rw [show 2 * π * I * ((h₁ + I * w) / K) = 2 * π * I * ((h₂ + I * w) / K) + (m : ℂ) * (2 * π * I) by
    have : (h₁ : ℂ) = h₂ + K * m := by exact_mod_cast (by linarith : h₁ = h₂ + K * m)
    rw [this]; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- the transformation of `b` at `h/2k` with multiplier `ω`. -/
def IsMultB (h k : ℕ) (ω : ℂ) : Prop :=
  ‖ω‖ = 1 ∧ ∀ h' : ℤ, ((2 * k : ℕ) : ℤ) ∣ h * h' + 1 → ∀ z : ℂ, 0 < z.re →
    bE (Rademacher.qp h (2 * k) z) =
      ω / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) * bE (Rademacher.qp h' (2 * k) (1 / z))

lemma exists_multB {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) : ∃ ω : ℂ, IsMultB h k ω := by
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ℤ, ((2 * k : ℕ) : ℤ) ∣ h * h₀ + 1 := by
    have : IsCoprime (h : ℤ) ((2 * k : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨x, y, hxy⟩ := this
    exact ⟨-x, ⟨y, by linarith⟩⟩
  obtain ⟨ω, hω, hb⟩ := b_transform_even (h := h) (h' := h₀) hk hh₀
  refine ⟨ω, hω, fun h' hh' z hz => ?_⟩
  rw [hb z hz]
  congr 2
  have : ((2 * k : ℕ) : ℤ) ∣ h₀ - h' := by
    have h1 : ((2 * k : ℕ) : ℤ) ∣ (h : ℤ) * (h₀ - h') := by
      have := dvd_sub hh₀ hh'
      rw [show (h : ℤ) * h₀ + 1 - (h * h' + 1) = h * (h₀ - h') by ring] at this
      exact this
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_comm]; exact_mod_cast hcop)).dvd_of_dvd_mul_left h1
  exact qp_periodic (by omega) h₀ h' this _

open Classical in
/-- **the canonical multiplier** `ω_b(h,k)` of `b` at the cusp `h/2k`. -/
def omegaB (h k : ℕ) : ℂ := if hx : ∃ ω : ℂ, IsMultB h k ω then Classical.choose hx else 0

lemma omegaB_spec {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) : IsMultB h k (omegaB h k) := by
  have hx := exists_multB hk hcop
  rw [omegaB, dif_pos hx]
  exact Classical.choose_spec hx

/-! ### the hypothesis `Hb` -/

/-- the sign `ε_K`: `(−1)^{K/2}` for even `K`, `0` for odd `K`. -/
def epsK (K : ℕ) : ℂ := if Even K then (-1) ^ (K / 2) else 0

/-- `f(q) = Σ q^{n²}/(−q;q)_n²` as a holomorphic function on the disc. -/
abbrev fA : ℂ → ℂ := MockTheta3.Radial.fA

/-- **the hypothesis `Hb` (milestone M-b)**: for every cusp `h/K` (`K ≥ 1`, `(h,K) = 1`) and every `z` with
`Re z > 0`, `Re(1/z) ≥ K/2`,
`‖f(e^{2πi(h+iz)/K}) − ε_K b(e^{2πi(h+iz)/K})‖ ≤ C ‖z‖^{−D}`. -/
def Hb (C D : ℝ) : Prop :=
  ∀ K : ℕ, 0 < K → ∀ h : ℕ, Nat.Coprime h K → ∀ z : ℂ, 0 < z.re → (K : ℝ) / 2 ≤ (1 / z).re →
    ‖fA (Rademacher.qp h K z) - epsK K * bE (Rademacher.qp h K z)‖ ≤ C * ‖z‖ ^ (-D)

end

end Andrews66
