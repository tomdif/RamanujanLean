/-
# The integrand on a Ford segment

For coprime `h/k` and any `h'` with `hh' ≡ −1 (mod k)`, on the segment `w = k + iu`:

  `f(τ_{h,k}(u)) τ'(u) = (ω_{h,k} e^{−2πinh/k}/k) · w^{−5/2} e^{aw + b/w} · F(e^{2πi(h'+iw)/k})`,

with `a = π/(12k)`, `b = (2π/k)(n − 1/24)`. The multiplier `ω_{h,k}` (`omega`) is canonical: it does not depend
on `h'`.
-/
import RamanujanTau.Rademacher.Pieces

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Filter Metric
open scoped Real Topology

noncomputable section

/-- the transformation property with multiplier `ω` at `h/k`. -/
def IsMult (h k : ℕ) (ω : ℂ) : Prop :=
  ‖ω‖ = 1 ∧ ∀ h' : ℤ, (k : ℤ) ∣ h * h' + 1 → ∀ z : ℂ, 0 < z.re →
    F (cexp (2 * π * I * ((h + I * z) / k))) =
      ω * sqrt z * cexp (π * (1 / z - z) / (12 * k)) * F (cexp (2 * π * I * ((h' + I / z) / k)))

lemma F_periodic {k : ℕ} (hk : 0 < k) (h₁ h₂ : ℤ) (hmod : (k : ℤ) ∣ h₁ - h₂) (w : ℂ) :
    F (cexp (2 * π * I * ((h₁ + w) / k))) = F (cexp (2 * π * I * ((h₂ + w) / k))) := by
  obtain ⟨m, hm⟩ := hmod
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  congr 1
  rw [show 2 * π * I * ((h₁ + w) / k) = 2 * π * I * ((h₂ + w) / k) + (m : ℂ) * (2 * π * I) by
    have : (h₁ : ℂ) = h₂ + k * m := by exact_mod_cast (by linarith : h₁ = h₂ + k * m)
    rw [this]; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma exists_mult {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) : ∃ ω : ℂ, IsMult h k ω := by
  -- an inverse of `−h` mod `k`
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ℤ, (k : ℤ) ∣ h * h₀ + 1 := by
    have : IsCoprime (h : ℤ) k := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨x, y, hxy⟩ := this
    exact ⟨-x, ⟨y, by linarith⟩⟩
  obtain ⟨ω, hω, hF⟩ := F_transform (h := h) (k := k) (h' := h₀) (by exact_mod_cast hk) hh₀
  refine ⟨ω, hω, fun h' hh' z hz => ?_⟩
  have hFz := hF z hz
  push_cast at hFz
  rw [hFz]
  congr 1
  have : (k : ℤ) ∣ h₀ - h' := by
    have h1 : (k : ℤ) ∣ (h : ℤ) * (h₀ - h') := by
      have := dvd_sub hh₀ hh'; rw [show (h : ℤ) * h₀ + 1 - (h * h' + 1) = h * (h₀ - h') by ring] at this
      exact this
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_comm]; exact_mod_cast hcop)).dvd_of_dvd_mul_left h1
  exact F_periodic hk h₀ h' this (I / z)

open Classical in
/-- **the canonical multiplier** `ω_{h,k}`. -/
def omega (h k : ℕ) : ℂ := if hx : ∃ ω : ℂ, IsMult h k ω then Classical.choose hx else 0

lemma omega_spec {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) : IsMult h k (omega h k) := by
  have hx := exists_mult hk hcop
  rw [omega, dif_pos hx]
  exact Classical.choose_spec hx

/-- **`A_k(n) = Σ_{h mod k, (h,k)=1} ω_{h,k} e^{−2πinh/k}`**. -/
def Ak (k n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k), omega h k * cexp (-(2 * π * I * n * h / k))

/-- `W(w) = w^{−5/2} e^{aw + b/w}`. -/
def Wf (k n : ℕ) (w : ℂ) : ℂ :=
  w ^ (-(5 / 2 : ℂ)) * cexp (π / (12 * k) * w + 2 * π / k * ((n : ℂ) - 1 / 24) / w)

/-- `q' = e^{2πi(h'+iw)/k}`. -/
def qp (h' : ℤ) (k : ℕ) (w : ℂ) : ℂ := cexp (2 * π * I * ((h' + I * w) / k))

lemma re_wk {k : ℕ} (u : ℝ) : ((k : ℂ) + u * I).re = k := by simp

lemma sqrt_inv_eq {w : ℂ} (hw : 0 < w.re) : sqrt (1 / w) = w ^ (-(2⁻¹ : ℂ)) := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have harg : w.arg ≠ π := by
    have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)); rw [abs_lt] at this
    intro h; rw [h] at this; linarith [Real.pi_pos]
  rw [sqrt, one_div, inv_cpow _ _ harg, cpow_neg]

lemma cpow_combine {w : ℂ} (hw0 : w ≠ 0) : w ^ (-(2⁻¹ : ℂ)) * (1 / w ^ 2) = w ^ (-(5 / 2 : ℂ)) := by
  rw [show (-(5 / 2 : ℂ)) = -(2⁻¹ : ℂ) + (-2 : ℂ) by norm_num, cpow_add _ _ hw0, cpow_neg w 2,
    show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, one_div]

/-- **the integrand on the segment**. -/
lemma integrand_eq {h k n : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) {h' : ℤ} (hh' : (k : ℤ) ∣ h * h' + 1)
    (u : ℝ) : fI n (τc h k u) * dτc k u =
      omega h k * cexp (-(2 * π * I * n * h / k)) / k * Wf k n ((k : ℂ) + u * I) *
        F (qp h' k ((k : ℂ) + u * I)) := by
  set w : ℂ := (k : ℂ) + u * I with hwdef
  have hw0 : w ≠ 0 := wk_ne hk u
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hwre : 0 < w.re := by rw [hwdef, re_wk]; exact hkr
  have hzre : 0 < (1 / w).re := by
    rw [one_div, inv_re]; exact div_pos hwre (Complex.normSq_pos.mpr hw0)
  obtain ⟨-, hF⟩ := omega_spec hk hcop
  have key := hF h' hh' (1 / w) hzre
  have hτ : τc h k u = (h + I * (1 / w)) / k := by rw [τc, ← hwdef]; ring
  have hIz : I / (1 / w) = I * w := by field_simp
  rw [hIz] at key
  unfold fI
  rw [hτ, key, sqrt_inv_eq hwre]
  unfold dτc Wf qp
  rw [← hwdef]
  have hexp : cexp (π * (1 / (1 / w) - 1 / w) / (12 * k)) * cexp (-(2 * π * I * n * ((h + I * (1 / w)) / k))) =
      cexp (-(2 * π * I * n * h / k)) * cexp (π / (12 * k) * w + 2 * π / k * ((n : ℂ) - 1 / 24) / w) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hc := cpow_combine hw0
  calc omega h k * w ^ (-(2⁻¹ : ℂ)) * cexp (π * (1 / (1 / w) - 1 / w) / (12 * k)) *
        F (cexp (2 * π * I * ((h' + I * w) / k))) * cexp (-(2 * π * I * n * ((h + I * (1 / w)) / k))) *
        (1 / (k * w ^ 2))
      = omega h k * (cexp (π * (1 / (1 / w) - 1 / w) / (12 * k)) *
          cexp (-(2 * π * I * n * ((h + I * (1 / w)) / k)))) * (w ^ (-(2⁻¹ : ℂ)) * (1 / w ^ 2)) / k *
          F (cexp (2 * π * I * ((h' + I * w) / k))) := by field_simp
    _ = _ := by rw [hexp, hc]; ring

end

end Rademacher
