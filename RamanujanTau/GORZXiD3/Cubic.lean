/-
# Real cubics with nonnegative discriminant are hyperbolic; the degree-3 Jensen polynomial

* **`hyperbolic_cubic`**: if `a > 0` and `Disc = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d² ≥ 0`, then
  `d + cX + bX² + aX³` has all its roots real (`Hyperbolic`, counted with multiplicity).
  Proof: a real root `r` exists (IVT); `P = (X − r)·Q` with `Q = aX² + (b+ar)X + (c+br+ar²)`, and
  `Disc(P) = Disc(Q)·Q(r)²` (an identity once `d = −(cr+br²+ar³)`).  If `Q(r) ≠ 0` this gives `Disc(Q) ≥ 0`; if
  `Q(r) = 0` then `Disc(Q) = (b+3ar)² ≥ 0`.  Either way `Q` is hyperbolic.
* **`jensen3_of_hot`**: for any real sequence `α` with `α(n+3) > 0`, the higher-order Turán inequality
  `4(α₁²−α₀α₂)(α₂²−α₁α₃) ≥ (α₁α₂−α₀α₃)²` (indices shifted by `n`) implies that
  `J^{3,n}_α = α₀ + 3α₁X + 3α₂X² + α₃X³` is hyperbolic.  Indeed `Disc(J^{3,n}_α) = 27 · HOT(α, n)`.
-/
import RamanujanTau.GORZXiEff.Turan2

set_option autoImplicit false

namespace GORZXiD3

open Real Set Polynomial JensenThreshold GORZXi

lemma hyperbolic_mul {p q : ℝ[X]} (hp : Hyperbolic p) (hq : Hyperbolic q) (hpq : p * q ≠ 0) :
    Hyperbolic (p * q) := by
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq0 : q ≠ 0 := right_ne_zero_of_mul hpq
  unfold Hyperbolic at *
  rw [roots_mul hpq, Multiset.card_add, natDegree_mul hp0 hq0, hp, hq]

lemma hyperbolic_X_sub_C (r : ℝ) : Hyperbolic (X - C r) := by
  unfold Hyperbolic; rw [roots_X_sub_C, natDegree_X_sub_C]; simp

/-- a real cubic with positive leading coefficient has a real root. -/
lemma cubic_has_root {a b c d : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, d + c * r + b * r ^ 2 + a * r ^ 3 = 0 := by
  set K := |b| + |c| + |d|
  set M := 1 + K / a
  have hK : 0 ≤ K := by positivity
  have hM1 : 1 ≤ M := by simp only [M]; have : 0 ≤ K / a := by positivity
                         linarith
  have haM : a * M = a + K := by simp only [M]; field_simp
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hbn := abs_nonneg b; have hcn := abs_nonneg c; have hdn := abs_nonneg d
  set f : ℝ → ℝ := fun x => d + c * x + b * x ^ 2 + a * x ^ 3
  have hf : Continuous f := by simp only [f]; fun_prop
  have hMpos : 0 < M := by linarith
  have hM0 : 0 < M ^ 2 := by positivity
  -- |d + c x + b x²| ≤ K M² for |x| ≤ M ... we only need it at x = ±M
  have up : 0 < f M := by
    have e1 : -(|d|) ≤ d := by linarith [neg_abs_le d]
    have e2 : -(|c| * M) ≤ c * M := by nlinarith [neg_abs_le c]
    have e3 : -(|b| * M ^ 2) ≤ b * M ^ 2 := by nlinarith [neg_abs_le b]
    have e4 : |d| ≤ |d| * M ^ 2 := by nlinarith
    have e5 : |c| * M ≤ |c| * M ^ 2 := by nlinarith
    have e6 : a * M ^ 3 = (a + K) * M ^ 2 := by rw [← haM]; ring
    simp only [f]; nlinarith
  have dn : f (-M) < 0 := by
    have e1 : d ≤ |d| := le_abs_self d
    have e2 : c * (-M) ≤ |c| * M := by nlinarith [neg_abs_le c, le_abs_self c]
    have e3 : b * (-M) ^ 2 ≤ |b| * M ^ 2 := by nlinarith [le_abs_self b]
    have e4 : |d| ≤ |d| * M ^ 2 := by nlinarith
    have e5 : |c| * M ≤ |c| * M ^ 2 := by nlinarith
    have e6 : a * (-M) ^ 3 = -((a + K) * M ^ 2) := by rw [← haM]; ring
    simp only [f]; nlinarith
  have hle : -M ≤ M := by linarith
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc hle hf.continuousOn ⟨dn.le, up.le⟩
  exact ⟨r, hr⟩

/-- **A real cubic `d + cX + bX² + aX³` with `a > 0` and nonnegative discriminant is hyperbolic.** -/
theorem hyperbolic_cubic {a b c d : ℝ} (ha : 0 < a)
    (hD : 0 ≤ 18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2) :
    Hyperbolic (C d + C c * X + C b * X ^ 2 + C a * X ^ 3) := by
  obtain ⟨r, hr⟩ := cubic_has_root (b := b) (c := c) (d := d) ha
  have hd : d = -(c * r + b * r ^ 2 + a * r ^ 3) := by linarith
  set b' := b + a * r
  set c' := c + b * r + a * r ^ 2
  have hfac : C d + C c * X + C b * X ^ 2 + C a * X ^ 3 =
      (X - C r) * (C c' + C b' * X + C a * X ^ 2) := by
    rw [hd]; simp only [b', c', map_add, map_mul, map_neg, map_pow]; ring
  -- discriminant identity
  set q := 3 * a * r ^ 2 + 2 * b * r + c
  have hid : 18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2 =
      (b' ^ 2 - 4 * a * c') * q ^ 2 := by
    rw [hd]; simp only [b', c', q]; ring
  have hQ : 4 * a * c' ≤ b' ^ 2 := by
    by_cases hq : q = 0
    · have hc : c = -(3 * a * r ^ 2 + 2 * b * r) := by simp only [q] at hq; linarith
      have : b' ^ 2 - 4 * a * c' = (b + 3 * a * r) ^ 2 := by
        simp only [b', c']; rw [hc]; ring
      nlinarith [sq_nonneg (b + 3 * a * r)]
    · have hq2 : 0 < q ^ 2 := by positivity
      rw [hid] at hD
      have := nonneg_of_mul_nonneg_left hD hq2
      linarith
  have hQh := GORZXiEff.hyperbolic_quadratic ha hQ
  rw [hfac]
  refine hyperbolic_mul (hyperbolic_X_sub_C r) hQh ?_
  refine mul_ne_zero (X_sub_C_ne_zero r) ?_
  intro h0
  have := congrArg (fun p => Polynomial.coeff p 2) h0
  simp at this
  exact ha.ne' this

lemma jensenSeq_three (α : ℕ → ℝ) (n : ℕ) :
    jensenSeq α 3 n = C (α n) + C (3 * α (n + 1)) * X + C (3 * α (n + 2)) * X ^ 2 +
      C (α (n + 3)) * X ^ 3 := by
  simp only [jensenSeq, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

/-- the higher-order Turán expression `4(α₁²−α₀α₂)(α₂²−α₁α₃) − (α₁α₂−α₀α₃)²` at shift `n`. -/
noncomputable def hot (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  4 * (α (n + 1) ^ 2 - α n * α (n + 2)) * (α (n + 2) ^ 2 - α (n + 1) * α (n + 3)) -
    (α (n + 1) * α (n + 2) - α n * α (n + 3)) ^ 2

/-- `Disc(J^{3,n}_α) = 27 · hot α n`. -/
lemma disc_jensen3 (α : ℕ → ℝ) (n : ℕ) :
    18 * α (n + 3) * (3 * α (n + 2)) * (3 * α (n + 1)) * α n - 4 * (3 * α (n + 2)) ^ 3 * α n +
      (3 * α (n + 2)) ^ 2 * (3 * α (n + 1)) ^ 2 - 4 * α (n + 3) * (3 * α (n + 1)) ^ 3 -
      27 * α (n + 3) ^ 2 * α n ^ 2 = 27 * hot α n := by
  unfold hot; ring

/-- **Higher-order Turán ⇒ `J^{3,n}_α` hyperbolic** (any real sequence with `α(n+3) > 0`). -/
theorem jensen3_of_hot {α : ℕ → ℝ} {n : ℕ} (hpos : 0 < α (n + 3)) (hH : 0 ≤ hot α n) :
    Hyperbolic (jensenSeq α 3 n) := by
  rw [jensenSeq_three]
  refine hyperbolic_cubic hpos ?_
  rw [disc_jensen3]; linarith

end GORZXiD3
