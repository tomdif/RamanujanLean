import RamanujanTau.ThetaLift.StripValue

/-!
# The closed form of the integral over the strip

The integral in `v` vanishes unless `x` and `g` have the same sign. For `g > 0` and `x > 0` it is an
explicit exponential.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex Polynomial MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups

noncomputable section

/-- `vT` as `vTerm`, for `g > 0`. -/
lemma vT_eq_vTerm (lam : ℕ) {g : ℤ} (y v : ℝ) (x : ℤ) {ε : ℝ} (hxε : (x : ℝ) = ε * |(x : ℝ)|) :
    vT lam g y v x = vTerm lam ε g |(x : ℝ)| y v := by
  unfold vT vTerm rR
  rw [← hxε, sq_abs]

/-- **The integral in `v` for `g > 0`, `x > 0`.** -/
theorem W_pos (lam : ℕ) {g x : ℤ} (hg : 0 < g) (hx : 0 < x) {y : ℝ} (hy : 0 < y) :
    ∫ v in Ioi (0 : ℝ), vT lam g y v x =
      2 ^ lam * (6 * (g : ℝ)) ^ lam * y ^ lam *
        ((√6 * y * g)⁻¹ * Real.exp (-(2 * π * y * g * x))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have habs : |(x : ℝ)| = x := abs_of_pos hxR
  have h : ∀ v, vT lam g y v x = vTerm lam 1 g |(x : ℝ)| y v := fun v =>
    vT_eq_vTerm lam y v x (by rw [habs, one_mul])
  simp only [h]
  rw [vTerm_integral lam (Or.inl rfl) hgR (by rwa [habs]) hy, habs]
  norm_num

/-- **The integral in `v` vanishes for `g > 0`, `x < 0`.** -/
theorem W_neg (lam : ℕ) (hlam : lam ≠ 0) {g x : ℤ} (hg : 0 < g) (hx : x < 0) {y : ℝ} (hy : 0 < y) :
    ∫ v in Ioi (0 : ℝ), vT lam g y v x = 0 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hxR : (x : ℝ) < 0 := by exact_mod_cast hx
  have habs : |(x : ℝ)| = -x := abs_of_neg hxR
  have h : ∀ v, vT lam g y v x = vTerm lam (-1) g |(x : ℝ)| y v := fun v =>
    vT_eq_vTerm lam y v x (by rw [habs]; ring)
  simp only [h]
  rw [vTerm_integral lam (Or.inr rfl) hgR (by rw [habs]; linarith) hy]
  simp [hlam]

/-- The symmetry under `(g,x) ↦ (-g,-x)`. -/
lemma vT_neg (lam : ℕ) (g : ℤ) (y v : ℝ) (x : ℤ) :
    vT lam (-g) y v (-x) = (-1) ^ lam * vT lam g y v x := by
  unfold vT rR
  have e : (((-x : ℤ) : ℝ) + 6 * ((-g : ℤ) : ℝ) * y / v) / √(3 / (π * v)) =
      -(((x : ℝ) + 6 * g * y / v) / √(3 / (π * v))) := by
    push_cast
    ring
  rw [e, ev_hermite_neg]
  push_cast
  rw [neg_sq, neg_sq]
  ring

lemma W_neg_neg (lam : ℕ) (g : ℤ) (y : ℝ) (x : ℤ) :
    ∫ v in Ioi (0 : ℝ), vT lam (-g) y v (-x) =
      (-1) ^ lam * ∫ v in Ioi (0 : ℝ), vT lam g y v x := by
  simp only [vT_neg]
  exact integral_const_mul _ _

lemma chiZ_neg (x : ℤ) : chiZ (-x) = chiZ x := by
  have h0 := Int.emod_nonneg x (by norm_num : (12 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 12)
  have h2 : (-x) % 12 = (12 - x % 12) % 12 := by omega
  unfold chiZ
  rw [h2]
  generalize x % 12 = r at *
  interval_cases r <;> norm_num

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N) (lam : ℕ) (ξ y : ℝ)

lemma cX_neg (x : ℤ) : cX G j N (-x) = cX G j N x := by
  classical
  have key : ∀ s s' : ℤ, s = s' →
      (if h : ∃ m : ℕ, s = (N : ℤ) * (24 * m - j) then conj (cA G j h.choose) else 0) =
        (if h : ∃ m : ℕ, s' = (N : ℤ) * (24 * m - j) then conj (cA G j h.choose) else 0) := by
    rintro _ _ rfl
    rfl
  unfold cX
  convert key _ _ (neg_sq x)

lemma cf_neg (g x : ℤ) : cf G j ξ (-g) (-x) (N := N) = cf G j ξ g x (N := N) := by
  unfold cf
  rw [chiZ_neg, cX_neg]
  push_cast
  congr 3
  ring

/-- The term of the double sum, at `w = ξ + iy`. -/
def lTerm (ξ y : ℝ) (g x : ℤ) : ℂ :=
  (chiZ x : ℂ) * (cX G j N x * cexp (2 * π * I * x * g * ((ξ : ℂ) + y * I)))

/-- The constant of the integral in `v`. -/
def cV (lam : ℕ) (y : ℝ) (g : ℤ) : ℝ :=
  2 ^ lam * (6 * (g : ℝ)) ^ lam * y ^ lam * (√6 * y * g)⁻¹

lemma cf_W (g x : ℤ) (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    cf G j ξ g x (N := N) * ((∫ v in Ioi (0 : ℝ), vT lam g y v x : ℝ) : ℂ) =
      (cV lam y g : ℂ) * lTerm G j (N := N) ξ y g x := by
  rw [W_pos lam hg hx hy]
  unfold cf lTerm cV
  have e : cexp (2 * π * I * x * g * ((ξ : ℂ) + y * I)) =
      cexp (2 * π * I * (x * (g * ξ))) * ((Real.exp (-(2 * π * y * g * x)) : ℝ) : ℂ) := by
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * (π : ℂ) * x * g * y) * Complex.I_sq
  rw [e]
  push_cast
  ring

/-- **The strip integral for `g > 0`, as a sum over `x > 0`.** -/
theorem hasSum_J (hlam : lam ≠ 0) {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (hy : 0 < y) {g : ℤ}
    (hg : 0 < g) :
    HasSum (fun n : ℕ => (cV lam y g : ℂ) * lTerm G j (N := N) ξ y g ((n : ℤ) + 1))
      (∫ z in stripSet, Hg G j hN lam ξ y g z) := by
  have h := strip_value G j hN lam ξ y (hj := hj) hNj hy hg.ne'
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b hab
    simpa using hab
  have hzero : ∀ x ∉ Set.range (fun n : ℕ => (n : ℤ) + 1),
      cf G j ξ g x (N := N) * ((∫ v in Ioi (0 : ℝ), vT lam g y v x : ℝ) : ℂ) = 0 := by
    intro x hx
    have hxle : x ≤ 0 := by
      by_contra hc
      exact hx ⟨(x - 1).toNat, by simp only; omega⟩
    rcases hxle.lt_or_eq with hlt | rfl
    · rw [W_neg lam hlam hg hlt hy]
      simp
    · simp [cf, chiZ]
  have h2 := (hinj.hasSum_iff hzero).mpr h
  convert h2 using 1
  funext n
  simp only [Function.comp]
  exact (cf_W G j lam ξ y g ((n : ℤ) + 1) hg (by omega) hy).symm

/-- **The symmetry of the strip integral.** -/
theorem J_neg (hlam : lam ≠ 0) {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (hy : 0 < y) {g : ℤ}
    (hg : g ≠ 0) :
    ∫ z in stripSet, Hg G j hN lam ξ y (-g) z =
      (-1) ^ lam * ∫ z in stripSet, Hg G j hN lam ξ y g z := by
  have h1 := strip_value G j hN lam ξ y (hj := hj) hNj hy (neg_ne_zero.mpr hg)
  have h2 := strip_value G j hN lam ξ y (hj := hj) hNj hy hg
  have h3 := ((Equiv.neg ℤ).hasSum_iff).mpr h1
  have h4 := h2.mul_left (((-1) ^ lam : ℝ) : ℂ)
  refine h3.unique ?_
  convert h4 using 1
  · funext x
    simp only [Function.comp, Equiv.neg_apply]
    rw [cf_neg, W_neg_neg]
    push_cast
    ring
  · push_cast
    rfl

/-- The double sum at `w = ξ + iy`. -/
def lamSum (ψ : ℤ → ℂ) (lam : ℕ) (ξ y : ℝ) : ℂ :=
  ∑' n : ℕ, ψ ((n : ℤ) + 1) * (((n : ℂ) + 1) ^ (lam - 1) *
    ∑' m : ℕ, lTerm G j (N := N) ξ y ((n : ℤ) + 1) ((m : ℤ) + 1))

/-- The constant of the closed form. -/
def c0 (lam : ℕ) : ℝ := 12 ^ lam / √6

lemma cV_eq (hlam : lam ≠ 0) (hy : 0 < y) {g : ℤ} (hg : 0 < g) :
    cV lam y g = c0 lam * (y ^ lam * y⁻¹) * (g : ℝ) ^ (lam - 1) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpow : (g : ℝ) ^ lam = (g : ℝ) ^ (lam - 1) * g := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hlam)]
  have h6 : (0 : ℝ) < √6 := Real.sqrt_pos.mpr (by norm_num)
  unfold cV c0
  rw [mul_pow, hpow, show (12 : ℝ) ^ lam = 2 ^ lam * 6 ^ lam by rw [← mul_pow]; norm_num]
  field_simp

/-- **The closed form of the integral over the strip.** -/
theorem strip_closed (hlam : lam ≠ 0) {hj : j < 24} (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1) (hy : 0 < y)
    {ψ : ℤ → ℂ} (h1 : ∀ g, ‖ψ g‖ ≤ 1) (hneg : ∀ g, ψ (-g) = (-1) ^ lam * ψ g) :
    ∫ z in stripSet, fTot G j hN lam ξ y (fun g => if g = 0 then 0 else ψ (-g)) z =
      2 * (-1) ^ lam * ((c0 lam * (y ^ lam * y⁻¹) : ℝ) : ℂ) * lamSum G j (N := N) ψ lam ξ y := by
  set ψg : ℤ → ℂ := fun g => if g = 0 then 0 else ψ (-g) with hψg
  have hg1 : ∀ g, ‖ψg g‖ ≤ 1 := by
    intro g
    simp only [hψg]
    split_ifs
    · simp
    · exact h1 _
  have hg0 : ψg 0 = 0 := by simp [hψg]
  obtain ⟨-, -, hsum⟩ := strip_total G j hN lam ξ y (hj := hj) hy hg1 hg0
  set F : ℤ → ℂ := fun g => ψg g * ∫ z in stripSet, Hg G j hN lam ξ y g z with hF
  have hS : Summable F := hsum.summable
  have hF0 : F 0 = 0 := by simp [hF, hg0]
  have hFneg : ∀ g : ℤ, g ≠ 0 → F (-g) = F g := by
    intro g hg
    have hne : -g ≠ 0 := neg_ne_zero.mpr hg
    simp only [hF, hψg, if_neg hne, if_neg hg, neg_neg]
    rw [J_neg G j hN lam ξ y hlam (hj := hj) hNj hy hg, hneg g]
    ring
  have hpos : Summable fun n : ℕ => F ((n : ℤ) + 1) := by
    refine hS.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) ?_
    intro a b hab
    simpa using hab
  have hnegS : Summable fun n : ℕ => F (-((n : ℤ) + 1)) := by
    refine hpos.congr fun n => ?_
    exact (hFneg _ (by omega)).symm
  have htot := HasSum.of_add_one_of_neg_add_one hpos.hasSum hnegS.hasSum
  have hT := hsum.unique htot
  have hnegval : ∑' n : ℕ, F (-((n : ℤ) + 1)) = ∑' n : ℕ, F ((n : ℤ) + 1) :=
    tsum_congr fun n => hFneg _ (by omega)
  have hval : ∀ n : ℕ, F ((n : ℤ) + 1) = ((-1) ^ lam * ((c0 lam * (y ^ lam * y⁻¹) : ℝ) : ℂ)) *
      (ψ ((n : ℤ) + 1) * (((n : ℂ) + 1) ^ (lam - 1) *
        ∑' m : ℕ, lTerm G j (N := N) ξ y ((n : ℤ) + 1) ((m : ℤ) + 1))) := by
    intro n
    have hgpos : (0 : ℤ) < (n : ℤ) + 1 := by omega
    have hJ := (hasSum_J G j hN lam ξ y hlam (hj := hj) hNj hy hgpos).tsum_eq
    rw [tsum_mul_left] at hJ
    have hne : ((n : ℤ) + 1) ≠ 0 := by omega
    simp only [hF, hψg, if_neg hne]
    rw [← hJ, hneg, cV_eq lam y hlam hy hgpos]
    push_cast
    ring
  rw [hT, hF0, add_zero, hnegval, tsum_congr hval, tsum_mul_left]
  unfold lamSum
  ring

end

end RamanujanTau.ThetaLift
