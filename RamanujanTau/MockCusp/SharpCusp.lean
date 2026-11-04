/-
# The sharp key lemma at the optimal shift, and the sum over the residue classes

`al_sum_cusp'`: `al_sum_le'` at `Y₀ = π Re(1/α)/(2TA)` with a *per-class* separation `δ(ρ)` of the phases
`θ(ρ)` from `2πℤ`; the class `ρ` contributes `Jb(min(1, |α|Re(1/α)(δ(ρ) − πD/(2TA)))/3)`.

`sumJb_le`: if `W = √(π/(A Re α)) ≤ 1/Z`, `Z ≤ 2`, `16|α|²D²/(π²A Re α) ≤ N₁`, `Z² ≤ c₁|α|`, `Z² ≤ c₂ Re α`
and `Σ_ρ g(ρ)^{−1/2} ≤ G₀ T`, then

  `Σ_{ρ<T} Jb(min(1, |α|Re(1/α) g(ρ))/3) ≤ (6√2 + 2√(18(1+N₁)c₁/D) + 2√(18(1+N₁)c₂/D) G₀) / (Z√Z)`.

This is the `Z^{−3/2}` that replaces the `Z^{−2}` of `al_sum_cusp`.

`class_phase_sum`: if `g(ρ) ≥ c·min(r(ρ), M − r(ρ))` with `ρ ↦ r(ρ) ∈ [1, M)` injective on `[0, T)`, then
`Σ_{ρ<T} g(ρ)^{−1/2} ≤ 4√(M/c)`.
-/
import RamanujanTau.MockCusp.SharpALSum
import RamanujanTau.MockCusp.GenCusp

set_option autoImplicit false

namespace MockCusp
open Complex Filter MeasureTheory Set
open scoped Topology Real

noncomputable section

/-- **the sharp key lemma at the optimal shift**. -/
theorem al_sum_cusp' {α : ℂ} (hα : 0 < α.re) {A B D E : ℝ} (hA : 0 < A) (hD : 0 < D) {T : ℕ} (hT : 0 < T)
    {c : ℤ → ℂ} (hc : ∀ n, c (n + T) = -c n) (hc1 : ∀ n, ‖c n‖ ≤ 1)
    {θ δ : ℤ → ℝ} (hθp : ∀ n, θ (n + T) = θ n) (hθ : ∀ n : ℤ, ∀ k : ℤ, δ n ≤ |θ n - 2 * π * k|)
    (hgap : ∀ n, π * D / (2 * T * A) < δ n) :
    Summable (alTerm α A B D E c (fun n => cexp (I * θ n))) ∧
    ‖∑' n, alTerm α A B D E c (fun n => cexp (I * θ n)) n‖ ≤
      Real.exp (π ^ 2 * (1 / α).re / (4 * A * T ^ 2) + B ^ 2 * α.re / (4 * A)) *
        (∑ ρ ∈ Finset.range T, Jb α A D T (min 1 (‖α‖ * ((1 / α).re * (δ ρ - π * D / (2 * T * A)))) / 3)) *
        (1 / Real.sinh (π ^ 2 * (1 / α).re / (2 * A * T ^ 2))) := by
  have hR := re_inv_pos' hα
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set Y0 := π * (1 / α).re / (2 * T * A)
  have hY0 : 0 < Y0 := by positivity
  have hDY : D * Y0 = (1 / α).re * (π * D / (2 * T * A)) := by simp only [Y0]; ring
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr fun h => by rw [h] at hα; simp at hα
  set m : ℤ → ℝ := fun n => min 1 (‖α‖ * ((1 / α).re * (δ n - π * D / (2 * T * A)))) / 3
  have hm : ∀ n, 0 < m n := fun n => by
    have : 0 < δ n - π * D / (2 * T * A) := by linarith [hgap n]
    have : 0 < min 1 (‖α‖ * ((1 / α).re * (δ n - π * D / (2 * T * A)))) := lt_min one_pos (by positivity)
    simp only [m]; positivity
  have hden : ∀ n : ℤ, ∀ x y : ℝ, |y| ≤ Y0 →
      m n ≤ ‖1 - (fun n => cexp (I * θ n)) n * cexp (-(α * (D * ((x : ℂ) + y * I) + E)))‖ := by
    intro n x y hy
    have := den_lower (E := E) hα hD (hθ n) x y hy
    simp only [m]
    convert this using 3
    rw [mul_sub, ← hDY]
  have hω : ∀ n, (fun n => cexp (I * θ n)) (n + T) = (fun n => cexp (I * θ n)) n := fun n => by
    simp only [hθp]
  obtain ⟨hs, hb⟩ := al_sum_le' (B := B) (E := E) hα hA hD hT hc hc1 hω (fun n => Complex.exp_ne_zero _)
    hm hY0 hden
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  have hn2 : α.re ^ 2 + α.im ^ 2 = α.re / (1 / α).re := by
    rw [one_div, inv_re, normSq_apply]
    have : α.re * α.re + α.im * α.im ≠ 0 := by
      have := normSq_pos.mpr (fun h : α = 0 => by rw [h] at hα; simp at hα)
      rw [normSq_apply] at this; linarith
    field_simp
  have hRr : (1 / α).re ≠ 0 := hR.ne'
  have e1 : A * Y0 ^ 2 * (α.re ^ 2 + α.im ^ 2) / α.re = π ^ 2 * (1 / α).re / (4 * A * T ^ 2) := by
    rw [hn2]; simp only [Y0]; field_simp; ring
  have e2 : π * Y0 / T = π ^ 2 * (1 / α).re / (2 * A * T ^ 2) := by
    simp only [Y0]; field_simp
  rw [e1, e2]

/-! ### `Jb` in closed form -/

lemma inv_sqrt_min_le {X : ℝ} (hX : 0 < X) : 1 / √(min 1 X) ≤ 1 + 1 / √X := by
  rcases le_total 1 X with h | h
  · rw [min_eq_left h, Real.sqrt_one, div_one]; have : 0 ≤ 1 / √X := by positivity
    linarith
  · rw [min_eq_right h]; have : (0 : ℝ) ≤ 1 := zero_le_one; linarith

/-- `Jb(min(1,X)/3) ≤ (6W + 2√(18NW/(|α|D))(1 + X^{−1/2}))/T`. -/
lemma Jb_le {α : ℂ} (hα : 0 < α.re) {A D : ℝ} (hA : 0 < A) (hD : 0 < D) {T : ℕ} (hT : 0 < T) {X : ℝ}
    (hX : 0 < X) :
    Jb α A D T (min 1 X / 3) ≤
      (6 * √(π / (A * α.re)) + 2 * √(18 * (1 + 16 * ‖α‖ ^ 2 * D ^ 2 / (π ^ 2 * A * α.re)) *
        √(π / (A * α.re)) / (‖α‖ * D)) * (1 + 1 / √X)) / T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr fun h => by rw [h] at hα; simp at hα
  set W := √(π / (A * α.re))
  set N := 1 + 16 * ‖α‖ ^ 2 * D ^ 2 / (π ^ 2 * A * α.re)
  have hW : 0 < W := Real.sqrt_pos.mpr (by positivity)
  have hN : 0 < N := by positivity
  have hmin : 0 < min 1 X := lt_min one_pos hX
  have hWT : √(π / (A * α.re * T ^ 2)) = W / T := by
    rw [show π / (A * α.re * T ^ 2) = (π / (A * α.re)) / T ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hT'.le]
  have hNe : 1 + 16 * (‖α‖ * D * T) ^ 2 / (π ^ 2 * (A * α.re * T ^ 2)) = N := by
    simp only [N]; field_simp
  unfold Jb
  rw [hWT, hNe]
  have hin : 3 * (W / T) * (1 / (min 1 X / 3) * (2 / (‖α‖ * D * T) * N)) =
      (18 * N * W / (‖α‖ * D)) * (1 / min 1 X) / T ^ 2 := by field_simp; ring
  rw [hin, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hT'.le, Real.sqrt_mul (by positivity),
    Real.sqrt_div' _ hmin.le, Real.sqrt_one]
  have hk := inv_sqrt_min_le hX
  have h0 : 0 ≤ √(18 * N * W / (‖α‖ * D)) := Real.sqrt_nonneg _
  rw [show 2 * (3 * (W / ↑T)) + 2 * (√(18 * N * W / (‖α‖ * D)) * (1 / √(min 1 X)) / ↑T) =
    (6 * W + 2 * (√(18 * N * W / (‖α‖ * D)) * (1 / √(min 1 X)))) / T by ring]
  apply div_le_div_of_nonneg_right _ hT'.le
  nlinarith [mul_le_mul_of_nonneg_left hk h0]

/-- **the sum of `Jb` over the classes is `O(Z^{−3/2})`.** -/
theorem sumJb_le {α : ℂ} (hα : 0 < α.re) {A D : ℝ} (hA : 0 < A) (hD : 0 < D) {T : ℕ} (hT : 0 < T)
    {g : ℕ → ℝ} (hg : ∀ ρ, 0 < g ρ) {Z N₁ c₁ c₂ G₀ : ℝ} (hZ : 0 < Z) (hZ2 : Z ≤ 2)
    (hW : √(π / (A * α.re)) ≤ 1 / Z) (hN : 16 * ‖α‖ ^ 2 * D ^ 2 / (π ^ 2 * A * α.re) ≤ N₁)
    (h1 : Z ^ 2 ≤ c₁ * ‖α‖) (h2 : Z ^ 2 ≤ c₂ * α.re) (hG : ∑ ρ ∈ Finset.range T, 1 / √(g ρ) ≤ G₀ * T) :
    ∑ ρ ∈ Finset.range T, Jb α A D T (min 1 (‖α‖ * ((1 / α).re * g ρ)) / 3) ≤
      (6 * √2 + 2 * √(18 * (1 + N₁) * c₁ / D) + 2 * √(18 * (1 + N₁) * c₂ / D) * G₀) / (Z * √Z) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr fun h => by rw [h] at hα; simp at hα
  have hR := re_inv_pos' hα
  set W := √(π / (A * α.re))
  set N := 1 + 16 * ‖α‖ ^ 2 * D ^ 2 / (π ^ 2 * A * α.re)
  have hW0 : 0 < W := Real.sqrt_pos.mpr (by positivity)
  have hN0 : 0 < N := by positivity
  have hNN : N ≤ 1 + N₁ := by simp only [N]; linarith
  have hN₁ : 0 ≤ N₁ := le_trans (by positivity) hN
  have hsZ : 0 < √Z := Real.sqrt_pos.mpr hZ
  have hZZ : √Z * √Z = Z := Real.mul_self_sqrt hZ.le
  have hc₁ : 0 < c₁ := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hαn.le, sq_pos_of_pos hZ]
  have hc₂ : 0 < c₂ := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hα.le, sq_pos_of_pos hZ]
  have hX : ∀ ρ, 0 < ‖α‖ * ((1 / α).re * g ρ) := fun ρ => by have := hg ρ; positivity
  -- ‖α‖² Re(1/α) = Re α
  have hαR : ‖α‖ ^ 2 * (1 / α).re = α.re := by
    rw [one_div, inv_re, Complex.normSq_eq_norm_sq]; field_simp
  -- each class
  set Q := √(18 * N * W / (‖α‖ * D))
  have hb : ∀ ρ ∈ Finset.range T, Jb α A D T (min 1 (‖α‖ * ((1 / α).re * g ρ)) / 3) ≤
      (6 * W + 2 * Q + 2 * Q * (1 / √(‖α‖ * ((1 / α).re * g ρ)))) / T := by
    intro ρ _
    refine (Jb_le hα hA hD hT (hX ρ)).trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the three pieces
  have hWZ : W * Z ≤ 1 := by rw [le_div_iff₀ hZ] at hW; exact hW
  have hQ : Q ≤ √(18 * (1 + N₁) * c₁ / D) / (Z * √Z) := by
    have hle : 18 * N * W / (‖α‖ * D) ≤ (18 * (1 + N₁) * c₁ / D) / (Z * √Z) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hZ.le, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 18 * N * W * (D * (Z ^ 2 * Z)) ≤ 18 * (1 + N₁) * D * (c₁ * ‖α‖) := by
        have e : 18 * N * W * (D * (Z ^ 2 * Z)) = 18 * N * D * (W * Z) * Z ^ 2 := by ring
        rw [e]
        calc 18 * N * D * (W * Z) * Z ^ 2 ≤ 18 * N * D * 1 * Z ^ 2 := by gcongr
          _ ≤ 18 * (1 + N₁) * D * 1 * (c₁ * ‖α‖) := by gcongr
          _ = _ := by ring
      linarith [this, show 18 * (1 + N₁) * D * (c₁ * ‖α‖) = 18 * (1 + N₁) * c₁ * (‖α‖ * D) by ring]
    calc Q ≤ √((18 * (1 + N₁) * c₁ / D) / (Z * √Z) ^ 2) := Real.sqrt_le_sqrt hle
      _ = _ := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have hQρ : ∀ ρ, Q * (1 / √(‖α‖ * ((1 / α).re * g ρ))) ≤
      √(18 * (1 + N₁) * c₂ / D) / (Z * √Z) * (1 / √(g ρ)) := by
    intro ρ
    have hgρ := hg ρ
    have key : 18 * N * W / (‖α‖ * D) / (‖α‖ * ((1 / α).re * g ρ)) ≤
        (18 * (1 + N₁) * c₂ / D) / (Z * √Z) ^ 2 / g ρ := by
      have e : 18 * N * W / (‖α‖ * D) / (‖α‖ * ((1 / α).re * g ρ)) = 18 * N * W / (α.re * D * g ρ) := by
        rw [← hαR]; field_simp
      rw [e, mul_pow, Real.sq_sqrt hZ.le, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have e2 : 18 * N * W * (D * (Z ^ 2 * Z * g ρ)) = 18 * N * D * g ρ * (W * Z) * Z ^ 2 := by ring
      rw [e2]
      calc 18 * N * D * g ρ * (W * Z) * Z ^ 2 ≤ 18 * N * D * g ρ * 1 * (c₂ * α.re) := by gcongr
        _ ≤ 18 * (1 + N₁) * D * g ρ * 1 * (c₂ * α.re) := by gcongr
        _ = _ := by ring
    calc Q * (1 / √(‖α‖ * ((1 / α).re * g ρ))) = √(18 * N * W / (‖α‖ * D) / (‖α‖ * ((1 / α).re * g ρ))) := by
          rw [Real.sqrt_div' _ (hX ρ).le]; ring
      _ ≤ √((18 * (1 + N₁) * c₂ / D) / (Z * √Z) ^ 2 / g ρ) := Real.sqrt_le_sqrt key
      _ = _ := by
          rw [Real.sqrt_div' _ hgρ.le, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]; ring
  have hS : ∑ ρ ∈ Finset.range T, 2 * Q * (1 / √(‖α‖ * ((1 / α).re * g ρ))) ≤
      2 * (√(18 * (1 + N₁) * c₂ / D) / (Z * √Z)) * (G₀ * T) := by
    rw [← Finset.mul_sum, mul_assoc, mul_assoc]
    gcongr 2 * ?_
    rw [Finset.mul_sum]
    calc ∑ ρ ∈ Finset.range T, Q * (1 / √(‖α‖ * ((1 / α).re * g ρ)))
        ≤ ∑ ρ ∈ Finset.range T, √(18 * (1 + N₁) * c₂ / D) / (Z * √Z) * (1 / √(g ρ)) :=
          Finset.sum_le_sum fun ρ _ => hQρ ρ
      _ = √(18 * (1 + N₁) * c₂ / D) / (Z * √Z) * ∑ ρ ∈ Finset.range T, 1 / √(g ρ) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hWs : W ≤ √2 / (Z * √Z) := by
    rw [le_div_iff₀ (by positivity)]
    have : √Z ≤ √2 := Real.sqrt_le_sqrt hZ2
    nlinarith
  rw [div_le_iff₀ hT']
  have e3 : (6 * √2 + 2 * √(18 * (1 + N₁) * c₁ / D) + 2 * √(18 * (1 + N₁) * c₂ / D) * G₀) / (Z * √Z) * T =
      T * (6 * (√2 / (Z * √Z)) + 2 * (√(18 * (1 + N₁) * c₁ / D) / (Z * √Z))) +
        2 * (√(18 * (1 + N₁) * c₂ / D) / (Z * √Z)) * (G₀ * T) := by ring
  rw [e3]
  have h6 : (T : ℝ) * (6 * W + 2 * Q) ≤ T * (6 * (√2 / (Z * √Z)) + 2 * (√(18 * (1 + N₁) * c₁ / D) / (Z * √Z))) := by
    gcongr
  linarith

/-! ### the harmonic sum over the classes -/

lemma sum_inv_sqrt_le (M : ℕ) : ∑ j ∈ Finset.Icc 1 M, 1 / √(j : ℝ) ≤ 2 * √(M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set u := √((M : ℝ) + 1)
    set v := √(M : ℝ)
    have hu : 0 < u := Real.sqrt_pos.mpr (by positivity)
    have hv : 0 ≤ v := Real.sqrt_nonneg _
    have huv : u ^ 2 = v ^ 2 + 1 := by
      simp only [u, v]; rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hk : 1 / u ≤ 2 * (u - v) := by
      rw [div_le_iff₀ hu]; nlinarith [sq_nonneg (u - v)]
    push_cast at ih ⊢
    linarith

lemma sum_inj_le {T M : ℕ} (s : ℕ → ℕ) (hs : ∀ ρ < T, s ρ ∈ Finset.Icc 1 M)
    (hinj : ∀ ρ < T, ∀ ρ' < T, s ρ = s ρ' → ρ = ρ') :
    ∑ ρ ∈ Finset.range T, 1 / √((s ρ : ℕ) : ℝ) ≤ 2 * √(M : ℝ) := by
  have hinj' : Set.InjOn s (Finset.range T : Set ℕ) := fun a ha b hb h =>
    hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) h
  rw [← Finset.sum_image (f := fun j : ℕ => 1 / √(j : ℝ)) hinj']
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity) (sum_inv_sqrt_le M)
  intro j hj
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
  exact hs ρ (Finset.mem_range.mp hρ)

/-- **the phase sum**: `Σ_ρ g(ρ)^{−1/2} ≤ 4√(M/c)` for `g(ρ) ≥ c·min(r(ρ), M − r(ρ))`, `r` injective. -/
theorem class_phase_sum {T M : ℕ} {c : ℝ} (hc : 0 < c) (r : ℕ → ℕ) (hr1 : ∀ ρ < T, 1 ≤ r ρ)
    (hrM : ∀ ρ < T, r ρ < M) (hinj : ∀ ρ < T, ∀ ρ' < T, r ρ = r ρ' → ρ = ρ') (g : ℕ → ℝ)
    (hg : ∀ ρ < T, c * min (r ρ : ℝ) ((M : ℝ) - r ρ) ≤ g ρ) :
    ∑ ρ ∈ Finset.range T, 1 / √(g ρ) ≤ 4 * √(M : ℝ) / √c := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hpt : ∀ ρ ∈ Finset.range T, 1 / √(g ρ) ≤
      (1 / √((r ρ : ℕ) : ℝ) + 1 / √(((M - r ρ : ℕ) : ℕ) : ℝ)) / √c := by
    intro ρ hρ
    have hρT := Finset.mem_range.mp hρ
    have h1 : (1 : ℝ) ≤ r ρ := by exact_mod_cast hr1 ρ hρT
    have hMr : ((M - r ρ : ℕ) : ℝ) = (M : ℝ) - r ρ := by
      rw [Nat.cast_sub (hrM ρ hρT).le]
    have h2 : (1 : ℝ) ≤ (M : ℝ) - r ρ := by
      have : r ρ + 1 ≤ M := hrM ρ hρT
      have : ((r ρ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      push_cast at this; linarith
    rw [hMr]
    set mn := min (r ρ : ℝ) ((M : ℝ) - r ρ)
    have hmn : 1 ≤ mn := le_min h1 h2
    have hgρ : c * mn ≤ g ρ := hg ρ hρT
    have hsm : 0 < √mn := Real.sqrt_pos.mpr (by linarith)
    have step1 : 1 / √(g ρ) ≤ 1 / (√c * √mn) := by
      rw [← Real.sqrt_mul hc.le]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hgρ)
    have step2 : 1 / √mn ≤ 1 / √(r ρ : ℝ) + 1 / √((M : ℝ) - r ρ) := by
      rcases min_choice (r ρ : ℝ) ((M : ℝ) - r ρ) with h | h
      · rw [show mn = (r ρ : ℝ) from h]
        have : 0 ≤ 1 / √((M : ℝ) - r ρ) := by positivity
        linarith
      · rw [show mn = (M : ℝ) - r ρ from h]
        have : 0 ≤ 1 / √(r ρ : ℝ) := by positivity
        linarith
    calc 1 / √(g ρ) ≤ 1 / (√c * √mn) := step1
      _ = (1 / √mn) / √c := by field_simp
      _ ≤ _ := by gcongr
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hA := sum_inj_le (T := T) (M := M) r (fun ρ hρ => Finset.mem_Icc.mpr ⟨hr1 ρ hρ, (hrM ρ hρ).le⟩) hinj
  have hB := sum_inj_le (T := T) (M := M) (fun ρ => M - r ρ)
    (fun ρ hρ => by have := hrM ρ hρ; have := hr1 ρ hρ; simp only [Finset.mem_Icc]; omega)
    (fun ρ hρ ρ' hρ' h => hinj ρ hρ ρ' hρ' (by have := hrM ρ hρ; have := hrM ρ' hρ'; simp only at h; omega))
  rw [div_le_div_iff_of_pos_right hsc]
  linarith

/-- integer distance: `|N − kM| ≥ min(N mod M, M − N mod M)`. -/
lemma int_dist (N k : ℤ) {M : ℤ} (hM : 0 < M) : min (N % M) (M - N % M) ≤ |N - k * M| := by
  have h0 : 0 ≤ N % M := Int.emod_nonneg _ hM.ne'
  have h1 : N % M < M := Int.emod_lt_of_pos _ hM
  have e : N - k * M = N % M + M * (N / M - k) := by
    have := Int.emod_add_mul_ediv N M; linear_combination -this
  rw [e]
  rcases le_or_gt 0 (N / M - k) with hj | hj
  · have : 0 ≤ M * (N / M - k) := mul_nonneg hM.le hj
    exact (min_le_left _ _).trans ((le_add_of_nonneg_right this).trans (le_abs_self _))
  · have : M * (N / M - k) ≤ -M := by nlinarith
    refine (min_le_right _ _).trans ?_
    rw [abs_of_neg (by linarith)]
    linarith

end

end MockCusp
