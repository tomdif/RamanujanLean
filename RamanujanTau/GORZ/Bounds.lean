/-
# Uniform-in-`m` bounds for the derivatives of `log Mmain`, and generic facts about the Leibniz chain `gs`

* `Pz_degOK` : every monomial `U^{-p}(U−1)^{-q}` of `Pz m` has `p + q ≥ 2m − 1` (all `m ≥ 1`).
* `fch_bound` : `|f^{(m)}(s)| ≤ (a/2)^m · Bz(Pz m) · U₀^{-(2m−1)}` for `s ≥ 0`, `U₀ ≥ 2`.
* `fch2_zero_le` : `f''(0) ≤ −(a/2)² U₀^{-3}/2` for `U₀ ≥ 12` (explicit `Pz 2`).
* `δ_lower`, `δ_upper` : `(a/4) t³ ≤ δ ≤ (a/2)(B₂+1) t³` with `t = U₀^{-1/2}`.
* `Φ_bound_ge2`, `Φ1_bound`, `Φ0_le` : `|Φ_m(s)| ≤ 2^m B_m t^{m−2}`, `|Φ₁(s)| ≤ X a B₂ t³`, `Φ₀(s) ≤ (a/2)² B₂ X²/2`.
* `gs_abs_le` (domination of the Leibniz chain), `gs_tendsto` (continuity), `gs_Φinf` (`= cH k`).
-/
import RamanujanTau.GORZ.Newton
import RamanujanTau.GORZ.Hermite

set_option autoImplicit false

namespace GORZ

open Real Finset Filter Topology JensenThreshold JensenThreshold.Tail

/-! ## degrees of the `Pz` data -/

def degOK (D : ℕ) (P : UWZ) : Prop := ∀ x ∈ P, D ≤ x.1 + x.2.1

lemma degOK_dZ {D : ℕ} {P : UWZ} (h : degOK D P) : degOK (D + 2) (dZ P) := by
  intro x hx
  simp only [dZ, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨m, hm, hx⟩ := hx
  have := h m hm
  rcases hx with rfl | rfl <;> simp <;> omega

lemma degOK_insZ {D : ℕ} (m : ℕ × ℕ × ℤ) (hm : D ≤ m.1 + m.2.1) : ∀ P : UWZ, degOK D P → degOK D (insZ m P)
  | [], _ => by
    intro x hx
    simp only [insZ, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact hm
  | x :: xs, h => by
    unfold insZ
    split_ifs with hc
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h x (by simp)
      · exact h y (by simp [hy])
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h _ (by simp)
      · exact degOK_insZ m hm xs (fun z hz => h z (by simp [hz])) y hy

lemma degOK_normZ {D : ℕ} : ∀ P : UWZ, degOK D P → degOK D (normZ P)
  | [], _ => by intro x hx; simp [normZ] at hx
  | x :: xs, h => by
    show degOK D (insZ x (normZ xs))
    exact degOK_insZ x (h x (by simp)) _ (degOK_normZ xs (fun z hz => h z (by simp [hz])))

lemma Pz_degOK' : ∀ m : ℕ, degOK (2 * m + 1) (Pz (m + 1))
  | 0 => by intro x hx; simp [Pz, P1] at hx; rcases hx with rfl | rfl | rfl <;> simp
  | m + 1 => by
    show degOK (2 * (m + 1) + 1) (normZ (dZ (Pz (m + 1))))
    exact degOK_normZ _ (by have := degOK_dZ (Pz_degOK' m); rwa [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring] at this)

lemma Pz_degOK {m : ℕ} (hm : 1 ≤ m) : degOK (2 * m - 1) (Pz m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]; exact Pz_degOK' k

/-! ## the absolute bound -/

noncomputable def Bz (P : UWZ) : ℝ := (P.map fun x => |(x.2.2 : ℝ)| * 2 ^ x.2.1).sum

lemma Bz_cons (x : ℕ × ℕ × ℤ) (P : UWZ) : Bz (x :: P) = |(x.2.2 : ℝ)| * 2 ^ x.2.1 + Bz P := by
  simp [Bz]

lemma Bz_nonneg : ∀ P : UWZ, 0 ≤ Bz P
  | [] => by simp [Bz]
  | x :: P => by rw [Bz_cons]; have := Bz_nonneg P; positivity

lemma abs_evalZ_le {U : ℝ} (hU : 2 ≤ U) {D : ℕ} : ∀ P : UWZ, degOK D P → |evalZ P U| ≤ Bz P * (U⁻¹) ^ D
  | [], _ => by simp [evalZ, Bz]
  | x :: P, h => by
    rw [evalZ_cons, Bz_cons]
    have ih := abs_evalZ_le hU P (fun z hz => h z (by simp [hz]))
    have hu0 : 0 < U⁻¹ := by positivity
    have hu1 : U⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hw0 : 0 < (U - 1)⁻¹ := inv_pos.mpr (by linarith)
    have hw : (U - 1)⁻¹ ≤ 2 * U⁻¹ := by
      rw [inv_le_comm₀ (by linarith) (by positivity), mul_inv, inv_inv]
      rw [show (2 : ℝ)⁻¹ * U = U / 2 by ring]; linarith
    have hterm : |(x.2.2 : ℝ) * (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1| ≤
        |(x.2.2 : ℝ)| * 2 ^ x.2.1 * (U⁻¹) ^ D := by
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hu0 _), abs_of_pos (pow_pos hw0 _)]
      calc |(x.2.2 : ℝ)| * (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1
          ≤ |(x.2.2 : ℝ)| * (U⁻¹) ^ x.1 * (2 * U⁻¹) ^ x.2.1 := by gcongr
        _ = |(x.2.2 : ℝ)| * 2 ^ x.2.1 * (U⁻¹) ^ (x.1 + x.2.1) := by rw [mul_pow, pow_add]; ring
        _ ≤ |(x.2.2 : ℝ)| * 2 ^ x.2.1 * (U⁻¹) ^ D :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu0.le hu1 (h x (by simp))) (by positivity)
    calc |(x.2.2 : ℝ) * (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1 + evalZ P U|
        ≤ |(x.2.2 : ℝ) * (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1| + |evalZ P U| := abs_add_le _ _
      _ ≤ |(x.2.2 : ℝ)| * 2 ^ x.2.1 * (U⁻¹) ^ D + Bz P * (U⁻¹) ^ D := add_le_add hterm ih
      _ = _ := by ring

/-- `B_m = Bz (Pz m)`. -/
noncomputable def Bm (m : ℕ) : ℝ := Bz (Pz m)

lemma Bm_nonneg (m : ℕ) : 0 ≤ Bm m := Bz_nonneg _

theorem fch_bound {U0 : ℝ} (hU0 : 2 ≤ U0) {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    |fch U0 m s| ≤ (aC / 2) ^ m * Bm m * (U0⁻¹) ^ (2 * m - 1) := by
  have hUs := U0_le_Us (by linarith : 1 < U0) hs
  simp only [fch, if_neg (show m ≠ 0 by omega)]
  rw [abs_mul, abs_of_pos (pow_pos (by have := aC_pos; positivity) _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by have := aC_pos; positivity)
  calc |evalZ (Pz m) (Us U0 s)| ≤ Bm m * ((Us U0 s)⁻¹) ^ (2 * m - 1) :=
        abs_evalZ_le (by linarith) _ (Pz_degOK hm)
    _ ≤ Bm m * (U0⁻¹) ^ (2 * m - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
          (inv_anti₀ (by linarith) hUs) _) (Bm_nonneg m)

lemma evalZ_Pz2 (U : ℝ) : evalZ (Pz 2) U =
    -(U⁻¹ ^ 3 * (U - 1)⁻¹) + 6 * U⁻¹ ^ 4 - U⁻¹ ^ 2 * (U - 1)⁻¹ ^ 2 - U⁻¹ ^ 3 := by
  have : Pz 2 = [(3, 1, -1), (4, 0, 6), (2, 2, -1), (2, 1, 0), (3, 0, -1)] := by decide
  rw [this]; simp [evalZ]; ring

theorem fch2_zero_le {U0 : ℝ} (hU0 : 12 ≤ U0) : fch U0 2 0 ≤ -((aC / 2) ^ 2 * (U0⁻¹) ^ 3 / 2) := by
  have hUs : Us U0 0 = U0 := Us_zero (by linarith)
  simp only [fch, if_neg (show (2 : ℕ) ≠ 0 by omega), hUs, evalZ_Pz2]
  have hu0 : 0 < U0⁻¹ := by positivity
  have hu1 : U0⁻¹ ≤ 1 / 12 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  have hw0 : 0 < (U0 - 1)⁻¹ := inv_pos.mpr (by linarith)
  have ha : 0 < (aC / 2) ^ 2 := by have := aC_pos; positivity
  have key : -(U0⁻¹ ^ 3 * (U0 - 1)⁻¹) + 6 * U0⁻¹ ^ 4 - U0⁻¹ ^ 2 * (U0 - 1)⁻¹ ^ 2 - U0⁻¹ ^ 3 ≤
      -(U0⁻¹ ^ 3 / 2) := by
    have h1 : 0 ≤ U0⁻¹ ^ 3 * (U0 - 1)⁻¹ := by positivity
    have h2 : 0 ≤ U0⁻¹ ^ 2 * (U0 - 1)⁻¹ ^ 2 := by positivity
    have h3 : 6 * U0⁻¹ ^ 4 ≤ U0⁻¹ ^ 3 / 2 := by
      have : U0⁻¹ ^ 4 = U0⁻¹ ^ 3 * U0⁻¹ := by ring
      rw [this]; have := pow_pos hu0 3; nlinarith
    linarith
  calc (aC / 2) ^ 2 * (-(U0⁻¹ ^ 3 * (U0 - 1)⁻¹) + 6 * U0⁻¹ ^ 4 - U0⁻¹ ^ 2 * (U0 - 1)⁻¹ ^ 2 - U0⁻¹ ^ 3)
      ≤ (aC / 2) ^ 2 * (-(U0⁻¹ ^ 3 / 2)) := mul_le_mul_of_nonneg_left key ha.le
    _ = _ := by ring

/-! ## `δ` and `Φ` in terms of `t = U₀^{-1/2}` -/

section
variable {U0 : ℝ} (hU0 : 12 ≤ U0)
include hU0

lemma t_pos : 0 < t0v U0 := t0v_pos (by linarith)
lemma t_le_one : t0v U0 ≤ 1 := by
  have h := t0v_sq (show 1 < U0 by linarith)
  have hp := t_pos hU0
  have : t0v U0 ^ 2 ≤ 1 := by rw [h]; exact inv_le_one_of_one_le₀ (by linarith)
  nlinarith

lemma Uinv_pow (m : ℕ) : (U0⁻¹) ^ m = t0v U0 ^ (2 * m) := by
  rw [← t0v_sq (show 1 < U0 by linarith), ← pow_mul]

lemma neg_fch2_pos : 0 < -fch U0 2 0 := by
  have := fch2_zero_le hU0
  have : 0 < (aC / 2) ^ 2 * (U0⁻¹) ^ 3 / 2 := by
    have := aC_pos; have : 0 < U0⁻¹ := (by positivity)
    positivity
  linarith

lemma δ_sq : δv U0 ^ 2 = -fch U0 2 0 / 2 := by
  unfold δv; rw [Real.sq_sqrt]; have := neg_fch2_pos hU0; linarith

lemma δ_lower : aC / 4 * t0v U0 ^ 3 ≤ δv U0 := by
  unfold δv
  have ht := t_pos hU0
  apply Real.le_sqrt_of_sq_le
  have h := fch2_zero_le hU0
  rw [Uinv_pow hU0] at h
  have : (aC / 4 * t0v U0 ^ 3) ^ 2 = (aC / 2) ^ 2 * t0v U0 ^ (2 * 3) / 2 / 2 := by ring
  rw [this]; linarith

lemma δ_pos : 0 < δv U0 := lt_of_lt_of_le (by have := aC_pos; have := t_pos hU0; positivity) (δ_lower hU0)

lemma δ_upper : δv U0 ≤ aC / 2 * (Bm 2 + 1) * t0v U0 ^ 3 := by
  have ht := t_pos hU0
  have hB := Bm_nonneg 2
  have h := fch_bound (by linarith : (2 : ℝ) ≤ U0) (m := 2) (by norm_num) (le_refl (0 : ℝ))
  rw [Uinv_pow hU0] at h
  have hsq := δ_sq hU0
  have hδ := δ_pos hU0
  have hle : δv U0 ^ 2 ≤ (aC / 2 * (Bm 2 + 1) * t0v U0 ^ 3) ^ 2 := by
    rw [hsq]
    have h1 : -fch U0 2 0 ≤ |fch U0 2 0| := neg_le_abs _
    have h2 : (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ (2 * (2 * 2 - 1)) ≤
        (aC / 2 * (Bm 2 + 1) * t0v U0 ^ 3) ^ 2 * 2 := by
      have e : (aC / 2 * (Bm 2 + 1) * t0v U0 ^ 3) ^ 2 * 2 =
          (aC / 2) ^ 2 * (2 * (Bm 2 + 1) ^ 2) * t0v U0 ^ (2 * (2 * 2 - 1)) := by ring
      rw [e]
      have : Bm 2 ≤ 2 * (Bm 2 + 1) ^ 2 := by nlinarith
      have : 0 ≤ (aC / 2) ^ 2 * t0v U0 ^ (2 * (2 * 2 - 1)) := by positivity
      nlinarith
    linarith
  have : 0 ≤ aC / 2 * (Bm 2 + 1) * t0v U0 ^ 3 := by have := aC_pos; positivity
  exact (pow_le_pow_iff_left₀ hδ.le this two_ne_zero).mp hle

lemma Φ_bound_ge2 {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    |Φv U0 m s| ≤ 2 ^ m * Bm m * t0v U0 ^ (m - 2) := by
  have ht := t_pos hU0
  have hδ := δ_pos hU0
  have hf := fch_bound (by linarith : (2 : ℝ) ≤ U0) (by omega : 1 ≤ m) hs
  rw [Uinv_pow hU0] at hf
  unfold Φv
  rw [φv_ge2 hm, abs_div, abs_of_pos (pow_pos hδ m), div_le_iff₀ (pow_pos hδ m)]
  have hl : (aC / 4 * t0v U0 ^ 3) ^ m ≤ δv U0 ^ m :=
    pow_le_pow_left₀ (by have := aC_pos; positivity) (δ_lower hU0) m
  have e : (aC / 2) ^ m * Bm m * t0v U0 ^ (2 * (2 * m - 1)) =
      2 ^ m * Bm m * t0v U0 ^ (m - 2) * (aC / 4 * t0v U0 ^ 3) ^ m := by
    rw [mul_pow, ← pow_mul, show aC / 2 = 2 * (aC / 4) by ring, mul_pow]
    have : t0v U0 ^ (2 * (2 * m - 1)) = t0v U0 ^ (m - 2) * t0v U0 ^ (3 * m) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hB := Bm_nonneg m
  calc |fch U0 m s| ≤ _ := hf
    _ = _ := e
    _ ≤ 2 ^ m * Bm m * t0v U0 ^ (m - 2) * δv U0 ^ m := by gcongr

lemma φ1_abs {X s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) :
    |φv U0 1 s| ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 * s := by
  have hb : ∀ t, 0 ≤ t → t ≤ X → -((aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6) ≤ fch U0 2 t ∧
      fch U0 2 t ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 := by
    intro t ht _
    have := fch_bound (by linarith : (2 : ℝ) ≤ U0) (m := 2) (by norm_num) ht
    rw [Uinv_pow hU0] at this
    exact abs_le.mp this
  have := φv1_bounds (by linarith : 1 < U0) hb hs hsX
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

lemma Φ1_bound {X s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) : |Φv U0 1 s| ≤ X * aC * Bm 2 := by
  have ht := t_pos hU0
  have ht1 := t_le_one hU0
  have hδ := δ_pos hU0
  have h := φ1_abs hU0 hs hsX
  unfold Φv
  rw [pow_one, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
  have hl := δ_lower hU0
  have hB := Bm_nonneg 2
  have ha := aC_pos
  have hX : 0 ≤ X := le_trans hs hsX
  calc |φv U0 1 s| ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 * s := h
    _ ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 * X := by gcongr
    _ = X * aC * Bm 2 * (aC / 4 * t0v U0 ^ 3) * t0v U0 ^ 3 := by ring
    _ ≤ X * aC * Bm 2 * (aC / 4 * t0v U0 ^ 3) * 1 := by
        gcongr; exact pow_le_one₀ ht.le ht1
    _ ≤ X * aC * Bm 2 * δv U0 := by rw [mul_one]; gcongr

lemma Φ0_le {X s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) : Φv U0 0 s ≤ (aC / 2) ^ 2 * Bm 2 * X ^ 2 / 2 := by
  have ht := t_pos hU0
  have ht1 := t_le_one hU0
  have hb : ∀ t, 0 ≤ t → t ≤ X → -((aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6) ≤ fch U0 2 t ∧
      fch U0 2 t ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 := by
    intro t ht _
    have := fch_bound (by linarith : (2 : ℝ) ≤ U0) (m := 2) (by norm_num) ht
    rw [Uinv_pow hU0] at this
    exact abs_le.mp this
  have h := (φv0_bounds (by linarith : 1 < U0) hb hs hsX).2
  unfold Φv
  rw [pow_zero, div_one]
  have hB := Bm_nonneg 2
  have ha := aC_pos
  calc φv U0 0 s ≤ (aC / 2) ^ 2 * Bm 2 * t0v U0 ^ 6 * s ^ 2 / 2 := h
    _ ≤ (aC / 2) ^ 2 * Bm 2 * 1 * X ^ 2 / 2 := by
        gcongr
        · exact pow_le_one₀ ht.le ht1
    _ = _ := by ring

omit hU0 in
lemma Φ0_zero : Φv U0 0 0 = 0 := by simp [Φv, φv0_zero]
omit hU0 in
lemma Φ1_zero : Φv U0 1 0 = 0 := by simp [Φv, φv1_zero]
lemma Φ2_zero : Φv U0 2 0 = -2 := by
  unfold Φv
  rw [φv_ge2 le_rfl, δ_sq hU0]
  have hne : fch U0 2 0 ≠ 0 := by have := neg_fch2_pos hU0; linarith
  rw [show -fch U0 2 0 / 2 = fch U0 2 0 * (-1 / 2) by ring, ← div_div, div_self hne]; norm_num

end

/-! ## the Leibniz chain: domination and continuity -/

theorem gs_abs_le (φ ψ : ℕ → ℝ → ℝ) (t : ℝ) (h0 : φ 0 t ≤ ψ 0 t) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → |φ i t| ≤ ψ i t) → |gs φ k t| ≤ gs ψ k t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hb
    rcases k with _ | k
    · rw [gs_zero, gs_zero, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr h0
    · rw [gs_succ, gs_succ]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
      simp only [mem_range] at hi
      have hg := ih (k - i) (by omega) (fun j h1 h2 => hb j h1 (by omega))
      have hp := hb (i + 1) (by omega) (by omega)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose i : ℝ))]
      have := abs_nonneg (gs φ (k - i) t)
      have := abs_nonneg (φ (i + 1) t)
      have := (abs_nonneg _).trans hg
      gcongr

theorem gs_tendsto {ι : Type*} {l : Filter ι} (φ : ι → ℕ → ℝ → ℝ) (ψ : ℕ → ℝ → ℝ) (t : ℝ) :
    ∀ k, (∀ i ≤ k, Tendsto (fun n => φ n i t) l (𝓝 (ψ i t))) →
      Tendsto (fun n => gs (φ n) k t) l (𝓝 (gs ψ k t)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    rcases k with _ | k
    · simp only [gs_zero]
      exact (Real.continuous_exp.tendsto _).comp (h 0 le_rfl)
    · simp only [gs_succ]
      apply tendsto_finsetSum
      intro i hi
      simp only [mem_range] at hi
      exact ((ih (k - i) (by omega) (fun j hj => h j (by omega))).const_mul _).mul (h (i + 1) (by omega))

/-- the limiting chain `Φ₂ = −2`, all other `Φ_m = 0`. -/
def Φinf : ℕ → ℝ → ℝ := fun i _ => if i = 2 then -2 else 0

theorem gs_Φinf : ∀ k, gs Φinf k 0 = cH k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [gs_zero, Φinf, cH_zero]
    · rw [gs_succ]; simp [Φinf, cH_one]
    · rw [gs_succ, sum_eq_single 1]
      · rw [show k + 1 - 1 = k by omega, ih k (by omega), cH_add_two]
        simp [Φinf]; ring
      · intro b _ hb; simp [Φinf, show b + 1 ≠ 2 by omega]
      · intro h; simp at h

end GORZ
