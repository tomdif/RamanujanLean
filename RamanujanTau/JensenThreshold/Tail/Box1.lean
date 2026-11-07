/-
# Soundness of the box intervals, part 1: `t₀`, `c₂`, `δ`, `Φ_m(0)`, `Φ_m(s)` for `s ∈ [0, d]`, and the
Leibniz values `ĝ_k`
-/
import RamanujanTau.JensenThreshold.Tail.Link

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real Iv Finset

lemma mem_Ia : aC ∈ᵢ Ia := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have hp : (0 : ℝ) < π := Real.pi_pos
  have lo := (mem_ofFrac (2 * 314159265358979323846 ^ 2) (3 * 10 ^ 40) (by norm_num)).1
  have hi := (mem_ofFrac (2 * 314159265358979323847 ^ 2) (3 * 10 ^ 40) (by norm_num)).2
  refine ⟨le_trans lo ?_, le_trans ?_ hi⟩
  · unfold aC; push_cast; nlinarith
  · unfold aC; push_cast; nlinarith

lemma mem_Ia2 : aC / 2 ∈ᵢ Ia2 := by
  have := mem_mul mem_Ia (mem_ofFrac 1 2 (by norm_num))
  convert this using 1; push_cast; ring

lemma lo_le_hi {x : ℝ} {I : Iv} (hx : x ∈ᵢ I) : I.lo ≤ I.hi := by
  have := le_trans hx.1 hx.2
  have hS := S_posR
  have : (I.lo : ℝ) ≤ I.hi := (div_le_div_iff_of_pos_right hS).mp this
  exact_mod_cast this

lemma mem_lo {x : ℝ} {I : Iv} (hx : x ∈ᵢ I) : ((I.lo : ℝ) / S) ∈ᵢ I :=
  ⟨le_rfl, div_le_div_of_nonneg_right (by exact_mod_cast lo_le_hi hx) S_posR.le⟩
lemma mem_hi {x : ℝ} {I : Iv} (hx : x ∈ᵢ I) : ((I.hi : ℝ) / S) ∈ᵢ I :=
  ⟨div_le_div_of_nonneg_right (by exact_mod_cast lo_le_hi hx) S_posR.le, le_rfl⟩

lemma getD_three_append {a b c : Iv} {L : List Iv} {i : ℕ} :
    ([a, b, c] ++ L).getD i zeroI = if i = 0 then a else if i = 1 then b else if i = 2 then c
      else L.getD (i - 3) zeroI := by
  rcases i with _ | _ | _ | i <;> simp [List.getD]

lemma getD_two_append {a b : Iv} {L : List Iv} {i : ℕ} :
    ([a, b] ++ L).getD i zeroI = if i = 0 then a else if i = 1 then b else L.getD (i - 2) zeroI := by
  rcases i with _ | _ | i <;> simp [List.getD]

/-- the facts certified by `checkBox` that the soundness proof uses. -/
structure BoxOK (d K N : ℕ) (B : BoxD) : Prop where
  tlq : 0 < B.tlq
  thq : 0 < B.thq
  tlp : 0 ≤ B.tlp
  thp : 0 < B.thp
  half : 2 * B.thp ≤ B.thq
  u0 : 0 < (oneI - bIu0 B).lo
  c2 : 0 < (bc2 B).lo
  sq : 0 < (bsq B).lo
  us : 0 < (oneI - bIus d B).lo
  rho : 0 < (bIrho d B).lo
  c2p : ∀ m ≤ K, 0 < (c2powI (bc2 B) (bsq B) m).lo
  phi0 : ((bPhis d K B).getD 0 zeroI).hi ≤ 0
  f2 : (bIf2 d B).hi ≤ 0
  okQ : ∀ m ≤ K, okQ m (Pz m) = true
  K3 : 3 ≤ K
  dK : d + 1 ≤ K
  dN : 3 * d + 4 ≤ 2 * N
  asq : 0 < (Ia2 * bsq B).lo
  dki : ∀ k ≤ d, ∀ i < k, Dki k i = 0
  len : B.pts.length = d + 1
  mono : ∀ i < d, (B.pts.getD i (0, 1)).1 * (B.pts.getD (i + 1) (0, 1)).2 <
      (B.pts.getD (i + 1) (0, 1)).1 * (B.pts.getD i (0, 1)).2
  den : ∀ x ∈ B.pts, 0 < x.2
  sign : ∀ i ≤ d, signOK d i (bG d K N B (B.pts.getD i (0, 1))) = true
  fin : 0 < B.tlp → 0 < (bIU0 B - oneI).lo ∧ 0 < (bIexps N B).lo ∧ 0 < (bdel B).lo ∧ 0 < (bIu0 B).lo

theorem boxOK_of_check {d K N : ℕ} {B : BoxD} (h : checkBox d K N B = true) : BoxOK d K N B := by
  simp only [checkBox, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, fun m hm => h12 m (by omega), h13, h14,
    fun m hm => h15 m (by omega), h16, h17, h18, h19, fun k hk i hi => h20 k (by omega) i hi, h21,
    h22, h23, fun i hi => h24 i (by omega), fun hp => ?_⟩
  simp only [hp, if_true, Bool.and_eq_true, decide_eq_true_eq] at h25
  exact ⟨h25.1.1.1, h25.1.1.2, h25.1.2, h25.2⟩

lemma okQ2 {d K N : ℕ} {B : BoxD} (hB : BoxOK d K N B) : okQ 2 (Pz 2) = true :=
  hB.okQ 2 (by have := hB.K3; omega)

/-! ## memberships for a real `U₀` with `t₀ ∈ bIt B` -/

section
variable {d K N : ℕ} {B : BoxD} (hB : BoxOK d K N B) {U0 : ℝ} (hU0 : 1 < U0) (ht : t0v U0 ∈ᵢ bIt B)
include hB hU0 ht

lemma m_u0 : U0⁻¹ ∈ᵢ bIu0 B := by rw [← t0v_sq hU0]; exact mem_pow ht 2

lemma m_om0 : U0 / (U0 - 1) ∈ᵢ bIom0 B := by
  have h := mem_inv (mem_sub mem_oneI (m_u0 hB hU0 ht)) hB.u0
  have e : U0 / (U0 - 1) = (1 - U0⁻¹)⁻¹ := by
    have : U0 - 1 ≠ 0 := by linarith
    field_simp
  rw [e]; exact h

lemma m_Q0 (m : ℕ) : Qv U0 m 0 ∈ᵢ evalQIv (Qd m) (bIu0 B) (bIom0 B) := by
  unfold Qv; rw [Us_zero hU0]; exact mem_evalQIv _ (m_u0 hB hU0 ht) (m_om0 hB hU0 ht)

lemma m_c2 : c2v U0 ∈ᵢ bc2 B := by
  have := mem_mul (m_Q0 hB hU0 ht 2) (mem_ofFrac (-1) 2 (by norm_num))
  unfold c2v; convert this using 1; push_cast; ring

lemma c2v_pos : 0 < c2v U0 := pos_of_mem (m_c2 hB hU0 ht) hB.c2

lemma m_sq : Real.sqrt (c2v U0) ∈ᵢ bsq B := mem_sqrt (m_c2 hB hU0 ht) hB.c2.le

lemma m_del : δv U0 ∈ᵢ bdel B := by
  rw [δv_eq hU0 (okQ2 hB) (c2v_pos hB hU0 ht).le]
  exact mem_mul (mem_mul mem_Ia2 (mem_pow ht 3)) (m_sq hB hU0 ht)

lemma m_c2p (m : ℕ) : c2p U0 m ∈ᵢ c2powI (bc2 B) (bsq B) m :=
  mem_c2powI (m_c2 hB hU0 ht) (m_sq hB hU0 ht) m

lemma m_Phi0 : ∀ i ≤ K, Φv U0 i 0 ∈ᵢ (bPhi0 K B).getD i zeroI := by
  intro i hi
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  unfold bPhi0
  rw [getD_three_append]
  split_ifs with h0 h1 h2
  · subst h0; simp [Φv, φv0_zero]; exact mem_zeroI
  · subst h1; simp [Φv, φv1_zero]; exact mem_zeroI
  · subst h2; rw [Φv2_zero hU0 hq2 hc]; exact mem_ofInt' _ (by norm_num)
  · rw [getD_map_range _ _ _ _ (by omega)]
    rw [Φv_zero_ge2 hU0 hq2 hc (by omega) (hB.okQ i hi)]
    have hi3 : i - 3 + 3 = i := by omega
    have hi1 : i - 3 + 1 = i - 2 := by omega
    rw [hi3, hi1]
    exact mem_mul (mem_mul (m_Q0 hB hU0 ht i) (mem_pow ht _))
      (mem_inv (m_c2p hB hU0 ht i) (hB.c2p i hi))

lemma m_g0 : ∀ k ≤ K, gs (Φv U0) k 0 ∈ᵢ (bg0 K B).getD k zeroI := by
  apply mem_recIv
  · exact m_Phi0 hB hU0 ht
  · simp [Φv, φv0_zero]; exact mem_oneI

/-! ### `s ∈ [0, d]` -/

lemma one_le_ratio_inv {s : ℝ} (hs : 0 ≤ s) : U0 / Us U0 s ≤ 1 := by
  have := U0_le_Us hU0 hs; have := one_lt_Us hU0 hs
  rw [div_le_one (by linarith)]; linarith

lemma Us_le_rho {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) :
    Us U0 s ≤ U0 * Real.sqrt (1 + aC * d * t0v U0 ^ 4) := by
  have hU := one_lt_Us hU0 hs
  have ha := aC_pos
  have ht4 : t0v U0 ^ 4 = (U0⁻¹) ^ 2 := by rw [← t0v_sq hU0, ← pow_mul]
  have hr : 0 ≤ 1 + aC * d * t0v U0 ^ 4 := by have := t0v_pos hU0; positivity
  have hsq : (U0 * Real.sqrt (1 + aC * d * t0v U0 ^ 4)) ^ 2 = U0 ^ 2 + aC * d := by
    rw [mul_pow, Real.sq_sqrt hr, ht4]
    have : U0 ≠ 0 := by linarith
    field_simp
  have h2 : Us U0 s ^ 2 ≤ (U0 * Real.sqrt (1 + aC * d * t0v U0 ^ 4)) ^ 2 := by
    rw [hsq, Us_sq hU0 hs]; nlinarith
  exact (pow_le_pow_iff_left₀ (by linarith) (by have := Real.sqrt_nonneg (1 + aC * d * t0v U0 ^ 4); nlinarith)
    two_ne_zero).mp h2

lemma m_rho : Real.sqrt (1 + aC * d * t0v U0 ^ 4) ∈ᵢ bIrho d B := by
  unfold bIrho
  apply mem_sqrt _ (le_of_lt (S_pos))
  have hm := mem_add mem_oneI (mem_mul (mem_mul mem_Ia (mem_ofInt (d : ℤ))) (mem_pow ht 4))
  have ha := aC_pos
  have ht0 := t0v_pos hU0
  refine ⟨?_, ?_⟩
  · simp only
    rw [div_self (S_posR.ne')]
    have : 0 ≤ aC * d * t0v U0 ^ 4 := by positivity
    linarith
  · have := hm.2; push_cast at this ⊢; linarith

lemma m_ratio {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : U0 / Us U0 s ∈ᵢ bIratio d B := by
  unfold bIratio
  have hrho := m_rho hB hU0 ht (d := d)
  have hrpos : 0 < Real.sqrt (1 + aC * d * t0v U0 ^ 4) := pos_of_mem hrho hB.rho
  have hinv := mem_inv hrho hB.rho
  have hU := one_lt_Us hU0 hs
  refine ⟨?_, ?_⟩
  · refine le_trans hinv.1 ?_
    have hle := Us_le_rho hB hU0 ht hs hsd
    rw [inv_eq_one_div, div_le_div_iff₀ hrpos (by linarith)]
    linarith
  · simp only; rw [div_self S_posR.ne']; exact one_le_ratio_inv hB hU0 ht hs

lemma m_us {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : (Us U0 s)⁻¹ ∈ᵢ bIus d B := by
  have := mem_mul (m_u0 hB hU0 ht) (m_ratio hB hU0 ht hs hsd)
  have hU := one_lt_Us hU0 hs
  convert this using 1
  have : U0 ≠ 0 := by linarith
  field_simp

lemma m_oms {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : Us U0 s / (Us U0 s - 1) ∈ᵢ bIoms d B := by
  have h := mem_inv (mem_sub mem_oneI (m_us hB hU0 ht hs hsd)) hB.us
  have hU := one_lt_Us hU0 hs
  have e : Us U0 s / (Us U0 s - 1) = (1 - (Us U0 s)⁻¹)⁻¹ := by
    have : Us U0 s - 1 ≠ 0 := by linarith
    field_simp
  rw [e]; exact h

lemma m_Qs (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) :
    Qv U0 m s ∈ᵢ evalQIv (Qd m) (bIus d B) (bIoms d B) :=
  mem_evalQIv _ (m_us hB hU0 ht hs hsd) (m_oms hB hU0 ht hs hsd)

lemma m_f2 {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : fch U0 2 s ∈ᵢ bIf2 d B := by
  rw [f2_eq hU0 (okQ2 hB) hs]
  exact mem_mul (mem_mul (mem_pow mem_Ia2 2) (mem_pow (m_us hB hU0 ht hs hsd) 3)) (m_Qs hB hU0 ht 2 hs hsd)

lemma m_J1 {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : fch U0 2 s / δv U0 ∈ᵢ bJ1 d B := by
  rw [f2_div_δ hU0 (okQ2 hB) (c2v_pos hB hU0 ht) hs]
  exact mem_mul (mem_mul (mem_mul (mem_mul mem_Ia2 (mem_pow (m_ratio hB hU0 ht hs hsd) 3)) (mem_pow ht 3))
    (m_Qs hB hU0 ht 2 hs hsd)) (mem_inv (m_sq hB hU0 ht) hB.sq)

lemma m_sint {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : s ∈ᵢ bsint d := by
  unfold bsint Iv.mem
  simp only [Int.cast_zero, zero_div]
  refine ⟨hs, ?_⟩
  push_cast; rw [mul_div_assoc, div_self S_posR.ne', mul_one]; exact hsd

lemma m_Phis : ∀ i ≤ K, ∀ s : ℝ, 0 ≤ s → s ≤ (d : ℝ) → Φv U0 i s ∈ᵢ (bPhis d K B).getD i zeroI := by
  intro i hi s hs hsd
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc
  -- uniform bounds for `f''` on `[0, d]`
  have hb : ∀ t, 0 ≤ t → t ≤ (d : ℝ) → ((bIf2 d B).lo : ℝ) / S ≤ fch U0 2 t ∧ fch U0 2 t ≤ ((bIf2 d B).hi : ℝ) / S :=
    fun t h1 h2 => m_f2 hB hU0 ht h1 h2
  unfold bPhis
  rw [getD_two_append]
  split_ifs with h0 h1
  · subst h0
    have hφ := φv0_bounds hU0 hb hs hsd
    have hf2 := m_f2 hB hU0 ht hs hsd
    have e1 : ((bIf2 d B).lo : ℝ) / S * s ^ 2 / 2 = (s ^ 2 * (1 / 2)) * (((bIf2 d B).lo : ℝ) / S) := by ring
    have e2 : ((bIf2 d B).hi : ℝ) / S * s ^ 2 / 2 = (s ^ 2 * (1 / 2)) * (((bIf2 d B).hi : ℝ) / S) := by ring
    have hhalf : (1 / 2 : ℝ) ∈ᵢ ofFrac 1 2 := by simpa using mem_ofFrac 1 2 (by norm_num)
    have hs2 := mem_mul (mem_pow (m_sint hB hU0 ht hs hsd) 2) hhalf
    have A1 := mem_mul hs2 (mem_lo hf2)
    have A2 := mem_mul hs2 (mem_hi hf2)
    rw [← e1] at A1; rw [← e2] at A2
    simp only [Φv, pow_zero, div_one]
    exact mem_between A1 A2 hφ.1 hφ.2
  · subst h1
    have hJ := m_J1 hB hU0 ht hs hsd
    have hb' : ∀ t, 0 ≤ t → t ≤ (d : ℝ) →
        ((bJ1 d B).lo : ℝ) / S * δv U0 ≤ fch U0 2 t ∧ fch U0 2 t ≤ ((bJ1 d B).hi : ℝ) / S * δv U0 := by
      intro t h1 h2
      have := m_J1 hB hU0 ht h1 h2
      exact ⟨by have := this.1; rwa [le_div_iff₀ hδ] at this, by have := this.2; rwa [div_le_iff₀ hδ] at this⟩
    have hφ := φv1_bounds hU0 hb' hs hsd
    have hsI := m_sint hB hU0 ht hs hsd
    have A1 := mem_mul hsI (mem_lo hJ)
    have A2 := mem_mul hsI (mem_hi hJ)
    simp only [Φv, pow_one]
    refine mem_between A1 A2 ?_ ?_
    · rw [le_div_iff₀ hδ]; nlinarith [hφ.1]
    · rw [div_le_iff₀ hδ]; nlinarith [hφ.2]
  · rw [getD_map_range _ _ _ _ (by omega)]
    have hi2 : i - 2 + 2 = i := by omega
    rw [hi2, Φv_ge2 hU0 hq2 hc (by omega) (hB.okQ i hi) hs]
    exact mem_mul (mem_mul (mem_mul (mem_pow (m_ratio hB hU0 ht hs hsd) _) (mem_pow ht _))
      (m_Qs hB hU0 ht i hs hsd)) (mem_inv (m_c2p hB hU0 ht i) (hB.c2p i hi))

lemma m_E0s {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : Real.exp (Φv U0 0 s) ∈ᵢ bE0s d K B := by
  have h := m_Phis hB hU0 ht 0 (by omega) s hs hsd
  have hle : Φv U0 0 s ≤ 0 := nonpos_of_mem h hB.phi0
  unfold bE0s Iv.mem
  constructor
  · push_cast
    rw [add_div, div_self S_posR.ne']
    have := Real.add_one_le_exp (Φv U0 0 s)
    linarith [h.1]
  · rw [div_self S_posR.ne']; exact Real.exp_le_one_iff.mpr hle

lemma m_gs {s : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) : |gs (Φv U0) K s| ≤ (bMK d K B : ℝ) / S := by
  have := mem_recIv (Φv U0) (bPhis d K B) (bE0s d K B) s K
    (fun i hi => m_Phis hB hU0 ht i hi s hs hsd) (m_E0s hB hU0 ht hs hsd) K le_rfl
  exact abs_le_absHi this

end

end JensenThreshold.Tail
