/-
# `L(Δ,s) ≠ 0` on the edge `Re s = 13/2` (Rankin 1939 / Ogg / Moreno; Deligne-free)

Build: `nice -n 10 lake build RamanujanTau.EdgeNonvanishing.Main`. See `docs/EDGE_NONVANISHING.md`.

Headlines (unconditional):

* `tauL_ne_zero_edge (t : ℝ) : tauL (13/2 + t*I) ≠ 0`;
* `tauL_ne_zero_of_ge`: `tauL s ≠ 0` for `Re s ≥ 13/2`;
* `tauL_ne_zero_of_le`: `tauL s ≠ 0` for `Re s ≤ 11/2` unless `s = −n` (functional equation).

Proof (`t ≠ 0`). `F(σ) = ζ(σ) L(σ+it)² L(σ−it)² (ζ(2σ)R(σ))² ζ(2σ+4it)R(σ+2it) ζ(2σ−4it)R(σ−2it)`
satisfies `‖F(σ)‖ ≥ 1` for `σ > 1` (`Assembly.one_le_norm_Fval`). If `L(1+it) = 0`, then as
`σ → 1⁺`: `ζ(σ) = O(1/(σ−1))`, `L(σ±it) = O(σ−1)` (also `L(1−it) = 0` by conjugation),
`ζ(2σ)R(σ) = O(1/(σ−1))` and `ζ(2σ±4it)R(σ±2it) = O(1)` (Rankin's `O(N^{3/5})` error term
via Abel summation, `RS.rs_sub_zeta_bound`), so `F(σ) = O(σ−1) → 0`: contradiction.
`t = 0`: `L(Δ,13/2) > 0` (`HeckeL.tauL_pos`, the Mellin transform of `Δ(iy) > 0`).
-/
import RamanujanTau.EdgeNonvanishing.Assembly

set_option autoImplicit false

namespace RamanujanTau.EdgeNonvanishing

open Complex Filter Topology Asymptotics
open RamanujanTau.HeckeL
open scoped ComplexConjugate

lemma tendsto_path (a b : ℂ) :
    Tendsto (fun h : ℝ => a + b * (h : ℂ)) (𝓝[>] 0) (𝓝 a) := by
  have hc : Continuous (fun h : ℝ => a + b * (h : ℂ)) := by fun_prop
  have := hc.tendsto 0
  simp only [ofReal_zero, mul_zero, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma cont_bound {g : ℂ → ℂ} {a b : ℂ} (hg : ContinuousAt g a) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ‖g (a + b * (h : ℂ))‖ ≤ ‖g a‖ + 1 := by
  have := ((hg.tendsto.comp (tendsto_path a b)).norm)
  exact (this.eventually_lt_const (lt_add_one _)).mono fun _ h => h.le

lemma zero_bound {g : ℂ → ℂ} {a : ℂ} (hg : DifferentiableAt ℂ g a) (h0 : g a = 0) :
    ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ‖g (a + (h : ℂ))‖ ≤ C * h := by
  have hO := hg.isBigO_sub.comp_tendsto (by simpa using tendsto_path a 1)
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨C, (hC.and eventually_mem_nhdsWithin).mono fun h ⟨hh, hpos⟩ => ?_⟩
  simp only [Function.comp_apply, h0, sub_zero, add_sub_cancel_left, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Set.mem_Ioi.mp hpos)] at hh ⊢
  exact hh

lemma zeta_bound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ‖riemannZeta (1 + (h : ℂ))‖ ≤ 2 / h := by
  have hφ : Tendsto (fun h : ℝ => (1 : ℂ) + h) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_path 1 1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, ofReal_eq_zero]
    exact hh.ne'
  have := (riemannZeta_residue_one.comp hφ).norm
  filter_upwards [this.eventually_lt_const (by norm_num : ‖(1 : ℂ)‖ < 2),
    self_mem_nhdsWithin] with h hh (hpos : 0 < h)
  simp only [Function.comp_apply, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos] at hh
  rw [le_div_iff₀ hpos]; linarith

/-- `ζ(2σ)R(σ) = O(1/(σ−1))`. -/
lemma rs_real_bound : ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
    ‖riemannZeta (2 * ((1 + h : ℝ) : ℂ)) * RS ((1 + h : ℝ) : ℂ)‖ ≤ C / h := by
  obtain ⟨K, hK0, hK⟩ := rs_sub_zeta_bound
  have hz2 := cont_bound (g := riemannZeta) (a := 2) (b := 2)
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  refine ⟨(‖riemannZeta 2‖ + 1) * (2 * |rsc| + 5 * K), ?_⟩
  filter_upwards [hz2, zeta_bound, self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with h h1 h2 (hpos : 0 < h) hh1
  have hh1' : h < 1 := hh1.2
  set s : ℂ := ((1 + h : ℝ) : ℂ)
  have hsre : s.re = 1 + h := by simp [s]
  have hsn : ‖s‖ = 1 + h := by
    simp only [s, Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_pos (by linarith)]
  have hR := hK s (by rw [hsre]; linarith)
  have hzs : ‖riemannZeta s‖ ≤ 2 / h := by
    have : s = 1 + (h : ℂ) := by simp [s]
    rw [this]; exact h2
  have h2s : riemannZeta (2 * s) = riemannZeta (2 + 2 * (h : ℂ)) := by
    congr 1; simp [s]; ring
  have hRS : ‖RS s‖ ≤ (2 * |rsc| + 5 * K) / h := by
    have e1 : ‖RS s‖ ≤ ‖(rsc : ℂ) * riemannZeta s‖ + K * ‖s‖ / (s.re - 3 / 5) := by
      have := norm_le_norm_add_norm_sub' (RS s) ((rsc : ℂ) * riemannZeta s)
      linarith
    have e2 : ‖(rsc : ℂ) * riemannZeta s‖ ≤ |rsc| * (2 / h) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hzs (abs_nonneg _)
    have e3 : K * ‖s‖ / (s.re - 3 / 5) ≤ 5 * K / h := by
      rw [hsn, hsre, div_le_div_iff₀ (by linarith) hpos]
      nlinarith [mul_nonneg (mul_nonneg hK0 hpos.le) (sub_pos.mpr hh1').le, mul_nonneg hK0 hpos.le]
    calc ‖RS s‖ ≤ |rsc| * (2 / h) + 5 * K / h := by linarith
      _ = (2 * |rsc| + 5 * K) / h := by field_simp
  rw [norm_mul, h2s]
  calc ‖riemannZeta (2 + 2 * (h : ℂ))‖ * ‖RS s‖ ≤ (‖riemannZeta 2‖ + 1) * ((2 * |rsc| + 5 * K) / h) :=
        mul_le_mul h1 hRS (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `ζ(2σ+4iu)R(σ+2iu) = O(1)` for `u ≠ 0`. -/
lemma rs_line_bound {u : ℝ} (hu : u ≠ 0) : ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
    ‖riemannZeta (2 * sR (1 + h) u) * RS (sR (1 + h) u)‖ ≤ C := by
  obtain ⟨K, hK0, hK⟩ := rs_sub_zeta_bound
  set a : ℂ := 1 + 2 * (u : ℂ) * I
  have ha1 : a ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [a] at this
    exact hu this
  have ha2 : 2 * a ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [a] at this
  have hz1 := cont_bound (g := riemannZeta) (a := a) (b := 1)
    (differentiableAt_riemannZeta ha1).continuousAt
  have hz2 := cont_bound (g := riemannZeta) (a := 2 * a) (b := 2)
    (differentiableAt_riemannZeta ha2).continuousAt
  refine ⟨(‖riemannZeta (2 * a)‖ + 1) * (|rsc| * (‖riemannZeta a‖ + 1) + K * (‖a‖ + 1) * (5 / 2)), ?_⟩
  filter_upwards [hz1, hz2, self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with h h1 h2 (hpos : 0 < h) hh1
  have hh1' : h < 1 := hh1.2
  have hs : sR (1 + h) u = a + 1 * (h : ℂ) := by simp [sR, a]; ring
  have h2s : 2 * sR (1 + h) u = 2 * a + 2 * (h : ℂ) := by rw [hs]; ring
  rw [norm_mul, h2s, hs]
  set s := a + 1 * (h : ℂ)
  have hsre : s.re = 1 + h := by simp [s, a]
  have hsn : ‖s‖ ≤ ‖a‖ + 1 := by
    calc ‖s‖ ≤ ‖a‖ + ‖1 * (h : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖a‖ + 1 := by
        rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]; linarith
  have hR := hK s (by rw [hsre]; linarith)
  have hRS : ‖RS s‖ ≤ |rsc| * (‖riemannZeta a‖ + 1) + K * (‖a‖ + 1) * (5 / 2) := by
    have e1 : ‖RS s‖ ≤ ‖(rsc : ℂ) * riemannZeta s‖ + K * ‖s‖ / (s.re - 3 / 5) := by
      have := norm_le_norm_add_norm_sub' (RS s) ((rsc : ℂ) * riemannZeta s)
      linarith
    have e2 : ‖(rsc : ℂ) * riemannZeta s‖ ≤ |rsc| * (‖riemannZeta a‖ + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have e3 : K * ‖s‖ / (s.re - 3 / 5) ≤ K * (‖a‖ + 1) * (5 / 2) := by
      rw [hsre, div_le_iff₀ (by linarith)]
      have : K * ‖s‖ ≤ K * (‖a‖ + 1) := mul_le_mul_of_nonneg_left hsn hK0
      nlinarith [mul_nonneg (mul_nonneg hK0 (by positivity : (0 : ℝ) ≤ ‖a‖ + 1)) hpos.le]
    linarith
  exact mul_le_mul h2 hRS (norm_nonneg _) (by positivity)

/-- **Non-vanishing on the edge, `t ≠ 0`.** -/
theorem tauL_ne_zero_edge_of_ne {t : ℝ} (ht : t ≠ 0) : tauL (13 / 2 + t * I) ≠ 0 := by
  intro h0
  have h0' : tauL (13 / 2 + ((-t : ℝ) : ℂ) * I) = 0 := by
    have := HeckeZeros.tauL_zero_conj h0
    have e : conj ((13 / 2 : ℂ) + t * I) = 13 / 2 + ((-t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [map_ofNat]
    rwa [e] at this
  have hd := tauLSeries_entire
  obtain ⟨Ca, hCa⟩ := zero_bound (hd (13 / 2 + t * I)) h0
  obtain ⟨Cb, hCb⟩ := zero_bound (hd (13 / 2 + ((-t : ℝ) : ℂ) * I)) h0'
  obtain ⟨C4, hC4⟩ := rs_real_bound
  obtain ⟨C5, hC5⟩ := rs_line_bound ht
  obtain ⟨C6, hC6⟩ := rs_line_bound (neg_ne_zero.mpr ht)
  set M : ℝ := 2 * |Ca| ^ 2 * |Cb| ^ 2 * |C4| ^ 2 * |C5| * |C6|
  have hM : 0 ≤ M := by positivity
  have hsmallE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (1 / (M + 1)) :=
    Ioo_mem_nhdsGT (by positivity)
  have hposE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  have hall := zeta_bound.and (hCa.and (hCb.and (hC4.and (hC5.and (hC6.and (hposE.and hsmallE))))))
  obtain ⟨h, hh⟩ := hall.exists
  obtain ⟨hz, ha, hb, h4, h5, h6, hpos, hsmall⟩ := hh
  have hpos : 0 < h := hpos
  have hsm : h < 1 / (M + 1) := hsmall.2
  have hsL : ∀ u : ℝ, sL (1 + h) u = 13 / 2 + (u : ℂ) * I + h := fun u => by
    simp [sL]; ring
  have hF := one_le_norm_Fval (σ := 1 + h) (by linarith) t
  have e1 : ‖riemannZeta ((1 + h : ℝ) : ℂ)‖ ≤ 2 / h := by
    have : ((1 + h : ℝ) : ℂ) = 1 + (h : ℂ) := by push_cast; ring
    rw [this]; exact hz
  rw [Fval, hsL t, hsL (-t)] at hF
  simp only [norm_mul] at hF
  have h5' : ‖riemannZeta (2 * sR (1 + h) t)‖ * ‖RS (sR (1 + h) t)‖ ≤ |C5| := by
    rw [← norm_mul]; exact h5.trans (le_abs_self _)
  have h6' : ‖riemannZeta (2 * sR (1 + h) (-t))‖ * ‖RS (sR (1 + h) (-t))‖ ≤ |C6| := by
    rw [← norm_mul]; exact h6.trans (le_abs_self _)
  rw [norm_mul] at h4
  have ha' := ha.trans (mul_le_mul_of_nonneg_right (le_abs_self Ca) hpos.le)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self Cb) hpos.le)
  have h4' := h4.trans (div_le_div_of_nonneg_right (le_abs_self C4) hpos.le)
  have key : 1 ≤ (2 / h) * ((|Ca| * h) * (|Ca| * h)) * ((|Cb| * h) * (|Cb| * h)) *
      ((|C4| / h) * (|C4| / h)) * |C5| * |C6| := by
    refine hF.trans ?_
    gcongr
  have hval : (2 / h) * ((|Ca| * h) * (|Ca| * h)) * ((|Cb| * h) * (|Cb| * h)) *
      ((|C4| / h) * (|C4| / h)) * |C5| * |C6| = M * h := by
    simp only [M]; field_simp
  rw [hval] at key
  have : M * h < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hsm
    nlinarith
  linarith

/-- **`L(Δ,s)` has no zeros on the edge `Re s = 13/2`.** -/
theorem tauL_ne_zero_edge (t : ℝ) : tauL (13 / 2 + t * I) ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · have := (tauL_pos (σ := 13 / 2) (by norm_num)).2
    intro h
    have e : (13 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I = ((13 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e] at h
    rw [h] at this
    simp at this
  · exact tauL_ne_zero_edge_of_ne ht

/-- **Non-vanishing on the closed half-plane `Re s ≥ 13/2`.** -/
theorem tauL_ne_zero_of_ge {s : ℂ} (hs : 13 / 2 ≤ s.re) : tauL s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · exact HeckeZeros.tauL_ne_zero_of_gt hs
  · have : s = 13 / 2 + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [← hs]
    rw [this]; exact tauL_ne_zero_edge s.im

/-- **By the functional equation**: on `Re s ≤ 11/2` the only zeros are the trivial ones. -/
theorem tauL_ne_zero_of_le {s : ℂ} (hs : s.re ≤ 11 / 2) (hn : ∀ n : ℕ, s ≠ -n) : tauL s ≠ 0 := by
  intro h
  have h12 := HeckeZeros.tauL_zero_twelve_sub h hn
  exact tauL_ne_zero_of_ge (s := 12 - s) (by simp; linarith) h12.1

end RamanujanTau.EdgeNonvanishing

#print axioms RamanujanTau.EdgeNonvanishing.localD_inv_eq_exp
#print axioms RamanujanTau.EdgeNonvanishing.rs_sub_zeta_bound
#print axioms RamanujanTau.EdgeNonvanishing.alpha_sq_le
#print axioms RamanujanTau.EdgeNonvanishing.rs_local
#print axioms RamanujanTau.EdgeNonvanishing.one_le_norm_Fval
#print axioms RamanujanTau.EdgeNonvanishing.tauL_ne_zero_edge
#print axioms RamanujanTau.EdgeNonvanishing.tauL_ne_zero_of_ge
#print axioms RamanujanTau.EdgeNonvanishing.tauL_ne_zero_of_le
