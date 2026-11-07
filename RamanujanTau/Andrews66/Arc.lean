/-
# Andrews 1966, M-c (second half): one Farey arc, conditional on `Hb`

Line `Im τ = y = 1/N²`, arc of `h/K` (`K ≤ N`) of half-widths `a₁ = 1/(K(K+k_p))`, `a₂ = 1/(K(K+k_n))`
(both in `[θ₀, 1/(KN))`, `θ₀ = 1/(2KN)`). With `z = K(y − iφ)`:

* on the whole arc `Re(1/z) ≥ K/2` (`re_inv_ge`), so `Hb` applies and `b(q') = 1 + O(e^{−π})`;
* `f(q)e^{−2πinτ} = e^{−2πinh/K}·[ε_K ω_b m(φ) + O(E·(C‖z‖^{−D} + C_b‖z‖^{−1/2}))]` (`pt_bound`),
  `E = e^{2πny}`;
* off the core `|φ| ≥ θ₀`: `Re(1/z) ≤ 4K`, so `|m(φ)| ≤ E e^{π/3}‖z‖^{−1/2}` (`mI_off`);
* on the core `|φ| ≤ θ₀`: `core_eval`, with `c ≤ π/3`, `s ≥ 1/10`, `Yc/(c²+s²) ≤ 2πny`.

`arc_bound`: `‖∫_{arc} f(e^{2πiτ})e^{−2πinτ}dx − e^{−2πinh/K} ε_K ω_b(h,K/2) M_K(n)‖ ≤ Barc`.
-/
import RamanujanTau.Andrews66.ArcMain
import RamanujanTau.Andrews66.Circle

set_option autoImplicit false

namespace Andrews66
open Complex Filter Metric MeasureTheory Set intervalIntegral
open scoped Real Topology Interval

noncomputable section

/-! ### the shift `x = h/K + φ` -/

lemma qp_zK (h K : ℕ) (hK : 0 < K) (y φ : ℝ) :
    Rademacher.qp h K (zK K y φ) = cexp (2 * π * I * tau y ((h : ℝ) / K + φ)) := by
  unfold Rademacher.qp zK tau
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

lemma gI_shift (n h K : ℕ) (hK : 0 < K) (y φ : ℝ) :
    gI n y ((h : ℝ) / K + φ) = cexp (-(2 * π * I * n * h / K)) *
      (fA (Rademacher.qp h K (zK K y φ)) * cexp (2 * π * n * zK K y φ / K)) := by
  rw [gI, qp_zK h K hK]
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have e : cexp (-(2 * π * I * n * tau y ((h : ℝ) / K + φ))) =
      cexp (-(2 * π * I * n * h / K)) * cexp (2 * π * n * zK K y φ / K) := by
    rw [← Complex.exp_add]
    congr 1
    unfold tau zK
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [e]; ring

lemma norm_eh (n h K : ℕ) : ‖cexp (-(2 * π * I * n * h / K))‖ = 1 := by
  rw [norm_exp]
  have : (-(2 * π * I * n * h / K)).re = 0 := by
    rw [show -(2 * π * I * n * h / K) = ((-(2 * π * n * h / K)) : ℝ) * I by push_cast; ring, re_ofReal_mul]
    simp
  rw [this, Real.exp_zero]

/-! ### norms -/

lemma norm_sqrt_eq {z : ℂ} : ‖Complex.sqrt z‖ = √‖z‖ := by
  rw [Complex.sqrt, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_real,
    Real.sqrt_eq_rpow]
  norm_num

lemma norm_cexp_nz (K n : ℕ) (hK : 0 < K) (y φ : ℝ) :
    ‖cexp (2 * π * n * zK K y φ / K)‖ = Real.exp (2 * π * n * y) := by
  rw [norm_exp]
  congr 1
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [show (2 * π * n * zK K y φ / K : ℂ) = ((2 * π * n / K : ℝ) : ℂ) * zK K y φ by push_cast; ring,
    re_ofReal_mul, zK_re]
  field_simp

lemma norm_cexp_main (K : ℕ) (z : ℂ) :
    ‖cexp (π * (1 / z - z) / (12 * K))‖ = Real.exp (π * ((1 / z).re - z.re) / (12 * K)) := by
  rw [norm_exp]
  congr 1
  rw [show (π * (1 / z - z) / (12 * K) : ℂ) = ((π / (12 * K) : ℝ) : ℂ) * (1 / z - z) by push_cast; ring,
    re_ofReal_mul, sub_re]
  ring

lemma norm_qp' (h' : ℤ) {K : ℕ} (hK : 0 < K) (w : ℂ) :
    ‖Rademacher.qp h' K w‖ = Real.exp (-(2 * π * w.re / K)) := by
  rw [Rademacher.qp, norm_exp]
  congr 1
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [show (2 * π * I * ((h' + I * w) / K)) = ((2 * π / K : ℝ) : ℂ) * (I * h' - w) by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring, re_ofReal_mul]
  simp; ring

lemma re_inv_zK {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) (φ : ℝ) :
    (1 / zK K y φ).re = y / (K * (y ^ 2 + φ ^ 2)) := by
  rw [one_div, inv_re, normSq_zK, zK_re]
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have : 0 < y ^ 2 + φ ^ 2 := by positivity
  field_simp

lemma norm_zK_ge (K : ℕ) (y φ : ℝ) : (K : ℝ) * y ≤ ‖zK K y φ‖ := by
  have := Complex.abs_re_le_norm (zK K y φ)
  rw [zK_re] at this
  exact (le_abs_self _).trans this

lemma norm_omegaB_le (h k : ℕ) : ‖omegaB h k‖ ≤ 1 := by
  unfold omegaB
  split_ifs with hx
  · exact le_of_eq (Classical.choose_spec hx).1
  · simp

lemma norm_epsK_le (K : ℕ) : ‖epsK K‖ ≤ 1 := by
  unfold epsK; split_ifs <;> simp

/-! ### pointwise bounds -/

/-- the `b`-part at an even cusp: `‖b(q) − ω_b z^{−1/2} e^{π(1/z−z)/(24k)}‖ ≤ C_b ‖z‖^{−1/2}`. -/
lemma b_main_pt {h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h (2 * k)) {h' : ℤ}
    (hh' : ((2 * k : ℕ) : ℤ) ∣ h * h' + 1) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hbn : ∀ q : ℂ, ‖q‖ ≤ 1 / 2 → ‖bE q - 1‖ ≤ Cb * ‖q‖) {z : ℂ} (hz : 0 < z.re) (hR : (k : ℝ) ≤ (1 / z).re) :
    ‖bE (Rademacher.qp h (2 * k) z) - omegaB h k / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k))‖ ≤
      Cb * (√‖z‖)⁻¹ := by
  obtain ⟨hω, hT⟩ := omegaB_spec hk hcop
  rw [hT h' hh' z hz]
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hk2 : 0 < 2 * k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  set R := (1 / z).re
  have hq : ‖Rademacher.qp h' (2 * k) (1 / z)‖ = Real.exp (-(π * R / k)) := by
    rw [norm_qp' h' hk2]; congr 1; push_cast; field_simp
    try rfl
  have hq2 : ‖Rademacher.qp h' (2 * k) (1 / z)‖ ≤ 1 / 2 := by
    rw [hq]
    calc Real.exp (-(π * R / k)) ≤ Real.exp (-π) := by
          apply Real.exp_le_exp.mpr
          rw [neg_le_neg_iff, le_div_iff₀ hkr]; nlinarith [Real.pi_pos]
      _ ≤ 1 / 2 := by
          have := Real.add_one_le_exp π
          rw [Real.exp_neg]
          rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          linarith [Real.pi_gt_three]
  have hb := hbn _ hq2
  have e : omegaB h k / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) * bE (Rademacher.qp h' (2 * k) (1 / z)) -
      omegaB h k / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) =
      omegaB h k / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) *
        (bE (Rademacher.qp h' (2 * k) (1 / z)) - 1) := by ring
  rw [e, norm_mul, norm_mul, norm_div, hω, norm_sqrt_eq, one_div]
  have hE : ‖cexp (π * (1 / z - z) / (24 * k))‖ ≤ Real.exp (π * R / (24 * k)) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    rw [show (π * (1 / z - z) / (24 * k) : ℂ) = ((π / (24 * k) : ℝ) : ℂ) * (1 / z - z) by push_cast; ring,
      re_ofReal_mul, sub_re]
    have : 0 ≤ π / (24 * k) * z.re := by positivity
    have e2 : π * R / (24 * k) = π / (24 * k) * R := by ring
    rw [e2]; nlinarith
  have hsz : 0 < √‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0)
  calc (√‖z‖)⁻¹ * ‖cexp (π * (1 / z - z) / (24 * k))‖ * ‖bE (Rademacher.qp h' (2 * k) (1 / z)) - 1‖
      ≤ (√‖z‖)⁻¹ * Real.exp (π * R / (24 * k)) * (Cb * Real.exp (-(π * R / k))) := by
        gcongr
        exact hb.trans (by rw [hq])
    _ = Cb * (√‖z‖)⁻¹ * Real.exp (π * R / (24 * k) - π * R / k) := by
        rw [Real.exp_sub, Real.exp_neg]; field_simp
    _ ≤ Cb * (√‖z‖)⁻¹ * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]
        have : 0 ≤ R := by linarith
        have : π * R / (24 * k) ≤ π * R / k := by
          apply div_le_div_of_nonneg_left (by positivity) hkr (by linarith)
        linarith
    _ = _ := by ring

/-- **the pointwise bound on an arc** (any `K`): with `X = e^{2πnz/K}`,
`‖f(q)X − ε_K ω_b m‖ ≤ ‖X‖ (C‖z‖^{−D} + C_b‖z‖^{−1/2})`. -/
lemma pt_bound {C D Cb : ℝ} (hHb : Hb C D) (hCb : 0 ≤ Cb)
    (hbn : ∀ q : ℂ, ‖q‖ ≤ 1 / 2 → ‖bE q - 1‖ ≤ Cb * ‖q‖) {h K : ℕ} (hK : 0 < K) (hcop : Nat.Coprime h K)
    {h' : ℤ} (hh' : (K : ℤ) ∣ h * h' + 1) {z : ℂ} (hz : 0 < z.re) (hR : (K : ℝ) / 2 ≤ (1 / z).re) (X : ℂ) :
    ‖fA (Rademacher.qp h K z) * X - epsK K * omegaB h (K / 2) *
        (1 / Complex.sqrt z * cexp (π * (1 / z - z) / (12 * K)) * X)‖ ≤
      ‖X‖ * (C * ‖z‖ ^ (-D) + Cb * (√‖z‖)⁻¹) := by
  have e : fA (Rademacher.qp h K z) * X - epsK K * omegaB h (K / 2) *
        (1 / Complex.sqrt z * cexp (π * (1 / z - z) / (12 * K)) * X) =
      X * ((fA (Rademacher.qp h K z) - epsK K * bE (Rademacher.qp h K z)) + epsK K *
        (bE (Rademacher.qp h K z) - omegaB h (K / 2) / Complex.sqrt z * cexp (π * (1 / z - z) / (12 * K)))) := by
    ring
  rw [e, norm_mul]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add (hHb K hK h hcop z hz hR) ?_)
  rw [norm_mul]
  by_cases hev : Even K
  · obtain ⟨k, rfl⟩ := hev
    have hk : 0 < k := by omega
    rw [show k + k = 2 * k by ring] at *
    have hk2 : 2 * k / 2 = k := by omega
    rw [hk2]
    have h24 : (12 * ((2 * k : ℕ) : ℂ)) = 24 * (k : ℂ) := by push_cast; ring
    rw [h24]
    have hb := b_main_pt hk hcop hh' hCb hbn hz (by push_cast at hR; linarith)
    calc ‖epsK (2 * k)‖ * _ ≤ 1 * (Cb * (√‖z‖)⁻¹) := by
          gcongr
          · exact norm_epsK_le _
    _ = _ := one_mul _
  · have : epsK K = 0 := by unfold epsK; rw [if_neg hev]
    rw [this, norm_zero, zero_mul]
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
    have : 0 < √‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0)
    positivity

/-- off the core the main integrand is bounded. -/
lemma mI_off {K n : ℕ} (hK : 0 < K) {y φ : ℝ} (hy : 0 < y) (hR : (1 / zK K y φ).re ≤ 4 * K) :
    ‖mI K n y φ‖ ≤ Real.exp (2 * π * n * y) * Real.exp (π / 3) * (√‖zK K y φ‖)⁻¹ := by
  unfold mI
  rw [norm_mul, norm_mul, norm_cexp_nz K n hK, norm_cexp_main, norm_div, norm_one, norm_sqrt_eq, one_div]
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have : Real.exp (π * ((1 / zK K y φ).re - (zK K y φ).re) / (12 * K)) ≤ Real.exp (π / 3) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    have : 0 < (zK K y φ).re := zK_re_pos hK hy φ
    nlinarith [Real.pi_pos]
  have h0 : 0 ≤ (√‖zK K y φ‖)⁻¹ := by positivity
  calc (√‖zK K y φ‖)⁻¹ * Real.exp (π * ((1 / zK K y φ).re - (zK K y φ).re) / (12 * K)) *
        Real.exp (2 * π * n * y)
      ≤ (√‖zK K y φ‖)⁻¹ * Real.exp (π / 3) * Real.exp (2 * π * n * y) := by gcongr
    _ = _ := by ring

/-! ### the geometry with `y = 1/N²` -/

lemma re_inv_ge {K N : ℕ} (hK : 0 < K) (hKN : K ≤ N) {φ : ℝ} (hφ : |φ| ≤ 1 / (K * N)) :
    (K : ℝ) / 2 ≤ (1 / zK K (1 / (N : ℝ) ^ 2) φ).re := by
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hN : (0 : ℝ) < N := by linarith
  rw [re_inv_zK hK (by positivity)]
  have hφ2 : φ ^ 2 ≤ 1 / ((K : ℝ) ^ 2 * N ^ 2) := by
    rw [← sq_abs]; calc |φ| ^ 2 ≤ (1 / (K * N)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hφ 2
      _ = _ := by rw [div_pow, mul_pow, one_pow]
  have hy2 : (1 / (N : ℝ) ^ 2) ^ 2 ≤ 1 / ((K : ℝ) ^ 2 * N ^ 2) := by
    rw [div_pow, one_pow, ← pow_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have : (K : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hkr.le hNr 2
    rw [show (N : ℝ) ^ (2 * 2) = N ^ 2 * N ^ 2 by ring]
    nlinarith [sq_nonneg (N : ℝ)]
  set S := (1 / (N : ℝ) ^ 2) ^ 2 + φ ^ 2
  have hS : S ≤ 2 / ((K : ℝ) ^ 2 * N ^ 2) := by
    have : S ≤ 1 / ((K : ℝ) ^ 2 * N ^ 2) + 1 / ((K : ℝ) ^ 2 * N ^ 2) := add_le_add hy2 hφ2
    linarith [show 1 / ((K : ℝ) ^ 2 * N ^ 2) + 1 / ((K : ℝ) ^ 2 * N ^ 2) = 2 / ((K : ℝ) ^ 2 * N ^ 2) by ring]
  have hS0 : 0 < S := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc (K : ℝ) / 2 * (K * S) ≤ (K : ℝ) / 2 * (K * (2 / ((K : ℝ) ^ 2 * N ^ 2))) := by gcongr
    _ = 1 / (N : ℝ) ^ 2 := by field_simp

lemma re_inv_le {K N : ℕ} (hK : 0 < K) (hKN : K ≤ N) {φ : ℝ} (hφ : 1 / (2 * K * N) ≤ |φ|) :
    (1 / zK K (1 / (N : ℝ) ^ 2) φ).re ≤ 4 * K := by
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hN : (0 : ℝ) < N := by linarith
  rw [re_inv_zK hK (by positivity)]
  have hφ2 : 1 / (4 * (K : ℝ) ^ 2 * N ^ 2) ≤ φ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (2 * K * N)) hφ 2
    rw [sq_abs] at h
    calc 1 / (4 * (K : ℝ) ^ 2 * N ^ 2) = (1 / (2 * K * N)) ^ 2 := by ring
      _ ≤ φ ^ 2 := h
  have hS0 : 0 < (1 / (N : ℝ) ^ 2) ^ 2 + φ ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have key : 1 / (N : ℝ) ^ 2 ≤ 4 * K ^ 2 * φ ^ 2 := by
    calc 1 / (N : ℝ) ^ 2 = 4 * K ^ 2 * (1 / (4 * (K : ℝ) ^ 2 * N ^ 2)) := by field_simp
      _ ≤ 4 * K ^ 2 * φ ^ 2 := by gcongr
  have : 0 ≤ (1 / (N : ℝ) ^ 2) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg (K : ℝ))) this]

/-- the chord parameters for `y = 1/N²`, `θ₀ = 1/(2KN)`. -/
lemma cK_eq {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    cK K (1 / (N : ℝ) ^ 2) (1 / (2 * K * N)) = π * N ^ 2 / (3 * (4 * K ^ 2 + N ^ 2)) := by
  unfold cK βK
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  ring

lemma sK_eq {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    sK K (1 / (N : ℝ) ^ 2) (1 / (2 * K * N)) = π * N ^ 3 / (6 * K * (4 * K ^ 2 + N ^ 2)) := by
  unfold sK βK
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  ring

lemma cK_le {K N : ℕ} (hK : 0 < K) (hN : 0 < N) : cK K (1 / (N : ℝ) ^ 2) (1 / (2 * K * N)) ≤ π / 3 := by
  rw [cK_eq hK hN]
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos, mul_pos Real.pi_pos (mul_pos hkr hkr)]

lemma sK_ge {K N : ℕ} (hK : 0 < K) (hKN : K ≤ N) : 1 / 10 ≤ sK K (1 / (N : ℝ) ^ 2) (1 / (2 * K * N)) := by
  have hN : 0 < N := lt_of_lt_of_le hK hKN
  rw [sK_eq hK hN]
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have h1 : (K : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hkr.le hNr 2
  have h3 : (K : ℝ) * N ^ 2 ≤ N ^ 3 := by nlinarith [sq_nonneg (N : ℝ)]
  have hπ := Real.pi_gt_three
  have : 6 * (K : ℝ) * (4 * K ^ 2 + N ^ 2) ≤ 30 * N ^ 3 := by nlinarith
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := pow_pos (by linarith) 3
  have : 30 * (N : ℝ) ^ 3 ≤ π * N ^ 3 * 10 := by nlinarith
  linarith

lemma Yc_le {K n : ℕ} (hK : 0 < K) {y θ₀ : ℝ} (hy : 0 < y) :
    YK K n * cK K y θ₀ / (cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2) ≤ 2 * π * n * y := by
  rw [cs_sq hK hy]
  have hc := cK_pos (θ₀ := θ₀) hK hy
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [mul_div_mul_right _ _ hc.ne']
  unfold YK AK βK
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [Real.pi_pos, mul_pos (mul_pos Real.pi_pos Real.pi_pos) hy]

/-- the per-arc error bound. -/
def Barc (C D Cb : ℝ) (n N K : ℕ) : ℝ :=
  2 / (K * N) * (Real.exp (2 * π * n * (1 / (N : ℝ) ^ 2)) *
    (C * ((K : ℝ) * (1 / (N : ℝ) ^ 2)) ^ (-D) + (Cb + Real.exp (π / 3)) * (√((K : ℝ) * (1 / (N : ℝ) ^ 2)))⁻¹)) +
  4 * √10 * Real.exp (π / 3) * Real.exp (2 * π * n * (1 / (N : ℝ) ^ 2)) / K

lemma mI_cont {K n : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 < y) : Continuous (mI K n y) := by
  have e : mI K n y = fun φ => ((√(βK K) : ℝ) : ℂ) / (I * K) *
      (hfun (YK K n) (zetaK K y φ) * ((βK K : ℂ) * ((K : ℂ) * I) / zK K y φ ^ 2)) := by
    funext φ; exact mI_eq hK n hy φ
  rw [e]
  refine continuous_iff_continuousAt.mpr fun φ => ?_
  refine continuousAt_const.mul (ContinuousAt.mul ?_ ?_)
  · have hre : 0 < (zetaK K y φ).re := by
      rw [zetaK_re]; have := βK_pos hK; have : (0 : ℝ) < K := by exact_mod_cast hK
      have : 0 < y ^ 2 + φ ^ 2 := by positivity
      positivity
    exact (differentiableAt_hfun _ hre).continuousAt.comp (hasDerivAt_zetaK hK hy φ).continuousAt
  · exact continuousAt_const.div ((hasDerivAt_zK K y φ).continuousAt.pow 2) (pow_ne_zero _ (zK_ne hK hy φ))

set_option maxHeartbeats 1000000 in
/-- **one Farey arc**, conditional on `Hb`. -/
theorem arc_bound {C D Cb : ℝ} (hHb : Hb C D) (hD : 0 ≤ D) (hC : 0 ≤ C) (hCb : 0 ≤ Cb)
    (hbn : ∀ q : ℂ, ‖q‖ ≤ 1 / 2 → ‖bE q - 1‖ ≤ Cb * ‖q‖) {n N h K kp kn : ℕ} (hn : 1 ≤ n) (hK : 0 < K)
    (hKN : K ≤ N) (hkp : kp ≤ N) (hkn : kn ≤ N) (hNp : N < K + kp) (hNn : N < K + kn)
    (hcop : Nat.Coprime h K) (hdvd : (K : ℤ) ∣ h * kn + 1) :
    ‖arcI n (1 / (N : ℝ) ^ 2) h K kp kn -
        cexp (-(2 * π * I * n * h / K)) * (epsK K * omegaB h (K / 2) * MK K n)‖ ≤ Barc C D Cb n N K := by
  have hN : 0 < N := lt_of_lt_of_le hK hKN
  set y : ℝ := 1 / (N : ℝ) ^ 2 with hydef
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hy : 0 < y := by positivity
  set θ₀ : ℝ := 1 / (2 * K * N) with hθdef
  have hθ : 0 < θ₀ := by positivity
  set a₁ : ℝ := 1 / (K * (K + kp)) with ha₁
  set a₂ : ℝ := 1 / (K * (K + kn)) with ha₂
  set E : ℝ := Real.exp (2 * π * n * y) with hEdef
  set eh := cexp (-(2 * π * I * n * h / K))
  set εω : ℂ := epsK K * omegaB h (K / 2) with hεω
  have hεω1 : ‖εω‖ ≤ 1 := by
    rw [hεω, norm_mul]
    calc ‖epsK K‖ * ‖omegaB h (K / 2)‖ ≤ 1 * 1 :=
          mul_le_mul (norm_epsK_le K) (norm_omegaB_le h _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- the arc in `φ`
  have hkpr : (N : ℝ) < K + kp := by exact_mod_cast hNp
  have hknr : (N : ℝ) < K + kn := by exact_mod_cast hNn
  have hkp' : (kp : ℝ) ≤ N := by exact_mod_cast hkp
  have hkn' : (kn : ℝ) ≤ N := by exact_mod_cast hkn
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have ha₁le : a₁ ≤ 1 / (K * N) := by
    rw [ha₁]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  have ha₂le : a₂ ≤ 1 / (K * N) := by
    rw [ha₂]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  have hθa₁ : θ₀ ≤ a₁ := by
    rw [ha₁, hθdef]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  have hθa₂ : θ₀ ≤ a₂ := by
    rw [ha₂, hθdef]; apply one_div_le_one_div_of_le (by positivity); nlinarith
  have hsum12 : a₁ + a₂ ≤ 2 / (K * N) := by
    have : 2 / ((K : ℝ) * N) = 1 / (K * N) + 1 / (K * N) := by ring
    linarith
  set Gs : ℝ → ℂ := fun φ => fA (Rademacher.qp h K (zK K y φ)) * cexp (2 * π * n * zK K y φ / K) with hGs
  set Mf : ℝ → ℂ := fun φ => εω * mI K n y φ with hMf
  have hshift : arcI n y h K kp kn = eh * ∫ φ in (-a₁)..a₂, Gs φ := by
    rw [arcI, ← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_add_left (fun x => gI n y x) ((h : ℝ) / K) (a := -a₁) (b := a₂)
    simp only at this
    rw [show Lend h K kp = (h : ℝ) / K + -a₁ by rw [Lend, ha₁]; ring,
      show Rend h K kn = (h : ℝ) / K + a₂ by rw [Rend, ha₂], ← this]
    exact intervalIntegral.integral_congr fun φ _ => gI_shift n h K hK y φ
  -- continuity
  have hGc : Continuous Gs := by
    have e : Gs = fun φ => cexp (2 * π * I * n * h / K) * gI n y ((h : ℝ) / K + φ) := by
      funext φ
      rw [gI_shift n h K hK y φ, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    rw [e]
    exact continuous_const.mul ((gI_cont n hy).comp (continuous_const.add continuous_id))
  have hMc : Continuous Mf := continuous_const.mul (mI_cont hK hy)
  -- the inverse of `−h` mod `K`
  have hh' : (K : ℤ) ∣ h * (kn : ℤ) + 1 := hdvd
  -- pointwise bounds
  have hB1 : ∀ φ ∈ Ι (-a₁) a₂, ‖Gs φ - Mf φ‖ ≤
      E * (C * ((K : ℝ) * y) ^ (-D) + Cb * (√((K : ℝ) * y))⁻¹) := by
    intro φ hφ
    have hφ' : |φ| ≤ 1 / (K * N) := by
      rw [Set.uIoc_of_le (by linarith)] at hφ
      rw [abs_le]; constructor <;> linarith [hφ.1, hφ.2]
    have hz := zK_re_pos hK hy φ
    have hR := re_inv_ge hK hKN hφ'
    have hp := pt_bound hHb hCb hbn hK hcop hh' hz hR (cexp (2 * π * n * zK K y φ / K))
    rw [norm_cexp_nz K n hK] at hp
    have hge := norm_zK_ge K y φ
    have hKy : 0 < (K : ℝ) * y := by positivity
    have e : Gs φ - Mf φ = fA (Rademacher.qp h K (zK K y φ)) * cexp (2 * π * n * zK K y φ / K) -
        epsK K * omegaB h (K / 2) * (1 / Complex.sqrt (zK K y φ) *
          cexp (π * (1 / zK K y φ - zK K y φ) / (12 * K)) * cexp (2 * π * n * zK K y φ / K)) := by
      simp only [hGs, hMf, mI, hεω]
    calc ‖Gs φ - Mf φ‖ ≤ E * (C * ‖zK K y φ‖ ^ (-D) + Cb * (√‖zK K y φ‖)⁻¹) := by
          rw [e]; exact hp
      _ ≤ E * (C * ((K : ℝ) * y) ^ (-D) + Cb * (√((K : ℝ) * y))⁻¹) := by
          have h1 : ‖zK K y φ‖ ^ (-D) ≤ ((K : ℝ) * y) ^ (-D) := Real.rpow_le_rpow_of_nonpos hKy hge (by linarith)
          have h2 : (√‖zK K y φ‖)⁻¹ ≤ (√((K : ℝ) * y))⁻¹ :=
            inv_anti₀ (Real.sqrt_pos.mpr hKy) (Real.sqrt_le_sqrt hge)
          have hE0 : 0 ≤ E := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 hC)
            (mul_le_mul_of_nonneg_left h2 hCb)) hE0
  have hB3 : ∀ φ, θ₀ ≤ |φ| → |φ| ≤ 1 / (K * N) → ‖Mf φ‖ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ := by
    intro φ h1 _
    have hR := re_inv_le hK hKN (φ := φ) (by rw [hθdef] at h1; exact h1)
    have hm := mI_off (n := n) hK hy hR
    have hge := norm_zK_ge K y φ
    have hKy : 0 < (K : ℝ) * y := by positivity
    calc ‖Mf φ‖ = ‖εω‖ * ‖mI K n y φ‖ := norm_mul _ _
      _ ≤ 1 * (E * Real.exp (π / 3) * (√‖zK K y φ‖)⁻¹) := mul_le_mul hεω1 hm (norm_nonneg _) zero_le_one
      _ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ := by
          rw [one_mul]; gcongr
  -- the decomposition
  have hI := fun a b => (hGc.sub hMc).intervalIntegrable (μ := volume) a b
  have hIM := fun a b => hMc.intervalIntegrable (μ := volume) a b
  have hsplit : (∫ φ in (-a₁)..a₂, Gs φ) - εω * MK K n =
      (∫ φ in (-a₁)..a₂, (Gs φ - Mf φ)) + ((∫ φ in (-a₁)..(-θ₀), Mf φ) + ∫ φ in θ₀..a₂, Mf φ) +
        εω * ((∫ φ in (-θ₀)..θ₀, mI K n y φ) - MK K n) := by
    rw [intervalIntegral.integral_sub (hGc.intervalIntegrable _ _) (hIM _ _)]
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hIM (-a₁) (-θ₀)) (hIM (-θ₀) θ₀)
    have e2 := intervalIntegral.integral_add_adjacent_intervals (hIM (-a₁) θ₀) (hIM θ₀ a₂)
    have e3 : ∫ φ in (-θ₀)..θ₀, Mf φ = εω * ∫ φ in (-θ₀)..θ₀, mI K n y φ :=
      intervalIntegral.integral_const_mul _ _
    rw [← e2, ← e1, e3]
    ring
  rw [hshift, show eh * (∫ φ in (-a₁)..a₂, Gs φ) - eh * (epsK K * omegaB h (K / 2) * MK K n) =
    eh * ((∫ φ in (-a₁)..a₂, Gs φ) - εω * MK K n) by rw [hεω]; ring, norm_mul, norm_eh, one_mul, hsplit]
  -- the four bounds
  have n1 : ‖∫ φ in (-a₁)..a₂, (Gs φ - Mf φ)‖ ≤
      E * (C * ((K : ℝ) * y) ^ (-D) + Cb * (√((K : ℝ) * y))⁻¹) * (2 / (K * N)) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hB1).trans ?_
    have hpos : 0 ≤ E * (C * ((K : ℝ) * y) ^ (-D) + Cb * (√((K : ℝ) * y))⁻¹) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpos
    rw [abs_of_nonneg (by linarith)]; linarith
  have n2 : ‖∫ φ in (-a₁)..(-θ₀), Mf φ‖ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ * (a₁ - θ₀) := by
    have hb2 : ∀ φ ∈ Ι (-a₁) (-θ₀), ‖Mf φ‖ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ := by
      intro φ hφ
      rw [Set.uIoc_of_le (by linarith)] at hφ
      apply hB3
      · rw [abs_of_neg (by linarith [hφ.2])]; linarith [hφ.2]
      · rw [abs_of_neg (by linarith [hφ.2])]; linarith [hφ.1]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb2).trans ?_
    rw [abs_of_nonneg (by linarith)]; apply le_of_eq; ring
  have n3 : ‖∫ φ in θ₀..a₂, Mf φ‖ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ * (a₂ - θ₀) := by
    have hb3 : ∀ φ ∈ Ι θ₀ a₂, ‖Mf φ‖ ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ := by
      intro φ hφ
      rw [Set.uIoc_of_le (by linarith)] at hφ
      apply hB3
      · rw [abs_of_pos (by linarith [hφ.1])]; linarith [hφ.1]
      · rw [abs_of_pos (by linarith [hφ.1])]; linarith [hφ.2]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb3).trans ?_
    rw [abs_of_nonneg (by linarith)]
  have n4 : ‖εω * ((∫ φ in (-θ₀)..θ₀, mI K n y φ) - MK K n)‖ ≤ 4 * √10 * Real.exp (π / 3) * E / K := by
    rw [norm_mul]
    refine (mul_le_mul hεω1 (core_eval hK hn hy hθ) (norm_nonneg _) zero_le_one).trans ?_
    rw [one_mul]
    have hβ1 : √(βK K) ≤ 1 := by
      rw [Real.sqrt_le_one]; unfold βK
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith [Real.pi_lt_four]
    have hc := cK_le hK hN
    have hs := sK_ge hK hKN
    have hYc := Yc_le (n := n) hK (θ₀ := θ₀) hy
    have hs0 : 0 < √(sK K y θ₀) := Real.sqrt_pos.mpr (by linarith)
    have hsq : (√(sK K y θ₀))⁻¹ ≤ √10 := by
      rw [inv_le_comm₀ hs0 (by positivity), ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by linarith)
    have hexp : Real.exp (cK K y θ₀ + YK K n * cK K y θ₀ / (cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2)) ≤
        Real.exp (π / 3) * E := by
      rw [hEdef, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    calc √(βK K) / K * (4 * Real.exp (cK K y θ₀ + YK K n * cK K y θ₀ / (cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2)) /
          √(sK K y θ₀))
        = √(βK K) * (4 * Real.exp (cK K y θ₀ + YK K n * cK K y θ₀ / (cK K y θ₀ ^ 2 + sK K y θ₀ ^ 2)) *
          (√(sK K y θ₀))⁻¹) / K := by ring
      _ ≤ 1 * (4 * (Real.exp (π / 3) * E) * √10) / K := by gcongr
      _ = _ := by ring
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add n1 ((norm_add_le _ _).trans (add_le_add n2 n3)))) n4).trans ?_
  unfold Barc
  rw [← hydef, ← hEdef]
  have hoff : E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ * (a₁ - θ₀) +
      E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ * (a₂ - θ₀) ≤
      E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ * (2 / (K * N)) := by
    rw [← mul_add]; gcongr; linarith
  have : 0 ≤ E * Real.exp (π / 3) * (√((K : ℝ) * y))⁻¹ := by positivity
  nlinarith

end

end Andrews66
