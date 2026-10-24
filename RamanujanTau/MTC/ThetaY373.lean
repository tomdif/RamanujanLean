/-
# `θ_{3,4}(x*, y*)` as a theta product

From `thV_xstar` (`thV = 2 j(Q³;Q¹²) S`), with `K_a = j(−Q^a; Q⁸⁰)` and `J_{a,m} = j(Q^a; Q^m)` (`Q = t^{168}`):

* `C1`: `Q J̄₄J̄₁₄ − J̄₆J̄₁₆ = −J_{1,20} J_{5,20}`, `C2`: `J̄₁₄J̄₁₆ − Q⁵ J̄₄J̄₆ = J_{5,20} J_{9,20}`
  (HM (1.4b) then (1.2f) with `m = 2`);
* `c12a`, `c12b`: `J_{1,20} j(−Q;Q²⁰) = J_{2,40} J_{20,40}`, `J_{9,20} j(−Q⁹;Q²⁰) = J_{18,40} J_{20,40}` (HM (1.2c));
* `dD`: `j(−Q⁹;Q²⁰) − Q² j(−Q;Q²⁰) = J_{2,5}` (HM (1.2f));

hence `S · Q² J̄₄J̄₆J̄₁₄J̄₁₆ · J_{20,40} = −J_{5,20} J_{1,20} J_{9,20} J_{2,5}` (`S_prod`).
-/
import RamanujanTau.MTC.ThetaX373
import RamanujanTau.MTC.ThetaMul
import RamanujanTau.MTC.GX373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma h840 : 1 ≤ 840 := by norm_num
lemma h3360 : 1 ≤ 3360 := by norm_num
lemma h13440 : 1 ≤ 13440 := by norm_num

lemma refl_m {N : ℕ} (hN : 1 ≤ N) (e : ℤ) : θ hN (N - e) (-1) = θ hN e (-1) := by
  have h := θ_reflect hN e (by norm_num : (-1 : ℂ) ≠ 0)
  rwa [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h

lemma inv_m {N : ℕ} (hN : 1 ≤ N) (e : ℤ) : θ hN (-e) (-1) = -mono (-e) (-1) * θ hN e (-1) := by
  have h := θ_inv hN e (by norm_num : (-1 : ℂ) ≠ 0)
  rwa [show ((-1 : ℂ))⁻¹ = -1 by norm_num] at h

/-- `K_a = j(−Q^a; Q⁸⁰)`, `J20 a = j(Q^a; Q²⁰)`, `B20 a = j(−Q^a; Q²⁰)`. -/
noncomputable def K80 (a : ℤ) : L := θ h13440 (168 * a) (-1)
noncomputable def J20 (a : ℤ) : L := θ h3360 (168 * a) 1
noncomputable def B20 (a : ℤ) : L := θ h3360 (168 * a) (-1)
noncomputable def J5 (a : ℤ) : L := θ h840 (168 * a) 1

/-- the base change `2·6720 = 13440`. -/
lemma b13440 (e : ℤ) (c : ℂ) : θ (h2N (h160 hqT)) e c = θ h13440 e c := θ_N' (by norm_num) _ _ e c
lemma b13440' (e : ℤ) (c : ℂ) : θ (hN' h3360 2 two_pos) e c = θ h13440 e c := θ_N' (by norm_num) _ _ e c
lemma b6720 (e : ℤ) (c : ℂ) : θ (h2N h3360) e c = θ (h160 hqT) e c := θ_N' (by norm_num) _ _ e c
lemma b3360 (e : ℤ) (c : ℂ) : θ (hN' h840 2 two_pos) e c = θ h3360 e c := θ_N' (by norm_num) _ _ e c

lemma Kref (a : ℤ) : θ h13440 (13440 - 168 * a) (-1) = K80 a := by
  have := refl_m h13440 (168 * a); push_cast at this; exact this

/-! ## the two products of `J̄`'s -/

lemma prod_4_14 : jB 4 * jB 14 = K80 18 * K80 30 - mono 672 (-1) * (K80 22 * K80 10) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (9744 : ℤ) = 13440 - 168 * 22 by norm_num, Kref, show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_6_16 : jB 6 * jB 16 = K80 22 * K80 30 - mono 1008 (-1) * (K80 18 * K80 10) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (10416 : ℤ) = 13440 - 168 * 18 by norm_num, Kref, show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_14_16 : jB 14 * jB 16 = K80 30 * K80 38 - mono 2352 (-1) * (K80 10 * K80 2) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref, show (13104 : ℤ) = 13440 - 168 * 2 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_4_6 : jB 4 * jB 6 = K80 10 * K80 38 - mono 672 (-1) * (K80 30 * K80 2) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (8400 : ℤ) = 13440 - 168 * 30 by norm_num, Kref, show (13104 : ℤ) = 13440 - 168 * 2 by norm_num, Kref]
  unfold K80; norm_num

/-! ## the `m = 2` dissections in base `Q²⁰` -/

lemma dis_1 : J20 1 = K80 22 - mono 168 1 * K80 18 := by
  unfold J20
  rw [dissect2 h3360 _ one_ne_zero]
  simp only [b13440']
  norm_num
  rw [show (-3024 : ℤ) = -(3024) by norm_num, inv_m]
  unfold K80
  have e : (single (3192:ℤ) (1:ℂ) : L) * mono (-3024) (-1) = -mono 168 1 := by
    rw [show (single (3192:ℤ) (1:ℂ) : L) = mono 3192 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 22 = 3696 by norm_num, show (168:ℤ) * 18 = 3024 by norm_num]
  linear_combination (θ h13440 3024 (-1)) * e

lemma dis_5 : J20 5 = K80 30 - mono 840 1 * K80 10 := by
  unfold J20
  rw [dissect2 h3360 _ one_ne_zero]
  simp only [b13440']
  norm_num
  rw [show (-1680 : ℤ) = -(1680) by norm_num, inv_m]
  unfold K80
  have e : (single (2520:ℤ) (1:ℂ) : L) * mono (-1680) (-1) = -mono 840 1 := by
    rw [show (single (2520:ℤ) (1:ℂ) : L) = mono 2520 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 30 = 5040 by norm_num, show (168:ℤ) * 10 = 1680 by norm_num]
  linear_combination (θ h13440 1680 (-1)) * e

lemma dis_9 : J20 9 = K80 38 - mono 1512 1 * K80 2 := by
  unfold J20
  rw [dissect2 h3360 _ one_ne_zero]
  simp only [b13440']
  norm_num
  rw [show (-336 : ℤ) = -(336) by norm_num, inv_m]
  unfold K80
  have e : (single (1848:ℤ) (1:ℂ) : L) * mono (-336) (-1) = -mono 1512 1 := by
    rw [show (single (1848:ℤ) (1:ℂ) : L) = mono 1848 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 38 = 6384 by norm_num, show (168:ℤ) * 2 = 336 by norm_num]
  linear_combination (θ h13440 336 (-1)) * e

lemma C1 : mono 168 1 * (jB 4 * jB 14) - jB 6 * jB 16 = -(J20 1 * J20 5) := by
  rw [prod_4_14, prod_6_16, dis_1, dis_5]
  have h1 : (mono 168 1 : L) * mono 672 (-1) = mono 840 (-1) := by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have h2 : (mono 840 1 : L) * mono 168 1 = mono 1008 1 := by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have h3 : (mono 840 (-1) : L) = -mono 840 1 := by rw [neg_mono_x]
  have h4 : (mono 1008 (-1) : L) = -mono 1008 1 := by rw [neg_mono_x]
  linear_combination (-(K80 22 * K80 10)) * h1 + (K80 10 * K80 18) * h2 - (K80 22 * K80 10) * h3 +
    (K80 18 * K80 10) * h4

lemma C2 : jB 14 * jB 16 - mono 840 1 * (jB 4 * jB 6) = J20 5 * J20 9 := by
  rw [prod_14_16, prod_4_6, dis_5, dis_9]
  have h1 : (mono 840 1 : L) * mono 672 (-1) = mono 1512 (-1) := by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have h2 : (mono 840 1 : L) * mono 1512 1 = mono 2352 1 := by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have h3 : (mono 1512 (-1) : L) = -mono 1512 1 := by rw [neg_mono_x]
  have h4 : (mono 2352 (-1) : L) = -mono 2352 1 := by rw [neg_mono_x]
  linear_combination (K80 30 * K80 2) * h1 - (K80 10 * K80 2) * h2 + (K80 30 * K80 2) * h3 -
    (K80 10 * K80 2) * h4

/-! ## HM (1.2c) and the last dissection -/

lemma θ6720_qpow : θ (h160 hqT) 6720 1 = 0 := by
  rw [show (6720 : ℤ) = ((160 * 42 : ℕ) : ℤ) * 1 by norm_num]; exact θ_qpow (h160 hqT) 1

lemma c12a : J20 1 * B20 1 = jA 2 * jA 20 := by
  unfold J20 B20
  rw [θ_mul h3360 _ _ one_ne_zero (by norm_num)]
  simp only [b6720]
  norm_num
  rw [θ6720_qpow]
  unfold jA; norm_num

lemma c12b : J20 9 * B20 9 = jA 18 * jA 20 := by
  unfold J20 B20
  rw [θ_mul h3360 _ _ one_ne_zero (by norm_num)]
  simp only [b6720]
  norm_num
  rw [θ6720_qpow]
  unfold jA; norm_num

lemma dD : J5 2 = B20 9 - mono 336 1 * B20 1 := by
  unfold J5
  rw [dissect2 h840 _ one_ne_zero]
  simp only [b3360]
  norm_num
  rw [show (-168 : ℤ) = -(168) by norm_num, inv_m]
  unfold B20
  have e : (single (504:ℤ) (1:ℂ) : L) * mono (-168) (-1) = -mono 336 1 := by
    rw [show (single (504:ℤ) (1:ℂ) : L) = mono 504 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 9 = 1512 by norm_num, show (168:ℤ) * 1 = 168 by norm_num]
  linear_combination (θ h3360 168 (-1)) * e

/-- **the bracket**: `(Q² J_{2,40} J_{9,20} − J_{18,40} J_{1,20}) J_{20,40} = −J_{1,20} J_{9,20} J_{2,5}`. -/
lemma Bk : (mono 336 1 * jA 2 * J20 9 - jA 18 * J20 1) * jA 20 = -(J20 1 * J20 9 * J5 2) := by
  rw [dD]
  linear_combination (-(mono 336 1 * J20 9)) * c12a + J20 1 * c12b

/-! ## monomials as powers of `Q` -/

noncomputable def Qm : L := mono 168 1

lemma Qm_ne : Qm ≠ 0 := by unfold Qm; simp [mono]

lemma Qm_pow (k : ℕ) : (mono (168 * k) 1 : L) = Qm ^ k := by
  unfold Qm
  show (single (168 * (k : ℤ)) (1 : ℂ) : L) = single 168 1 ^ k
  rw [single_pow, one_pow, nsmul_eq_mul, mul_comm]

lemma m336 : (mono 336 1 : L) = Qm ^ 2 := by rw [show (336 : ℤ) = 168 * ((2 : ℕ) : ℤ) by norm_num, Qm_pow]
lemma m840 : (mono 840 1 : L) = Qm ^ 5 := by rw [show (840 : ℤ) = 168 * ((5 : ℕ) : ℤ) by norm_num, Qm_pow]

lemma mneg (k : ℕ) : (mono (-(168 * k)) 1 : L) = (Qm ^ k)⁻¹ := by
  rw [← Qm_pow]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mono_mul]
  show mono _ _ = mono 0 1
  exact mono_ext (by ring) (by norm_num)

lemma mneg168 : (mono (-168) 1 : L) = Qm⁻¹ := by
  have := mneg 1; rw [pow_one] at this; rw [← this]; exact mono_ext (by norm_num) rfl
lemma mneg336 : (mono (-336) 1 : L) = (Qm ^ 2)⁻¹ := by
  rw [← mneg 2]; exact mono_ext (by norm_num) rfl

/-- **`S` as a product**. -/
theorem S_prod :
    (mono (-168) 1 * jA 18 / (jB 6 * jB 16) + jA 2 / (jB 4 * jB 6) -
      mono 840 1 * jA 2 / (jB 14 * jB 16) - mono (-336) 1 * jA 18 / (jB 14 * jB 4)) *
      (mono 336 1 * (jB 4 * jB 6 * jB 14 * jB 16) * jA 20) = -(J20 5 * J20 1 * J20 9 * J5 2) := by
  have hb : ∀ a : ℤ, jB a ≠ 0 := fun a => by
    unfold jB
    exact θ_ne_zero (h160 hqT) (by norm_num) fun _ _ => by norm_num
  have h4 := hb 4; have h6 := hb 6; have h14 := hb 14; have h16 := hb 16
  have hQ := Qm_ne
  have hC1 := C1
  have hC2 := C2
  have hB := Bk
  rw [show (mono 168 1 : L) = Qm from rfl] at hC1
  rw [m840] at hC2
  rw [m336] at hB
  rw [mneg168, m840, mneg336, m336]
  have e1 : (Qm⁻¹ * jA 18 / (jB 6 * jB 16) + jA 2 / (jB 4 * jB 6) - Qm ^ 5 * jA 2 / (jB 14 * jB 16) -
      (Qm ^ 2)⁻¹ * jA 18 / (jB 14 * jB 4)) * (Qm ^ 2 * (jB 4 * jB 6 * jB 14 * jB 16) * jA 20) =
      (jA 18 * (Qm * (jB 4 * jB 14) - jB 6 * jB 16) + Qm ^ 2 * jA 2 * (jB 14 * jB 16 - Qm ^ 5 * (jB 4 * jB 6))) *
        jA 20 := by
    field_simp
    ring
  rw [e1, hC1, hC2]
  linear_combination J20 5 * hB

end MTC
