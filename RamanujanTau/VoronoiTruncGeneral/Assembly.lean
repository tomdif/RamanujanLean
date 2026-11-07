/-
# Assembly of the `L²`-truncated Voronoi formula

For `X ≤ x ≤ 2X` write (all with `r = 12`)

    S(x) − V_N(x) = [S − S_h] + [S_h − h^{−12} It_h^{12} V_M] + h^{−12} It_h^{12}(V_M − V_N)
                    + [h^{−12} It_h^{12} V_N − V_N],

where `S_h = h^{−12} Σ τ(n) It_h^{12} k₀(n,·)` is the smoothed sum (`= Δ_h^{12} W₁₂ / (12! h^{12})`).
The first bracket is a short sum (`bracket_signed`), the second is the kernel error plus the
tail `n > M` (`kB_zero_sub_main`, `norm_kB_top_le hd.one_le`), the third is controlled in `L²` by the
mean value theorem, the fourth by the Lipschitz bound of the main terms.
-/
import RamanujanTau.VoronoiTruncGeneral.Est

set_option autoImplicit false

namespace RamanujanTau.VoronoiTruncGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.VoronoiTrunc (It It_add It_const_mul It_finset_sum norm_It_le norm_It_sub_le
  integral_norm_It_sq_le continuous_It)

variable {m : ℕ} {a : ℕ → ℝ}

/-- `S(x) = Σ_{n≤x} τ(n)`. -/
noncomputable def Sre (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

/-- `bₙ = τ(n) n^{−25/4}`. -/
noncomputable def bco (m : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ := a n * (n : ℝ) ^ (-((m : ℝ) + 1 / 4))

/-- The truncated Voronoi sum `V_N(x) = x^{23/4}/(π√2) Σ_{n≤N} bₙ cos(4π√n√x − π/4)`. -/
noncomputable def Vth (m : ℕ) (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  x ^ ((m : ℝ) - 1 / 4) / (π * √2) * ∑ n ∈ Finset.Icc 1 N, bco m a n * Real.cos (th n x)

lemma continuous_Vth (hm : 1 ≤ m) (N : ℕ) : Continuous (Vth m a N) := by
  unfold Vth
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : Continuous fun y : ℝ => y ^ ((m : ℝ) - 1 / 4) := Real.continuous_rpow_const (by linarith)
  exact (this.div_const _).mul (continuous_finsetSum _ fun n _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_th n)))

lemma sum_tau_mK (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, a n * mK m n x = Vth m a N x := by
  unfold Vth mK bco
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The smoothed partial sum `S_h(x) = h^{−12} Σ τ(n) It_h^{12} k₀(n,·)(x)`. -/
noncomputable def Sh (m : ℕ) (a : ℕ → ℝ) (h x : ℝ) : ℂ := ((h ^ 12 : ℝ) : ℂ)⁻¹ * ∑' n, ac a n * It h 12 (kB m 0 n) x

lemma ac_eq (n : ℕ) : ac a n = (a n : ℂ) := rfl

/-- **Bracket**: `|S(x) − S_h(x)| ≤ Σ_{x<n≤x+12h} |τ(n)|`. -/
theorem norm_S_sub_Sh_le (hd : VData m a) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ‖(Sre a x : ℂ) - Sh m a h x‖ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 12 * h⌋₊, |a n| := by
  have hb := TauPartialSumsSharp.bracket_signed (ac a) 12 hh.le hx.le
  have hdd := (DkC_WC_eq hd (r := 12) (by norm_num) hh.le hx).tsum_eq
  set D := TauPartialSumsSharp.DkC h 12 (TauPartialSumsSharp.WC (ac a) 12) x
  have hA : TauPartialSums.A (ac a) x = (Sre a x : ℂ) := by
    unfold TauPartialSums.A Sre; push_cast
    refine Finset.sum_congr rfl fun n _ => ac_eq n
  have hf : (0 : ℝ) < Nat.factorial 12 := by positivity
  have hc0 : (0 : ℝ) < (Nat.factorial 12 : ℝ) * h ^ 12 := by positivity
  have hDeq : D = ((Nat.factorial 12 : ℝ) : ℂ) * ∑' n, ac a n * It h 12 (kB m 0 n) x := by
    have hf' : ((Nat.factorial 12 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
    rw [hdd]; field_simp
  have e : (Sre a x : ℂ) - Sh m a h x = ((((Nat.factorial 12 : ℝ) * h ^ 12 : ℝ) : ℂ))⁻¹ *
      ((((Nat.factorial 12 : ℝ) * h ^ 12 : ℝ) : ℂ) * TauPartialSums.A (ac a) x - D) := by
    rw [hA, hDeq]; unfold Sh
    have : (((Nat.factorial 12 : ℝ) * h ^ 12 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have : (h : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hh.ne')
    have hh12 : (h : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hh.ne')
    have : ((Nat.factorial 12 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
    push_cast
    field_simp
    rw [sub_div, mul_div_cancel_right₀ _ hh12]
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hb' : ‖(((Nat.factorial 12 : ℝ) * h ^ 12 : ℝ) : ℂ) * TauPartialSums.A (ac a) x - D‖ ≤
      (Nat.factorial 12 : ℝ) * h ^ 12 * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 12 * h⌋₊, |a n| := by
    have e2 : ∀ n, ‖ac a n‖ = |a n| := fun n => norm_ac n
    simp only [e2] at hb
    push_cast at hb ⊢
    exact hb
  rw [inv_mul_le_iff₀ hc0]
  exact hb'


lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] {g : ℕ → M} (h0 : g 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, g n = ∑ n ∈ Finset.range (N + 1), g n := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (N + 1)]

lemma ac_zero' (hd : VData m a) : ac a 0 = 0 := by simp [ac, hd.zero]

/-- Head/tail split of the smoothed sum. -/
lemma Sh_split (hd : VData m a) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (M : ℕ) :
    Sh m a h x = ((h ^ 12 : ℝ) : ℂ)⁻¹ * (It h 12 (fun y => ∑ n ∈ Finset.Icc 1 M, ac a n * kB m 0 n y) x +
      ∑' k, ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x) := by
  have hsum := (DkC_WC_eq hd (r := 12) (by norm_num) hh.le hx).summable
  unfold Sh
  congr 1
  rw [← hsum.sum_add_tsum_nat_add (M + 1), ← sum_Icc_eq_range (by rw [ac_zero' hd, zero_mul]) M]
  congr 1
  rw [It_finset_sum 12 _ (fun n y => ac a n * kB m 0 n y) (fun n => continuous_const.mul (continuous_kB hd.one_le 0 n))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [It_const_mul]

/-- The kernel error of the head. -/
lemma norm_EM_le (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) (M : ℕ) {y : ℝ} (hy1 : X ≤ y) (hy2 : y ≤ 3 * X) :
    ‖∑ n ∈ Finset.Icc 1 M, ac a n * (kB m 0 n y - (mK m n y : ℂ))‖ ≤
      CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * ((M : ℝ) ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 5 / 8)) := by
  have hy : 1 ≤ y := le_trans hX hy1
  have hCK : 0 ≤ CK m := by unfold CK; have := CK_nonneg m; positivity
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ n ∈ Finset.Icc 1 M, ‖ac a n * (kB m 0 n y - (mK m n y : ℂ))‖ ≤
      CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * (|a n| * (n : ℝ) ^ (-((m : ℝ) + 1 / 2))) := by
    intro n hn
    rw [norm_mul, norm_ac]
    have h1 := kB_zero_sub_main hd.one_le (Finset.mem_Icc.1 hn).1 hy
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hd.one_le
    have h2 : y ^ ((m : ℝ) - 1 / 2) ≤ (3 * X) ^ ((m : ℝ) - 1 / 2) :=
      Real.rpow_le_rpow (by linarith) hy2 (by linarith)
    have h3 : 0 ≤ (n : ℝ) ^ (-((m : ℝ) + 1 / 2)) := by positivity
    calc |a n| * ‖kB m 0 n y - (mK m n y : ℂ)‖
        ≤ |a n| * (CK m * y ^ ((m : ℝ) - 1 / 2) * (n : ℝ) ^ (-((m : ℝ) + 1 / 2))) := by gcongr
      _ ≤ |a n| * (CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * (n : ℝ) ^ (-((m : ℝ) + 1 / 2))) := by gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  have := head_sum_le hd (β := (m : ℝ) + 5 / 8) (γ := (m : ℝ) + 1 / 2) (by linarith) (by linarith) M
  convert this using 2; ring_nf

/-- One tail term. -/
lemma norm_tail_term_le (hd : VData m a) {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) {x : ℝ} (hx1 : X ≤ x)
    (hx2 : x + 12 * h ≤ 3 * X) {n : ℕ} (hn1 : 1 ≤ n) :
    ‖ac a n * It h 12 (kB m 0 n) x‖ ≤ CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
      (|a n| * (n : ℝ) ^ (-((m : ℝ) + 25 / 4))) := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hCT : 0 ≤ CT m := by unfold CT; have := CT_nonneg m; positivity
  rw [norm_mul, norm_ac]
  have hD := DkC_kB hd.one_le hh.le n 12 x hx0
  have hIt : It h 12 (kB m 0 n) x = ((2 * π : ℂ) ^ 12)⁻¹ * TauPartialSumsSharp.DkC h 12 (kB m 12 n) x := by
    rw [hD]; field_simp
  have hB : ∀ y ∈ Icc x (x + (12 : ℕ) * h), ‖kB m 12 n y‖ ≤
      CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) := by
    intro y hy
    have hy1 : 1 ≤ y := by linarith [hy.1]
    have hyX : X ≤ y := by linarith [hy.1]
    have hy3 : y ≤ 3 * X := by push_cast at hy; linarith [hy.2]
    refine (norm_kB_top_le hd.one_le hn1 hy1).trans ?_
    have h1 : y ^ (m + 6) ≤ (3 * X) ^ (m + 6) := pow_le_pow_left₀ (by linarith) hy3 (m + 6)
    have h2 : ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) ≤ ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by norm_num)
    have h3 : 0 ≤ ((n : ℝ) ^ (m + 6))⁻¹ := by positivity
    have h4 : 0 ≤ ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by positivity
    have h5 : 0 ≤ CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ := by positivity
    calc CT m * y ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ)
        ≤ CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by gcongr
      _ ≤ CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 h5
  have hDk := TauPartialSumsSharp.norm_DkC_le h hh.le 12 (kB m 12 n) x _ hB
  have hItn : ‖It h 12 (kB m 0 n) x‖ ≤
      CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) / π ^ 12 := by
    rw [hIt, norm_mul, norm_inv, norm_pow, show ‖(2 * π : ℂ)‖ = 2 * π by
      simp [abs_of_pos Real.pi_pos]]
    calc ((2 * π) ^ 12)⁻¹ * ‖TauPartialSumsSharp.DkC h 12 (kB m 12 n) x‖
        ≤ ((2 * π) ^ 12)⁻¹ * (2 ^ 12 * (CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ *
            ((n : ℝ) * X) ^ (-(1 / 4) : ℝ))) := by gcongr
      _ = _ := by field_simp
  have hBe : CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) / π ^ 12 =
      CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) * (n : ℝ) ^ (-((m : ℝ) + 25 / 4)) := by
    rw [Real.mul_rpow hn0.le hX0.le]
    have e : ((n : ℝ) ^ (m + 6))⁻¹ * (n : ℝ) ^ (-(1 / 4) : ℝ) = (n : ℝ) ^ (-((m : ℝ) + 25 / 4)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]; push_cast; ring_nf
    rw [← e]; ring
  calc |a n| * ‖It h 12 (kB m 0 n) x‖
      ≤ |a n| * (CT m * (3 * X) ^ (m + 6) * ((n : ℝ) ^ (m + 6))⁻¹ * ((n : ℝ) * X) ^ (-(1 / 4) : ℝ) /
          π ^ 12) := by gcongr
    _ = _ := by rw [hBe]; ring

/-- The tail `n > M`. -/
lemma norm_tail_le (hd : VData m a) {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (M : ℕ) {x : ℝ} (hx1 : X ≤ x)
    (hx2 : x + 12 * h ≤ 3 * X) :
    ‖∑' k, ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x‖ ≤
      CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
        (((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4)) := by
  have hCT : 0 ≤ CT m := by unfold CT; have := CT_nonneg m; positivity
  have hK : 0 ≤ CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) := by
    have : 0 < X := by linarith
    positivity
  have hb : ∀ k : ℕ, ‖ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x‖ ≤
      CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
        (|a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-((m : ℝ) + 25 / 4))) :=
    fun k => norm_tail_term_le hd hX hh hx1 hx2 (by omega)
  obtain ⟨hs, hle0⟩ := tail_sum_le hd (α := (m : ℝ) + 25 / 4) (β := (m : ℝ) + 3 / 4) (by linarith) (by linarith) M
  have hle : ∑' k : ℕ, |a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-((m : ℝ) + 25 / 4)) ≤
      ((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4) := by
    convert hle0 using 3; ring
  have hsK := hs.mul_left (CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ))
  have hsn : Summable fun k : ℕ => ‖ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hsK
  calc _ ≤ ∑' k, ‖ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ _ := hsn.tsum_le_tsum hb hsK
    _ = CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
        ∑' k : ℕ, |a (k + (M + 1))| * ((k + (M + 1) : ℕ) : ℝ) ^ (-((m : ℝ) + 25 / 4)) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hK

/-- Lipschitz bound for `V_N`. -/
lemma abs_Vth_sub_le (hd : VData m a) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) {x y : ℝ} (h1 : X ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3 * X) :
    |Vth m a N y - Vth m a N x| ≤ 1 / (π * √2) * (((m : ℝ) + 2 * π) * ((N : ℝ) * St a ((m : ℝ) + 3 / 4))) *
      (3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x) := by
  have hx1 : 1 ≤ x := le_trans hX h1
  have hV : ∀ z, Vth m a N z = 1 / (π * √2) * ∑ n ∈ Finset.Icc 1 N, bco m a n * (z ^ ((m : ℝ) - 1 / 4) * Real.cos (th n z)) := by
    intro z; unfold Vth; rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [hV, hV, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  have hb : ∀ n ∈ Finset.Icc 1 N, |bco m a n * (y ^ ((m : ℝ) - 1 / 4) * Real.cos (th n y)) -
      bco m a n * (x ^ ((m : ℝ) - 1 / 4) * Real.cos (th n x))| ≤
      ((m : ℝ) + 2 * π) * (|a n| * (n : ℝ) ^ (-((m : ℝ) - 1 / 4))) * (3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [← mul_sub, abs_mul]
    have hl := abs_main_sub_le hd.one_le n hx1 h2 h3
    have hsn : 1 ≤ √(n : ℝ) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; simpa using hn1
    have hb1 : |bco m a n| * ((m : ℝ) + 2 * π * √(n : ℝ)) ≤ ((m : ℝ) + 2 * π) * (|a n| * (n : ℝ) ^ (-((m : ℝ) - 1 / 4))) := by
      unfold bco
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ (-((m : ℝ) + 1 / 4)))]
      have e : (n : ℝ) ^ (-((m : ℝ) - 1 / 4)) = (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) * √(n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; ring_nf
      rw [e]
      have : 0 ≤ |a n| * (n : ℝ) ^ (-((m : ℝ) + 1 / 4)) := by positivity
      have hm1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : (m : ℝ) + 2 * π * √(n : ℝ) ≤ ((m : ℝ) + 2 * π) * √(n : ℝ) := by nlinarith [Real.pi_pos]
      nlinarith
    have hy0 : 0 ≤ y - x := by linarith
    calc |bco m a n| * |y ^ ((m : ℝ) - 1 / 4) * Real.cos (th n y) - x ^ ((m : ℝ) - 1 / 4) * Real.cos (th n x)|
        ≤ |bco m a n| * (((m : ℝ) + 2 * π * √(n : ℝ)) * (3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x)) := by gcongr
      _ = (|bco m a n| * ((m : ℝ) + 2 * π * √(n : ℝ))) * ((3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x)) := by ring
      _ ≤ (((m : ℝ) + 2 * π) * (|a n| * (n : ℝ) ^ (-((m : ℝ) - 1 / 4)))) *
          ((3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x)) := by gcongr
      _ = _ := by ring
  have hsum := head_sum_le hd (β := (m : ℝ) + 3 / 4) (γ := (m : ℝ) - 1 / 4) (by linarith) (by linarith) N
  rw [show (m : ℝ) + 3 / 4 - ((m : ℝ) - 1 / 4) = 1 by ring, Real.rpow_one] at hsum
  calc 1 / (π * √2) * |∑ n ∈ Finset.Icc 1 N, (bco m a n * (y ^ ((m : ℝ) - 1 / 4) * Real.cos (th n y)) -
        bco m a n * (x ^ ((m : ℝ) - 1 / 4) * Real.cos (th n x)))|
      ≤ 1 / (π * √2) * ∑ n ∈ Finset.Icc 1 N, ((m : ℝ) + 2 * π) * (|a n| * (n : ℝ) ^ (-((m : ℝ) - 1 / 4))) *
          (3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
    _ = 1 / (π * √2) * (((m : ℝ) + 2 * π) * ∑ n ∈ Finset.Icc 1 N, |a n| * (n : ℝ) ^ (-((m : ℝ) - 1 / 4))) *
          (3 * X) ^ ((m : ℝ) - 3 / 4) * (y - x) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ ≤ _ := by
        have : 0 ≤ y - x := by linarith
        gcongr


/-! ### The pointwise decomposition -/

/-- The short-sum majorant `g₁(x) = (H+1) Σ_{n≤3X} τ(n)² 1_{[n−H,n)}(x)`. -/
noncomputable def g1 (a : ℕ → ℝ) (X H x : ℝ) : ℝ :=
  (H + 1) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x

lemma g1_nonneg (X : ℝ) {H : ℝ} (hH : 0 ≤ H) (x : ℝ) : 0 ≤ g1 a X H x := by
  unfold g1
  refine mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) ?_)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma integrableOn_g1 (X H : ℝ) (lo hi : ℝ) : IntegrableOn (g1 a X H) (Ioc lo hi) := by
  have hfin : ∀ n : ℕ, (volume.restrict (Ioc lo hi)) (Ico ((n : ℝ) - H) n) ≠ ⊤ := by
    intro n
    rw [Measure.restrict_apply measurableSet_Ico]
    exact ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
  refine Integrable.const_mul (integrable_finsetSum _ fun n _ => ?_) _
  refine Integrable.const_mul ?_ _
  exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))

lemma integral_g1_le {X H : ℝ} (hX : 0 < X) (hH : 0 ≤ H) :
    ∫ x in Ioc X (2 * X), g1 a X H x ≤ (H + 1) * H * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 := by
  have hfin : ∀ n : ℕ, (volume.restrict (Ioc X (2 * X))) (Ico ((n : ℝ) - H) n) ≠ ⊤ := by
    intro n
    rw [Measure.restrict_apply measurableSet_Ico]
    exact ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
  unfold g1
  rw [integral_const_mul, integral_finsetSum _ (fun n _ => Integrable.const_mul
    ((integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))) _),
    mul_assoc]
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have : volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ H := by
    calc volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ volume.real (Ico ((n : ℝ) - H) n) :=
          measureReal_mono inter_subset_left (by simp)
      _ = H := by rw [Real.volume_real_Ico_of_le (by linarith)]; ring
  rw [mul_comm H]
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

/-- The bound `B₂` on the kernel error plus the tail. -/
noncomputable def B2 (m : ℕ) (a : ℕ → ℝ) (X h : ℝ) (M : ℕ) : ℝ :=
  CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * ((M : ℝ) ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 5 / 8)) +
    (h ^ 12)⁻¹ * (CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
      (((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4)))

/-- The bound `B₄` on the smoothing error of `V_N`. -/
noncomputable def B4 (m : ℕ) (a : ℕ → ℝ) (X h : ℝ) (N : ℕ) : ℝ :=
  1 / (π * √2) * (((m : ℝ) + 2 * π) * ((N : ℝ) * St a ((m : ℝ) + 3 / 4))) * (3 * X) ^ ((m : ℝ) - 3 / 4) * (12 * h)

lemma continuous_EM (hd : VData m a) (M : ℕ) : Continuous fun y : ℝ =>
    ∑ n ∈ Finset.Icc 1 M, ac a n * (kB m 0 n y - (mK m n y : ℂ)) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul ((continuous_kB hd.one_le 0 n).sub
    (continuous_ofReal.comp (continuous_mK hd.one_le n)))

/-- **Pointwise decomposition.** -/
theorem pointwise_bound (hd : VData m a) {X h : ℝ} {N M : ℕ} (hX : 1 ≤ X) (hh : 0 < h) (h12 : 12 * h ≤ X)
    {x : ℝ} (hx : x ∈ Ioc X (2 * X)) :
    (Sre a x - Vth m a N x) ^ 2 ≤ 4 * (g1 a X (12 * h) x + B2 m a X h M ^ 2 +
      ‖((h ^ 12 : ℝ) : ℂ)⁻¹ * It h 12 (fun y => ((Vth m a M y - Vth m a N y : ℝ) : ℂ)) x‖ ^ 2 + B4 m a X h N ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hx1 : X ≤ x := hx.1.le
  have hx0 : 0 < x := by linarith
  have hx3 : x + 12 * h ≤ 3 * X := by linarith [hx.2]
  have hh12 : (0 : ℝ) < h ^ 12 := pow_pos hh 12
  have hc : (((h ^ 12 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hh12.ne'
  set VM : ℝ → ℂ := fun y => ((Vth m a M y : ℝ) : ℂ)
  set VN : ℝ → ℂ := fun y => ((Vth m a N y : ℝ) : ℂ)
  set EM : ℝ → ℂ := fun y => ∑ n ∈ Finset.Icc 1 M, ac a n * (kB m 0 n y - (mK m n y : ℂ))
  set D : ℝ → ℂ := fun y => ((Vth m a M y - Vth m a N y : ℝ) : ℂ)
  have hVMc : Continuous VM := continuous_ofReal.comp (continuous_Vth hd.one_le M)
  have hVNc : Continuous VN := continuous_ofReal.comp (continuous_Vth hd.one_le N)
  have hDc : Continuous D := continuous_ofReal.comp ((continuous_Vth hd.one_le M).sub (continuous_Vth hd.one_le N))
  have hEMc : Continuous EM := continuous_EM hd M
  -- the head is `V_M + E_M`
  have hhead : (fun y => ∑ n ∈ Finset.Icc 1 M, ac a n * kB m 0 n y) = fun y => VM y + EM y := by
    funext y
    simp only [VM, EM]
    rw [← sum_tau_mK]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ac_eq]; push_cast; ring
  have hItVM : It h 12 (fun y => VM y + EM y) x = It h 12 VM x + It h 12 EM x := by
    rw [It_add 12 VM EM hVMc hEMc]
  have hVMsplit : (fun y => VM y) = fun y => VN y + D y := by
    funext y; simp only [VM, VN, D]; push_cast; ring
  have hItVN : It h 12 VM x = It h 12 VN x + It h 12 D x := by
    have := congrFun (It_add (h := h) 12 VN D hVNc hDc) x
    rw [← this]; congr 1
  -- decomposition
  set T := ∑' k, ac a (k + (M + 1)) * It h 12 (kB m 0 (k + (M + 1))) x
  have hsplit := Sh_split hd hh hx0 M
  rw [hhead, hItVM, hItVN] at hsplit
  have hdec : ((Sre a x - Vth m a N x : ℝ) : ℂ) =
      ((Sre a x : ℂ) - Sh m a h x) + ((((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EM x + (((h ^ 12 : ℝ) : ℂ))⁻¹ * T) +
      (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 D x + ((((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x) := by
    rw [hsplit]; simp only [VN]; push_cast; ring
  -- the four bounds
  have hb1 := norm_S_sub_Sh_le hd hh hx0
  have hb1' : ‖(Sre a x : ℂ) - Sh m a h x‖ ^ 2 ≤ g1 a X (12 * h) x := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hb1 2).trans ?_
    exact short_sq_pointwise hX0 (by positivity) h12 hx
  have hbE : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EM x‖ ≤
      CK m * (3 * X) ^ ((m : ℝ) - 1 / 2) * ((M : ℝ) ^ (1 / 8 : ℝ) * St a ((m : ℝ) + 5 / 8)) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12, inv_mul_le_iff₀ hh12]
    refine norm_It_le hh.le 12 EM x _ (fun y hy => ?_)
    exact norm_EM_le hd hX M (by linarith [hy.1]) (by push_cast at hy; linarith [hy.2])
  have hbT : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * T‖ ≤ (h ^ 12)⁻¹ * (CT m / π ^ 12 * (3 * X) ^ (m + 6) * X ^ (-(1 / 4) : ℝ) *
      (((M : ℝ) + 1) ^ (-(11 / 2) : ℝ) * St a ((m : ℝ) + 3 / 4))) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12]
    exact mul_le_mul_of_nonneg_left (norm_tail_le hd hX hh M hx1 hx3) (by positivity)
  have hb2 : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EM x + (((h ^ 12 : ℝ) : ℂ))⁻¹ * T‖ ≤ B2 m a X h M :=
    (norm_add_le _ _).trans (add_le_add hbE hbT)
  have hb4 : ‖(((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x‖ ≤ B4 m a X h N := by
    have hε : ∀ y ∈ Icc x (x + (12 : ℕ) * h), ‖VN y - VN x‖ ≤ B4 m a X h N := by
      intro y hy
      simp only [VN]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hy3 : y ≤ 3 * X := by push_cast at hy; linarith [hy.2]
      refine (abs_Vth_sub_le hd hX N hx1 hy.1 hy3).trans ?_
      unfold B4
      have : y - x ≤ 12 * h := by push_cast at hy; linarith [hy.2]
      have : 0 ≤ 1 / (π * √2) * (((m : ℝ) + 2 * π) * ((N : ℝ) * St a ((m : ℝ) + 3 / 4))) * (3 * X) ^ ((m : ℝ) - 3 / 4) := by
        have := St_nonneg (a := a) ((m : ℝ) + 3 / 4); positivity
      gcongr
    have := norm_It_sub_le hh.le 12 hVNc x _ hε
    have e : (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x =
        (((h ^ 12 : ℝ) : ℂ))⁻¹ * (It h 12 VN x - (h : ℂ) ^ 12 * VN x) := by
      field_simp; push_cast; ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12, inv_mul_le_iff₀ hh12]
    exact this
  -- combine
  have hnorm : (Sre a x - Vth m a N x) ^ 2 = ‖((Sre a x - Vth m a N x : ℝ) : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm, hdec]
  set p1 := (Sre a x : ℂ) - Sh m a h x
  set p2 := (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 EM x + (((h ^ 12 : ℝ) : ℂ))⁻¹ * T
  set p3 := (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 D x
  set p4 := (((h ^ 12 : ℝ) : ℂ))⁻¹ * It h 12 VN x - VN x
  have h4 : ‖p1 + p2 + p3 + p4‖ ^ 2 ≤ 4 * (‖p1‖ ^ 2 + ‖p2‖ ^ 2 + ‖p3‖ ^ 2 + ‖p4‖ ^ 2) := by
    have t : ‖p1 + p2 + p3 + p4‖ ≤ ‖p1‖ + ‖p2‖ + ‖p3‖ + ‖p4‖ :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    have t2 := pow_le_pow_left₀ (norm_nonneg _) t 2
    nlinarith [sq_nonneg (‖p1‖ - ‖p2‖), sq_nonneg (‖p1‖ - ‖p3‖), sq_nonneg (‖p1‖ - ‖p4‖),
      sq_nonneg (‖p2‖ - ‖p3‖), sq_nonneg (‖p2‖ - ‖p4‖), sq_nonneg (‖p3‖ - ‖p4‖)]
  refine h4.trans ?_
  have hb2' : ‖p2‖ ^ 2 ≤ B2 m a X h M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb2 2
  have hb4' : ‖p4‖ ^ 2 ≤ B4 m a X h N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb4 2
  gcongr


/-- **The `L²` bound** on a dyadic block, with free parameters `h`, `N`, `M`. -/
theorem L2_main (hd : VData m a) {X h : ℝ} {N M : ℕ} (hX : 1 ≤ X) (hh : 0 < h) (h12 : 12 * h ≤ X) :
    ∫ x in Ioc X (2 * X), (Sre a x - Vth m a N x) ^ 2 ≤
      4 * ((12 * h + 1) * (12 * h) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, a n ^ 2 +
        X * B2 m a X h M ^ 2 + (∫ x in X..3 * X, (Vth m a M x - Vth m a N x) ^ 2) + X * B4 m a X h N ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hh12 : (0 : ℝ) < h ^ 12 := pow_pos hh 12
  set D : ℝ → ℂ := fun y => ((Vth m a M y - Vth m a N y : ℝ) : ℂ) with hD
  have hDc : Continuous D := continuous_ofReal.comp ((continuous_Vth hd.one_le M).sub (continuous_Vth hd.one_le N))
  set c : ℝ → ℝ := fun x => ‖((h ^ 12 : ℝ) : ℂ)⁻¹ * It h 12 D x‖ ^ 2 with hcdef
  have hcc : Continuous c := ((continuous_const.mul (continuous_It h 12 D hDc)).norm).pow 2
  have hci : IntegrableOn c (Ioc X (2 * X)) :=
    (hcc.integrableOn_Icc (a := X) (b := 2 * X)).mono_set Ioc_subset_Icc_self
  have hg1i := integrableOn_g1 (a := a) X (12 * h) X (2 * X)
  have hvol : volume.real (Ioc X (2 * X)) = X := by
    rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
  have hconst : ∀ C : ℝ, ∫ x in Ioc X (2 * X), C = X * C := by
    intro C; rw [setIntegral_const, hvol, smul_eq_mul]
  have hcI : ∀ C : ℝ, IntegrableOn (fun _ : ℝ => C) (Ioc X (2 * X)) := fun C =>
    integrableOn_const (by simp) (by simp)
  have hgi : IntegrableOn (fun x => 4 * (g1 a X (12 * h) x + B2 m a X h M ^ 2 + c x + B4 m a X h N ^ 2))
      (Ioc X (2 * X)) :=
    (((hg1i.add (hcI _)).add hci).add (hcI _)).const_mul 4
  have hmono := integral_mono_of_nonneg (μ := volume.restrict (Ioc X (2 * X)))
    (Eventually.of_forall fun x => sq_nonneg (Sre a x - Vth m a N x)) hgi
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
      pointwise_bound hd (N := N) (M := M) hX hh h12 hx))
  refine hmono.trans ?_
  have i1 : IntegrableOn (fun u => g1 a X (12 * h) u + B2 m a X h M ^ 2) (Ioc X (2 * X)) :=
    hg1i.add (hcI (B2 m a X h M ^ 2))
  have i2 : IntegrableOn (fun u => g1 a X (12 * h) u + B2 m a X h M ^ 2 + c u) (Ioc X (2 * X)) :=
    i1.add hci
  rw [integral_const_mul,
    integral_add (f := fun u => g1 a X (12 * h) u + B2 m a X h M ^ 2 + c u) (g := fun _ => B4 m a X h N ^ 2)
      i2 (hcI _),
    integral_add (f := fun u => g1 a X (12 * h) u + B2 m a X h M ^ 2) (g := c) i1 hci,
    integral_add (f := g1 a X (12 * h)) (g := fun _ => B2 m a X h M ^ 2) hg1i (hcI _), hconst, hconst]
  gcongr
  · exact integral_g1_le hX0 (by positivity)
  · -- the mean-value part
    rw [← intervalIntegral.integral_of_le (by linarith)]
    have h1 : ∫ x in X..2 * X, c x = (h ^ 12)⁻¹ ^ 2 * ∫ x in X..2 * X, ‖It h 12 D x‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hcdef]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh12]; ring
    have h2 := integral_norm_It_sq_le hh.le 12 D hDc X (2 * X) (by linarith)
    have h3 : ∫ x in X..(2 * X + (12 : ℕ) * h), ‖D x‖ ^ 2 ≤ ∫ x in X..3 * X, ‖D x‖ ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl (by push_cast; linarith) (by push_cast; linarith)
        (Eventually.of_forall fun x => sq_nonneg _) ((hDc.norm.pow 2).intervalIntegrable _ _)
    have h4 : ∫ x in X..3 * X, ‖D x‖ ^ 2 = ∫ x in X..3 * X, (Vth m a M x - Vth m a N x) ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hD, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h1, ← h4]
    have e : (h ^ 12)⁻¹ ^ 2 * (h ^ (2 * 12)) = 1 := by
      rw [show 2 * 12 = 12 * 2 by rfl, pow_mul]; field_simp
    calc (h ^ 12)⁻¹ ^ 2 * ∫ x in X..2 * X, ‖It h 12 D x‖ ^ 2
        ≤ (h ^ 12)⁻¹ ^ 2 * (h ^ (2 * 12) * ∫ x in X..(2 * X + (12 : ℕ) * h), ‖D x‖ ^ 2) := by gcongr
      _ = ∫ x in X..(2 * X + (12 : ℕ) * h), ‖D x‖ ^ 2 := by rw [← mul_assoc, e, one_mul]
      _ ≤ _ := h3

end RamanujanTau.VoronoiTruncGeneral
