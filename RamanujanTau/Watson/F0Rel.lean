/-
# Watson's (2₀) and (3₀): `f₀(q) ± ϑ₄(q) G(q)`

(Watson 1937, §3, pp. 285–287; `docs/watson1937_R1_proof.md`.)

* (2₀) `f₀(q) + ϑ₄(q)G(q) = 2φ₀(−q²)`;
* (3₀) `f₀(q) − ϑ₄(q)G(q) = 2qψ(q²)H(q⁴) − 2(F₀(q²) − 1)`.

Here:
* `ϑ₄(q) = (q;q)_∞/(−q;q)_∞`;
* `G(q) = Σ q^{n²}/(q)_n` and `H(q) = Σ q^{n²+n}/(q)_n` (Rogers–Ramanujan series);
* `ψ(q²) = (q⁴;q⁴)_∞/(q²;q⁴)_∞`.
-/
import RamanujanTau.Watson.R1

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-- `f₀ = Σ q^{n²}/(−q;q)_n`. -/
noncomputable def f0w : PowerSeries ℤ := osum fun n => X ^ (n * n) * Ring.inverse (FP (-1) 1 1 n)

/-- `G(q) = Σ q^{n²}/(q;q)_n`. -/
noncomputable def Gw : PowerSeries ℤ := osum fun n => X ^ (n * n) * QI 1 n

/-- `H(q) = Σ q^{n²+n}/(q;q)_n`. -/
noncomputable def Hw : PowerSeries ℤ := osum fun n => X ^ (n * n + n) * QI 1 n

/-- `ϑ₄(q) = (q;q)_∞/(−q;q)_∞`. -/
noncomputable def th4w : PowerSeries ℤ := IP 1 1 1 * Ring.inverse (IP (-1) 1 1)

/-- `ψ(q²) = (q⁴;q⁴)_∞/(q²;q⁴)_∞`. -/
noncomputable def psi2w : PowerSeries ℤ := IP 1 4 4 * Ring.inverse (IP 1 2 4)

/-- the odd part: `Σ_k (1 − (−1)ᵏ) u k = 2 Σ_n u (2n+1)`. -/
lemma osum_odd_part {u : ℕ → PowerSeries ℤ} (hu : LF u) :
    osum (fun k => ((1 - (-1) ^ k : ℤ) : PowerSeries ℤ) * u k) = 2 * osum (fun n => u (2 * n + 1)) := by
  have hv : LF (fun k => ((1 - (-1) ^ k : ℤ) : PowerSeries ℤ) * u k) := by
    intro k
    refine (hu k).subset fun i hi => ?_
    simp only [Function.mem_support, ne_eq, coeff_intCast_mul] at hi ⊢
    intro h; apply hi; simp [h]
  rw [osum_parity hv]
  have h1 : (osum fun n => ((1 - (-1) ^ (2 * n) : ℤ) : PowerSeries ℤ) * u (2 * n)) = 0 := by
    rw [← osum_zero (ι := ℕ)]; refine osum_ext fun n => ?_; simp [pow_mul]
  have hu2 : LF (fun n => u (2 * n + 1)) := hu.comp_injective (e := fun n => 2 * n + 1)
    (fun a b h => by simp only at h; omega)
  rw [h1, zero_add, ← osum_smul (2 : PowerSeries ℤ) hu2]
  refine osum_ext fun n => ?_
  simp [pow_succ, pow_mul]

/-- the common first step: `f₀ ± ϑ₄G = (q)_∞ Σ_n q^{n²}/(q²;q²)_n · [1/(q^{n+1})_∞ ± 1/(−q^{n+1})_∞]`. -/
lemma f0_pm_step (n : ℕ) :
    X ^ (n * n) * Ring.inverse (FP (-1) 1 1 n) = IP 1 1 1 * (X ^ (n * n) * QI 2 n * GI 1 (n + 1) 1) ∧
    Ring.inverse (IP (-1) 1 1) * (X ^ (n * n) * QI 1 n) =
      X ^ (n * n) * QI 2 n * GI (-1) (n + 1) 1 := by
  have uq := uFP 1 (show 1 ≤ 1 by rfl) 1 n
  have um := uFP (-1) (show 1 ≤ 1 by rfl) 1 n
  have sq : FP 1 1 1 n * FP (-1) 1 1 n = QF 2 n := by rw [FP_sq]; norm_num
  have e2 := QF_mul_QI 2 n (by norm_num)
  rw [← sq] at e2
  constructor
  · have hE : IP 1 1 1 * GI 1 (n + 1) 1 = QF 1 n := E_mul_GI n
    have hq := QF_mul_QI 1 n le_rfl
    apply um.mul_left_cancel
    calc FP (-1) 1 1 n * (X ^ (n * n) * Ring.inverse (FP (-1) 1 1 n))
        = X ^ (n * n) * (FP (-1) 1 1 n * Ring.inverse (FP (-1) 1 1 n)) := by ring
      _ = X ^ (n * n) * ((FP 1 1 1 n * FP (-1) 1 1 n * QI 2 n)) := by rw [Ring.mul_inverse_cancel _ um, e2]
      _ = FP (-1) 1 1 n * (IP 1 1 1 * (X ^ (n * n) * QI 2 n * GI 1 (n + 1) 1)) := by
        rw [show FP 1 1 1 n = IP 1 1 1 * GI 1 (n + 1) 1 from hE.symm]; ring
  · have s2 : IP (-1) 1 1 = FP (-1) 1 1 n * IP (-1) (n + 1) 1 := by
      rw [IP_split (-1) (a := 1) (b := 1) le_rfl le_rfl n]; ring_nf
    have uI := uIP (-1) (show 1 ≤ n + 1 by omega) (show 1 ≤ 1 by rfl)
    have eG : GI (-1) (n + 1) 1 * IP (-1) (n + 1) 1 = 1 := by
      rw [mul_comm]; exact euler_inv (-1) (by omega) le_rfl
    have uIm := uIP (-1) (show 1 ≤ 1 by rfl) (show 1 ≤ 1 by rfl)
    apply uIm.mul_left_cancel
    rw [← mul_assoc, Ring.mul_inverse_cancel _ uIm, one_mul, s2]
    have hq := QF_mul_QI 1 n le_rfl
    calc X ^ (n * n) * QI 1 n
        = X ^ (n * n) * QI 1 n * (FP 1 1 1 n * FP (-1) 1 1 n * QI 2 n) * (GI (-1) (n + 1) 1 * IP (-1) (n + 1) 1) := by
          rw [e2, eG]; ring
      _ = X ^ (n * n) * (QF 1 n * QI 1 n) * FP (-1) 1 1 n * QI 2 n * GI (-1) (n + 1) 1 * IP (-1) (n + 1) 1 := by
          rw [QF]; ring
      _ = FP (-1) 1 1 n * IP (-1) (n + 1) 1 * (X ^ (n * n) * QI 2 n * GI (-1) (n + 1) 1) := by
          rw [hq]; ring

lemma LF_f0 : LF fun n => X ^ (n * n) * Ring.inverse (FP (-1) 1 1 n) := LF_Xpow_mul fun n => by nlinarith
lemma LF_G : LF fun n => X ^ (n * n) * QI 1 n := LF_Xpow_mul fun n => by nlinarith

/-- `f₀ ± ϑ₄G = (q)_∞ Σ_n q^{n²}/(q²;q²)_n · (GI₊ ± GI₋)`. -/
lemma f0_pm (s : ℤ) (hs : s = 1 ∨ s = -1) :
    f0w + (s : PowerSeries ℤ) * (th4w * Gw) =
      IP 1 1 1 * osum fun n => X ^ (n * n) * QI 2 n * (GI 1 (n + 1) 1 + (s : PowerSeries ℤ) * GI (-1) (n + 1) 1) := by
  have l1 : LF fun n => X ^ (n * n) * QI 2 n * GI 1 (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 2 n * GI 1 (n + 1) 1) (e := fun n => n * n)
      (fun n => by show n ≤ n * n; nlinarith)
  have l2 : LF fun n => X ^ (n * n) * QI 2 n * GI (-1) (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 2 n * GI (-1) (n + 1) 1) (e := fun n => n * n)
      (fun n => by show n ≤ n * n; nlinarith)
  have hf : f0w = IP 1 1 1 * osum fun n => X ^ (n * n) * QI 2 n * GI 1 (n + 1) 1 := by
    rw [f0w, mul_osum l1]; exact osum_ext fun n => (f0_pm_step n).1
  have hg : th4w * Gw = IP 1 1 1 * osum fun n => X ^ (n * n) * QI 2 n * GI (-1) (n + 1) 1 := by
    rw [th4w, Gw, mul_assoc, mul_osum LF_G]
    congr 1; exact osum_ext fun n => (f0_pm_step n).2
  rw [hf, hg]
  have : (osum fun n => X ^ (n * n) * QI 2 n * (GI 1 (n + 1) 1 + (s : PowerSeries ℤ) * GI (-1) (n + 1) 1)) =
      (osum fun n => X ^ (n * n) * QI 2 n * GI 1 (n + 1) 1) +
        (s : PowerSeries ℤ) * osum fun n => X ^ (n * n) * QI 2 n * GI (-1) (n + 1) 1 := by
    rw [← osum_smul _ l2, ← osum_add l1 (l2.mul_left _)]
    exact osum_ext fun n => by ring
  rw [this]
  ring

lemma u4 (m : ℕ) : IP 1 1 1 * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2 = IP 1 2 2 * QI 2 m * IP 1 (4 * m + 2) 4 := by
  have h1 : IP 1 1 1 * QI 1 (2 * m) = IP 1 (2 * m + 1) 1 := by
    rw [IP_split1 (2 * m), mul_comm (QF 1 _), mul_assoc, QF_mul_QI 1 _ le_rfl, mul_one]
  have h2 : IP 1 (2 * m + 1) 1 = IP 1 (2 * m + 1) 2 * IP 1 (2 * m + 2) 2 := by
    rw [IP_two 1 (a := 2 * m + 1) (b := 1) (by omega) le_rfl]
  have h3 : IP 1 (2 * m + 1) 2 * IP (-1) (2 * m + 1) 2 = IP 1 (4 * m + 2) 4 := by
    rw [IP_sq 1 (a := 2 * m + 1) (b := 2) (by omega) (by norm_num)]; ring_nf
  have h4 : IP 1 (2 * m + 2) 2 = IP 1 2 2 * QI 2 m := by
    rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) m, mul_comm (FP 1 2 2 m), mul_assoc,
      show FP 1 2 2 m = QF 2 m from rfl, QF_mul_QI 2 m (by norm_num), mul_one]; ring_nf
  rw [h1, h2, h4, ← h3]; ring

lemma u5 (n : ℕ) : IP 1 2 2 * QI 4 n * GI 1 (4 * n + 2) 2 = FP 1 2 4 n := by
  have s1 : IP 1 2 2 = FP 1 2 2 (2 * n) * IP 1 (4 * n + 2) 2 := by
    rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) (2 * n)]; ring_nf
  have s2 : FP 1 2 2 (2 * n) = FP 1 2 4 n * FP 1 4 4 n := by rw [FP_two]
  have e1 : IP 1 (4 * n + 2) 2 * GI 1 (4 * n + 2) 2 = 1 := euler_inv 1 (by omega) (by norm_num)
  have e2 : FP 1 4 4 n * QI 4 n = 1 := QF_mul_QI 4 n (by norm_num)
  rw [s1, s2]
  linear_combination (FP 1 2 4 n * FP 1 4 4 n * QI 4 n) * e1 + FP 1 2 4 n * e2

lemma expand2_P0w : expand 2 two_ne_zero P0w = osum fun n => (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n)) * FP 1 2 4 n := by
  have hLP : LF fun n => (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * FP 1 1 2 n :=
    LF.of_nat fun n k hk => by
      rw [show (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * FP 1 1 2 n
        = X ^ (n * n) * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * FP 1 1 2 n) by ring,
        coeff_X_pow_mul', if_neg (by nlinarith)]
  rw [P0w, expand_osum 2 two_ne_zero hLP]
  refine osum_ext fun n => ?_
  rw [map_mul, map_mul, map_intCast, map_pow, expand_X, expand_FP, ← pow_mul]

/-- **(2₀)** `f₀(q) + ϑ₄(q)G(q) = 2φ₀(−q²)`. -/
theorem watson_2_0 : f0w + th4w * Gw = 2 * expand 2 two_ne_zero P0w := by
  have h := f0_pm 1 (Or.inl rfl)
  simp only [Int.cast_one, one_mul] at h
  rw [h]
  -- `GI₊ + GI₋ = 2 A(2n+2)` and expand `A`
  set g : ℕ × ℕ → PowerSeries ℤ := fun q => X ^ (q.1 * q.1 + (2 * q.1 + 2) * q.2) * (QI 2 q.1 * QI 1 (2 * q.2)) with hg_def
  have hg : LF g := LF_pair fun q => by nlinarith
  have e1 : (osum fun n => X ^ (n * n) * QI 2 n * (GI 1 (n + 1) 1 + GI (-1) (n + 1) 1)) =
      2 * osum fun n => osum fun m => g (n, m) := by
    rw [← osum_smul _ hg.prod_outer]
    refine osum_ext fun n => ?_
    rw [GI_pm, Aw, show X ^ (n * n) * QI 2 n * (2 * osum fun m => X ^ ((2 * n + 2) * m) * QI 1 (2 * m))
      = 2 * (X ^ (n * n) * QI 2 n * osum fun m => X ^ ((2 * n + 2) * m) * QI 1 (2 * m)) by ring,
      mul_osum (LF_Xpow_mul fun m => by nlinarith)]
    congr 1; refine osum_ext fun m => ?_
    simp only [hg_def]; rw [pow_add]; ring
  -- inner sum over `n` is `(−q^{2m+1};q²)_∞`
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2 := fun m => by
    rw [euler_prod (-1) (by omega) (by norm_num), HP, mul_osum (LF_hP (-1) (by omega) 2)]
    refine osum_ext fun n => ?_
    simp only [hg_def, hP]
    rw [show n * n + (2 * n + 2) * m = 2 * m + ((2 * m + 1) * n + 2 * n.choose 2) by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  -- multiply by `(q)_∞` and expand `(q^{4m+2};q⁴)_∞`
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + ((4 * q.1 + 2) * q.2 + 4 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 2 q.1 * QI 4 q.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun q => by nlinarith
  have hL : LF fun m => X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 (2 * m) * IP (-1) (2 * m + 1) 2) (e := fun m => 2 * m)
      (fun m => by show m ≤ 2 * m; omega)
  have e3 : IP 1 1 1 * (2 * osum fun m => X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2) =
      2 * (IP 1 2 2 * osum fun m => osum fun n => g2 (m, n)) := by
    rw [mul_left_comm, mul_osum hL, ← osum_smul _ hg2.prod_outer]
    congr 1; refine osum_ext fun m => ?_
    rw [show IP 1 1 1 * (X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2)
      = X ^ (2 * m) * (IP 1 1 1 * QI 1 (2 * m) * IP (-1) (2 * m + 1) 2) by ring, u4,
      euler_prod 1 (a := 4 * m + 2) (b := 4) (by omega) (by norm_num), HP,
      show X ^ (2 * m) * (IP 1 2 2 * QI 2 m * osum (hP 1 (4 * m + 2) 4))
        = IP 1 2 2 * (X ^ (2 * m) * QI 2 m * osum (hP 1 (4 * m + 2) 4)) by ring,
      mul_osum (LF_hP 1 (by omega) 4)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) = (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n)) * QI 4 n * GI 1 (4 * n + 2) 2 :=
    fun n => by
      rw [GI, mul_osum (LF_gI 1 (by omega) 2)]
      refine osum_ext fun m => ?_
      simp only [hg2_def, gI]
      rw [show 2 * m + ((4 * m + 2) * n + 4 * n.choose 2) = 2 * (n * n) + (4 * n + 2) * m by
        have := two_choose_two n; nlinarith, pow_add]
      push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer', expand2_P0w]
  congr 1; refine osum_ext fun n => ?_
  rw [e4, show IP 1 2 2 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n)) * QI 4 n * GI 1 (4 * n + 2) 2)
    = (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n)) * (IP 1 2 2 * QI 4 n * GI 1 (4 * n + 2) 2) by ring, u5]

/-- `1/(q^{n+1};q)_∞ − 1/(−q^{n+1};q)_∞ = 2 Σ_m q^{(n+1)(2m+1)}/(q)_{2m+1}`. -/
lemma GI_mp (n : ℕ) :
    GI 1 (n + 1) 1 - GI (-1) (n + 1) 1 = 2 * osum fun m => X ^ ((n + 1) * (2 * m + 1)) * QI 1 (2 * m + 1) := by
  have hu : LF (fun k => X ^ ((n + 1) * k) * QI 1 k : ℕ → PowerSeries ℤ) := LF_Xpow_mul (fun k => by nlinarith)
  rw [GI, GI, ← osum_sub (LF_gI 1 (by omega) 1) (LF_gI (-1) (by omega) 1), ← osum_odd_part hu]
  refine osum_ext fun k => ?_
  simp only [gI]; push_cast; ring

lemma u6 (m : ℕ) :
    IP 1 1 1 * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2 = IP 1 4 4 * QI 4 m * IP 1 (2 * m + 3) 2 := by
  have h1 : IP 1 1 1 * QI 1 (2 * m + 1) = IP 1 (2 * m + 2) 1 := by
    rw [IP_split1 (2 * m + 1), mul_comm (QF 1 _), mul_assoc, QF_mul_QI 1 _ le_rfl, mul_one]
  have h2 : IP 1 (2 * m + 2) 1 = IP 1 (2 * m + 2) 2 * IP 1 (2 * m + 3) 2 := by
    rw [IP_two 1 (a := 2 * m + 2) (b := 1) (by omega) le_rfl]
  have h3 : IP 1 (2 * m + 2) 2 * IP (-1) (2 * m + 2) 2 = IP 1 (4 * m + 4) 4 := by
    rw [IP_sq 1 (a := 2 * m + 2) (b := 2) (by omega) (by norm_num)]; ring_nf
  have h4 : IP 1 (4 * m + 4) 4 = IP 1 4 4 * QI 4 m := by
    rw [IP_split 1 (a := 4) (b := 4) (by norm_num) (by norm_num) m, mul_comm (FP 1 4 4 m), mul_assoc,
      show FP 1 4 4 m = QF 4 m from rfl, QF_mul_QI 4 m (by norm_num), mul_one]; ring_nf
  rw [h1, h2, ← h4, ← h3]; ring

lemma u7 (m : ℕ) : IP 1 4 4 * QI 2 (2 * m) * GI 1 (4 * m + 2) 4 = psi2w * QI 4 m := by
  have s1 : IP 1 2 4 = FP 1 2 4 m * IP 1 (4 * m + 2) 4 := by
    rw [IP_split 1 (a := 2) (b := 4) (by norm_num) (by norm_num) m]; ring_nf
  have s2 : QF 2 (2 * m) = FP 1 2 4 m * FP 1 4 4 m := by rw [QF, FP_two]
  have e1 : IP 1 (4 * m + 2) 4 * GI 1 (4 * m + 2) 4 = 1 := euler_inv 1 (by omega) (by norm_num)
  have e2 := QF_mul_QI 2 (2 * m) (by norm_num)
  rw [s2] at e2
  have e3 : FP 1 4 4 m * QI 4 m = 1 := QF_mul_QI 4 m (by norm_num)
  have u1 := uIP 1 (show 1 ≤ 2 by norm_num) (show 1 ≤ 4 by norm_num)
  have e5 := Ring.inverse_mul_cancel _ u1
  have uF := (uFP 1 (show 1 ≤ 2 by norm_num) 4 m).mul (uFP 1 (show 1 ≤ 4 by norm_num) 4 m)
  rw [psi2w]
  apply (uF.mul u1).mul_right_cancel
  calc IP 1 4 4 * QI 2 (2 * m) * GI 1 (4 * m + 2) 4 * (FP 1 2 4 m * FP 1 4 4 m * IP 1 2 4)
      = IP 1 4 4 * (FP 1 2 4 m * FP 1 4 4 m * QI 2 (2 * m)) * (GI 1 (4 * m + 2) 4 * IP 1 2 4) := by ring
    _ = IP 1 4 4 * FP 1 2 4 m * (IP 1 (4 * m + 2) 4 * GI 1 (4 * m + 2) 4) := by rw [e2, s1]; ring
    _ = IP 1 4 4 * FP 1 2 4 m * (FP 1 4 4 m * QI 4 m) * (Ring.inverse (IP 1 2 4) * IP 1 2 4) := by
      rw [e1, e3, e5]; ring
    _ = IP 1 4 4 * Ring.inverse (IP 1 2 4) * QI 4 m * (FP 1 2 4 m * FP 1 4 4 m * IP 1 2 4) := by ring

lemma u8 (m : ℕ) : IP 1 4 4 * QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4 = Ring.inverse (FP 1 2 4 (m + 1)) := by
  have s1 : IP 1 4 4 = FP 1 4 4 m * IP 1 (4 * m + 4) 4 := by
    rw [IP_split 1 (a := 4) (b := 4) (by norm_num) (by norm_num) m]; ring_nf
  have s2 : QF 2 (2 * m + 1) = FP 1 2 4 (m + 1) * FP 1 4 4 m := by rw [QF, FP_two_succ]
  have e1 : IP 1 (4 * m + 4) 4 * GI 1 (4 * m + 4) 4 = 1 := euler_inv 1 (by omega) (by norm_num)
  have e2 := QF_mul_QI 2 (2 * m + 1) (by norm_num)
  rw [s2] at e2
  symm
  apply inv_eq_of_mul_eq_one
  calc FP 1 2 4 (m + 1) * (IP 1 4 4 * QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4)
      = (FP 1 2 4 (m + 1) * FP 1 4 4 m * QI 2 (2 * m + 1)) * (IP 1 (4 * m + 4) 4 * GI 1 (4 * m + 4) 4) := by
        rw [s1]; ring
    _ = 1 := by rw [e2, e1, one_mul]

lemma expand4_Hw : expand 4 (by norm_num) Hw = osum fun m => X ^ (4 * (m * m + m)) * QI 4 m := by
  rw [Hw, expand_osum 4 _ (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [map_mul, map_pow, expand_X, expand_QI 4 _ 1 m le_rfl, ← pow_mul]

lemma expand2_F0w : expand 2 two_ne_zero F0w = osum fun n => X ^ (2 * (2 * (n * n))) * Ring.inverse (FP 1 2 4 n) := by
  rw [F0w, expand_osum 2 _ (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun n => ?_
  rw [map_mul, map_pow, expand_X, expand_inverse 2 _ (uFP 1 le_rfl 2 n), expand_FP, ← pow_mul]

/-- **(3₀)** `f₀(q) − ϑ₄(q)G(q) = 2qψ(q²)H(q⁴) − 2(F₀(q²) − 1)`. -/
theorem watson_3_0 :
    f0w - th4w * Gw = 2 * X * psi2w * expand 4 (by norm_num) Hw - 2 * (expand 2 two_ne_zero F0w - 1) := by
  have h := f0_pm (-1) (Or.inr rfl)
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg] at h
  rw [h]
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (q.1 * q.1 + (q.1 + 1) * (2 * q.2 + 1)) * (QI 2 q.1 * QI 1 (2 * q.2 + 1)) with hg_def
  have hg : LF g := LF_pair fun q => by nlinarith
  have e1 : (osum fun n => X ^ (n * n) * QI 2 n * (GI 1 (n + 1) 1 - GI (-1) (n + 1) 1)) =
      2 * osum fun n => osum fun m => g (n, m) := by
    rw [← osum_smul _ hg.prod_outer]
    refine osum_ext fun n => ?_
    rw [GI_mp, show X ^ (n * n) * QI 2 n * (2 * osum fun m => X ^ ((n + 1) * (2 * m + 1)) * QI 1 (2 * m + 1))
      = 2 * (X ^ (n * n) * QI 2 n * osum fun m => X ^ ((n + 1) * (2 * m + 1)) * QI 1 (2 * m + 1)) by ring,
      mul_osum (LF_Xpow_mul fun m => by nlinarith)]
    congr 1; refine osum_ext fun m => ?_
    simp only [hg_def]; rw [pow_add]; ring
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2 :=
    fun m => by
      rw [euler_prod (-1) (a := 2 * m + 2) (b := 2) (by omega) (by norm_num), HP, mul_osum (LF_hP (-1) (by omega) 2)]
      refine osum_ext fun n => ?_
      simp only [hg_def, hP]
      rw [show n * n + (n + 1) * (2 * m + 1) = 2 * m + 1 + ((2 * m + 2) * n + 2 * n.choose 2) by
        have := two_choose_two n; nlinarith, pow_add]
      push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + 1 + ((2 * q.1 + 3) * q.2 + 2 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 4 q.1 * QI 2 q.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun q => by nlinarith
  have hL : LF fun m => X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2)
      (e := fun m => 2 * m + 1) (fun m => by show m ≤ 2 * m + 1; omega)
  have e3 : IP 1 1 1 * (2 * osum fun m => X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2) =
      2 * (IP 1 4 4 * osum fun m => osum fun n => g2 (m, n)) := by
    rw [mul_left_comm, mul_osum hL, ← osum_smul _ hg2.prod_outer]
    congr 1; refine osum_ext fun m => ?_
    rw [show IP 1 1 1 * (X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2)
      = X ^ (2 * m + 1) * (IP 1 1 1 * QI 1 (2 * m + 1) * IP (-1) (2 * m + 2) 2) by ring, u6,
      euler_prod 1 (a := 2 * m + 3) (b := 2) (by omega) (by norm_num), HP,
      show X ^ (2 * m + 1) * (IP 1 4 4 * QI 4 m * osum (hP 1 (2 * m + 3) 2))
        = IP 1 4 4 * (X ^ (2 * m + 1) * QI 4 m * osum (hP 1 (2 * m + 3) 2)) by ring,
      mul_osum (LF_hP 1 (by omega) 2)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) =
      (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * QI 2 n * GI 1 (2 * n + 2) 4 := fun n => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 4)]
    refine osum_ext fun m => ?_
    simp only [hg2_def, gI]
    rw [show 2 * m + 1 + ((2 * m + 3) * n + 2 * n.choose 2) = (n + 1) * (n + 1) + (2 * n + 2) * m by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer']
  simp_rw [e4]
  -- parity split in `n`
  have hK : LF fun n => IP 1 4 4 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * QI 2 n * GI 1 (2 * n + 2) 4) := by
    refine LF.of_nat fun n k hk => ?_
    rw [show IP 1 4 4 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * QI 2 n * GI 1 (2 * n + 2) 4)
      = X ^ ((n + 1) * (n + 1)) * (IP 1 4 4 * (((-1) ^ n : ℤ) : PowerSeries ℤ) * QI 2 n * GI 1 (2 * n + 2) 4) by ring,
      coeff_X_pow_mul', if_neg (by nlinarith)]
  rw [osum_parity hK]
  have hev : (osum fun m => IP 1 4 4 * ((((-1) ^ (2 * m) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1) * (2 * m + 1)) *
      QI 2 (2 * m) * GI 1 (2 * (2 * m) + 2) 4)) = X * psi2w * expand 4 (by norm_num) Hw := by
    rw [expand4_Hw, mul_osum (LF_Xpow_mul fun m => by nlinarith)]
    refine osum_ext fun m => ?_
    rw [show 2 * (2 * m) + 2 = 4 * m + 2 by ring,
      show IP 1 4 4 * ((((-1) ^ (2 * m) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1) * (2 * m + 1)) * QI 2 (2 * m) *
        GI 1 (4 * m + 2) 4) = (((-1) ^ (2 * m) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1) * (2 * m + 1)) *
          (IP 1 4 4 * QI 2 (2 * m) * GI 1 (4 * m + 2) 4) by ring, u7,
      show (2 * m + 1) * (2 * m + 1) = 1 + 4 * (m * m + m) by ring, pow_add]
    simp [pow_mul]; ring
  have hod : (osum fun m => IP 1 4 4 * ((((-1) ^ (2 * m + 1) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1 + 1) * (2 * m + 1 + 1)) *
      QI 2 (2 * m + 1) * GI 1 (2 * (2 * m + 1) + 2) 4)) = -(expand 2 two_ne_zero F0w - 1) := by
    rw [expand2_F0w, osum_succ (LF_Xpow_mul fun n => by nlinarith)]
    simp only [mul_zero, pow_zero, FP_zero, Ring.inverse_one, mul_one, add_sub_cancel_left]
    rw [← osum_neg]
    refine osum_ext fun m => ?_
    rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 by ring,
      show IP 1 4 4 * ((((-1) ^ (2 * m + 1) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1 + 1) * (2 * m + 1 + 1)) *
        QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4) = (((-1) ^ (2 * m + 1) : ℤ) : PowerSeries ℤ) *
          X ^ ((2 * m + 1 + 1) * (2 * m + 1 + 1)) * (IP 1 4 4 * QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4) by ring, u8,
      show (2 * m + 1 + 1) * (2 * m + 1 + 1) = 2 * (2 * ((m + 1) * (m + 1))) by ring]
    simp [pow_succ, pow_mul]
  rw [hev, hod]; ring

end Watson
