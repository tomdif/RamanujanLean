/-
# Watson's linear relations (1₀), (1₁), (2₁), (3₁)

G. N. Watson, *The mock theta functions (2)*, Proc. LMS (2) 42 (1937), §3, pp. 283–287
(`docs/watson1937_R1_proof.md` transcribes the `f₀` group; the `f₁` group is the same computation with
`q^{n²}` replaced by `q^{n²+n}`).

* (1₀) `ψ₀(q) = qψ(q²)H(q⁴) + F₀(q²) − 1`                                 (`watson_1_0`)
* (1₁) `ψ₁(q) = ψ(q²)G(q⁴) + qF₁(q²)`                                     (`watson_1_1`)
* (2₁) `q(f₁(q) − ϑ₄(q)H(q)) = −2φ₁(−q²)`                                  (`watson_2_1`)
* (3₁) `f₁(q) + ϑ₄(q)H(q) = 2ψ(q²)G(q⁴) − 2qF₁(q²)`                         (`watson_3_1`)

All four reduce, after expanding with Euler's two identities and summing by Fubini, to the kernel
`K_{σ,δ} = (q⁴;q⁴)_∞ Σ_n σⁿ q^{(n+δ)²}/((q²;q²)_n (q^{2n+2};q⁴)_∞)`, which a parity split evaluates
(`kern_split`); `(3₀)` (`Watson.watson_3_0`) is the case `σ = −1, δ = 1`.
-/
import RamanujanTau.MockTheta5All.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MockTheta5All
open PowerSeries Watson Finset

/-! ### unit bookkeeping -/

lemma QF2_eq (n : ℕ) : QF 2 n = IP 1 2 2 * GI 1 (2 * n + 2) 2 := by
  have s : IP 1 2 2 = FP 1 2 2 n * IP 1 (2 * n + 2) 2 := by
    rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) n]; ring_nf
  have e : IP 1 (2 * n + 2) 2 * GI 1 (2 * n + 2) 2 = 1 := euler_inv 1 (by omega) (by norm_num)
  rw [s, mul_assoc, e, mul_one]

lemma FPm_eq (n : ℕ) : FP (-1) 1 1 n = QF 2 n * QI 1 n := by
  have h := FP_sq 1 1 1 n
  norm_num at h
  have e := QF_mul_QI 1 n le_rfl
  calc FP (-1) 1 1 n = (FP 1 1 1 n * QI 1 n) * FP (-1) 1 1 n := by rw [e, one_mul]
    _ = (FP 1 1 1 n * FP (-1) 1 1 n) * QI 1 n := by ring
    _ = QF 2 n * QI 1 n := by rw [h]

lemma IP22_QI (m : ℕ) : IP 1 2 2 * QI 2 m = IP 1 (2 * m + 2) 2 := by
  rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) m, mul_comm (FP 1 2 2 m), mul_assoc,
    show FP 1 2 2 m = QF 2 m from rfl, QF_mul_QI 2 m (by norm_num), mul_one]; ring_nf

lemma IP44_QI (m : ℕ) : IP 1 (4 * m + 4) 4 = IP 1 4 4 * QI 4 m := by
  rw [IP_split 1 (a := 4) (b := 4) (by norm_num) (by norm_num) m, mul_comm (FP 1 4 4 m), mul_assoc,
    show FP 1 4 4 m = QF 4 m from rfl, QF_mul_QI 4 m (by norm_num), mul_one]; ring_nf

lemma IP_two' (c : ℤ) (a : ℕ) (ha : 1 ≤ a) : IP c a 1 = IP c a 2 * IP c (a + 1) 2 := by
  rw [IP_two c (a := a) (b := 1) ha le_rfl]

lemma IP_sq' (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : IP 1 a b * IP (-1) a b = IP 1 (2 * a) (2 * b) := by
  rw [IP_sq 1 ha hb]; norm_num

/-- `(q²;q²)_∞/(q²;q²)_m · (−q^{2m+1};q)_∞ = (q⁴;q⁴)_∞/(q⁴;q⁴)_m · (−q^{2m+1};q²)_∞`. -/
lemma U1 (m : ℕ) : IP 1 2 2 * QI 2 m * IP (-1) (2 * m + 1) 1 = IP 1 4 4 * QI 4 m * IP (-1) (2 * m + 1) 2 := by
  rw [IP22_QI, IP_two' (-1) (2 * m + 1) (by omega), show 2 * m + 1 + 1 = 2 * m + 2 by ring, ← IP44_QI,
    show 4 * m + 4 = 2 * (2 * m + 2) by ring, ← IP_sq' (2 * m + 2) 2 (by omega) (by norm_num)]
  ring

/-- `(q²;q²)_∞/(q²;q²)_m · (−q^{2m+2};q)_∞ = (q⁴;q⁴)_∞/(q⁴;q⁴)_m · (−q^{2m+3};q²)_∞`. -/
lemma U0 (m : ℕ) : IP 1 2 2 * QI 2 m * IP (-1) (2 * m + 2) 1 = IP 1 4 4 * QI 4 m * IP (-1) (2 * m + 3) 2 := by
  rw [IP22_QI, IP_two' (-1) (2 * m + 2) (by omega), show 2 * m + 2 + 1 = 2 * m + 3 by ring, ← IP44_QI,
    show 4 * m + 4 = 2 * (2 * m + 2) by ring, ← IP_sq' (2 * m + 2) 2 (by omega) (by norm_num)]
  ring

/-- `(q)_∞/(q)_{2m} · (−q^{2m+2};q²)_∞ = (q⁴;q⁴)_∞/(q⁴;q⁴)_m · (q^{2m+1};q²)_∞`. -/
lemma U9 (m : ℕ) : IP 1 1 1 * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2 = IP 1 4 4 * QI 4 m * IP 1 (2 * m + 1) 2 := by
  have h1 : IP 1 1 1 * QI 1 (2 * m) = IP 1 (2 * m + 1) 1 := by
    rw [IP_split1 (2 * m), mul_comm (QF 1 _), mul_assoc, QF_mul_QI 1 _ le_rfl, mul_one]
  rw [h1, IP_two' 1 (2 * m + 1) (by omega), show 2 * m + 1 + 1 = 2 * m + 2 by ring, ← IP44_QI,
    show 4 * m + 4 = 2 * (2 * m + 2) by ring, ← IP_sq' (2 * m + 2) 2 (by omega) (by norm_num)]
  ring

/-- `(q)_∞/(q)_{2m+1} · (−q^{2m+3};q²)_∞ = (q²;q²)_∞/(q²;q²)_m · (q^{4m+6};q⁴)_∞`. -/
lemma U10 (m : ℕ) :
    IP 1 1 1 * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2 = IP 1 2 2 * QI 2 m * IP 1 (4 * m + 6) 4 := by
  have h1 : IP 1 1 1 * QI 1 (2 * m + 1) = IP 1 (2 * m + 2) 1 := by
    rw [IP_split1 (2 * m + 1), mul_comm (QF 1 _), mul_assoc, QF_mul_QI 1 _ le_rfl, mul_one]
  rw [h1, IP_two' 1 (2 * m + 2) (by omega), show 2 * m + 2 + 1 = 2 * m + 3 by ring, IP22_QI,
    show 4 * m + 6 = 2 * (2 * m + 3) by ring, ← IP_sq' (2 * m + 3) 2 (by omega) (by norm_num)]
  ring

/-! ### the kernel `K_{σ,δ}` and its parity split -/

lemma kern_split (σ : ℤ) (hσ : σ * σ = 1) (δ : ℕ) :
    (osum fun n => IP 1 4 4 * (((σ ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + δ) * (n + δ)) * QI 2 n * GI 1 (2 * n + 2) 4)) =
      (osum fun m => X ^ ((2 * m + δ) * (2 * m + δ)) * psi2w * QI 4 m) +
        (σ : PowerSeries ℤ) * osum fun m => X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) * Ring.inverse (FP 1 2 4 (m + 1)) := by
  have hK : LF fun n => IP 1 4 4 * (((σ ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + δ) * (n + δ)) * QI 2 n * GI 1 (2 * n + 2) 4) := by
    refine LF.of_nat fun n k hk => ?_
    rw [show IP 1 4 4 * (((σ ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + δ) * (n + δ)) * QI 2 n * GI 1 (2 * n + 2) 4)
      = X ^ ((n + δ) * (n + δ)) * (IP 1 4 4 * ((σ ^ n : ℤ) : PowerSeries ℤ) * QI 2 n * GI 1 (2 * n + 2) 4) by ring,
      coeff_X_pow_mul', if_neg (by nlinarith)]
  have hO : LF fun m => X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) * Ring.inverse (FP 1 2 4 (m + 1)) :=
    LF_Xpow_mul fun m => by nlinarith
  rw [osum_parity hK]
  have hev : (osum fun m => IP 1 4 4 * (((σ ^ (2 * m) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + δ) * (2 * m + δ)) *
      QI 2 (2 * m) * GI 1 (2 * (2 * m) + 2) 4)) = osum fun m => X ^ ((2 * m + δ) * (2 * m + δ)) * psi2w * QI 4 m := by
    refine osum_ext fun m => ?_
    have hs : ((σ ^ (2 * m) : ℤ) : PowerSeries ℤ) = 1 := by rw [pow_mul, sq, hσ, one_pow]; simp
    rw [hs, show 2 * (2 * m) + 2 = 4 * m + 2 by ring,
      show IP 1 4 4 * (1 * X ^ ((2 * m + δ) * (2 * m + δ)) * QI 2 (2 * m) * GI 1 (4 * m + 2) 4)
        = X ^ ((2 * m + δ) * (2 * m + δ)) * (IP 1 4 4 * QI 2 (2 * m) * GI 1 (4 * m + 2) 4) by ring, u7]
    ring
  have hod : (osum fun m => IP 1 4 4 * (((σ ^ (2 * m + 1) : ℤ) : PowerSeries ℤ) * X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) *
      QI 2 (2 * m + 1) * GI 1 (2 * (2 * m + 1) + 2) 4)) =
        (σ : PowerSeries ℤ) * osum fun m => X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) * Ring.inverse (FP 1 2 4 (m + 1)) := by
    rw [← osum_smul _ hO]
    refine osum_ext fun m => ?_
    have hs : ((σ ^ (2 * m + 1) : ℤ) : PowerSeries ℤ) = σ := by rw [pow_succ, pow_mul, sq, hσ, one_pow, one_mul]
    rw [hs, show 2 * (2 * m + 1) + 2 = 4 * m + 4 by ring,
      show IP 1 4 4 * ((σ : PowerSeries ℤ) * X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) * QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4)
        = (σ : PowerSeries ℤ) * X ^ ((2 * m + 1 + δ) * (2 * m + 1 + δ)) * (IP 1 4 4 * QI 2 (2 * m + 1) * GI 1 (4 * m + 4) 4) by ring,
      u8]
    ring
  rw [hev, hod]

lemma expand4_Gw : expand 4 (by norm_num) Gw = osum fun m => X ^ (4 * (m * m)) * QI 4 m := by
  rw [Gw, expand_osum 4 _ (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [map_mul, map_pow, expand_X, expand_QI 4 _ 1 m le_rfl, ← pow_mul]

lemma expand2_F1w : expand 2 two_ne_zero F1w = osum fun n => X ^ (2 * (2 * (n * n + n))) * Ring.inverse (FP 1 2 4 (n + 1)) := by
  rw [F1w, expand_osum 2 _ LF_F1w]
  refine osum_ext fun n => ?_
  rw [map_mul, map_pow, expand_X, expand_inverse 2 _ (uFP 1 le_rfl 2 (n + 1)), expand_FP, ← pow_mul]

lemma expand2_P1w : expand 2 two_ne_zero P1w =
    osum fun n => (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ (2 * ((n + 1) * (n + 1))) * FP 1 2 4 n := by
  rw [P1w, expand_osum 2 two_ne_zero LF_P1w]
  refine osum_ext fun n => ?_
  rw [map_mul, map_mul, map_intCast, map_pow, expand_X, expand_FP, ← pow_mul]

lemma kern_e1 : (osum fun m => X ^ ((2 * m + 1) * (2 * m + 1)) * psi2w * QI 4 m) = X * psi2w * expand 4 (by norm_num) Hw := by
  rw [expand4_Hw, mul_osum (LF_Xpow_mul fun m => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [show (2 * m + 1) * (2 * m + 1) = 1 + 4 * (m * m + m) by ring, pow_add]; ring

lemma kern_o1 : (osum fun m => X ^ ((2 * m + 1 + 1) * (2 * m + 1 + 1)) * Ring.inverse (FP 1 2 4 (m + 1))) =
    expand 2 two_ne_zero F0w - 1 := by
  rw [expand2_F0w]
  conv_rhs => rw [osum_succ (LF_Xpow_mul fun n => by nlinarith)]
  simp only [mul_zero, pow_zero, FP_zero, Ring.inverse_one, mul_one, add_sub_cancel_left]
  refine osum_ext fun m => ?_
  rw [show (2 * m + 1 + 1) * (2 * m + 1 + 1) = 2 * (2 * ((m + 1) * (m + 1))) by ring]

lemma kern_e0 : (osum fun m => X ^ ((2 * m + 0) * (2 * m + 0)) * psi2w * QI 4 m) = psi2w * expand 4 (by norm_num) Gw := by
  rw [expand4_Gw, mul_osum (LF_Xpow_mul fun m => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [show (2 * m + 0) * (2 * m + 0) = 4 * (m * m) by ring]; ring

lemma kern_o0 : (osum fun m => X ^ ((2 * m + 1 + 0) * (2 * m + 1 + 0)) * Ring.inverse (FP 1 2 4 (m + 1))) =
    X * expand 2 two_ne_zero F1w := by
  rw [expand2_F1w, mul_osum (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [show (2 * m + 1 + 0) * (2 * m + 1 + 0) = 1 + 2 * (2 * (m * m + m)) by ring, pow_add]; ring

/-! ### (1₀) and (1₁): the `ψ` functions -/

/-- `q^e (−q;q)_n = (q²;q²)_∞ Σ_m q^{e+(2n+2)m}/((q)_n (q²;q²)_m)`. -/
lemma psi_term (e n : ℕ) :
    X ^ e * FP (-1) 1 1 n = IP 1 2 2 * osum fun m => X ^ (e + (2 * n + 2) * m) * (QI 1 n * QI 2 m) := by
  rw [FPm_eq, QF2_eq, GI,
    show X ^ e * (IP 1 2 2 * osum (gI 1 (2 * n + 2) 2) * QI 1 n) = IP 1 2 2 * (X ^ e * QI 1 n * osum (gI 1 (2 * n + 2) 2)) by ring,
    mul_osum (LF_gI 1 (by omega) 2)]
  congr 1; refine osum_ext fun m => ?_
  simp only [gI]; rw [pow_add]; push_cast; ring

/-- **(1₁)** `ψ₁(q) = ψ(q²)G(q⁴) + qF₁(q²)`. -/
theorem watson_1_1 : psi1w = psi2w * expand 4 (by norm_num) Gw + X * expand 2 two_ne_zero F1w := by
  set g : ℕ × ℕ → PowerSeries ℤ := fun p => X ^ ((p.1 + 1).choose 2 + (2 * p.1 + 2) * p.2) * (QI 1 p.1 * QI 2 p.2) with hg_def
  have hg : LF g := LF_pair fun p => by rw [choose_succ_two]; nlinarith
  have e1 : psi1w = IP 1 2 2 * osum fun n => osum fun m => g (n, m) := by
    rw [psi1w, mul_osum hg.prod_outer]
    exact osum_ext fun n => psi_term _ n
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m) * QI 2 m * IP (-1) (2 * m + 1) 1 := fun m => by
    rw [euler_prod (-1) (a := 2 * m + 1) (b := 1) (by omega) le_rfl, HP, mul_osum (LF_hP (-1) (by omega) 1)]
    refine osum_ext fun n => ?_
    simp only [hg_def, hP]
    rw [show (n + 1).choose 2 + (2 * n + 2) * m = 2 * m + ((2 * m + 1) * n + 1 * n.choose 2) by
      rw [choose_succ_two]; ring, pow_add]
    push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun p =>
    X ^ (2 * p.1 + ((2 * p.1 + 1) * p.2 + 2 * p.2.choose 2)) * (QI 4 p.1 * QI 2 p.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun p => by nlinarith
  have hL : LF fun m => X ^ (2 * m) * QI 2 m * IP (-1) (2 * m + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 2 m * IP (-1) (2 * m + 1) 1) (e := fun m => 2 * m)
      (fun m => by show m ≤ 2 * m; omega)
  have e3 : IP 1 2 2 * (osum fun m => X ^ (2 * m) * QI 2 m * IP (-1) (2 * m + 1) 1) =
      IP 1 4 4 * osum fun m => osum fun n => g2 (m, n) := by
    rw [mul_osum hL, mul_osum hg2.prod_outer]
    refine osum_ext fun m => ?_
    rw [show IP 1 2 2 * (X ^ (2 * m) * QI 2 m * IP (-1) (2 * m + 1) 1)
        = X ^ (2 * m) * (IP 1 2 2 * QI 2 m * IP (-1) (2 * m + 1) 1) by ring, U1,
      euler_prod (-1) (a := 2 * m + 1) (b := 2) (by omega) (by norm_num), HP,
      show X ^ (2 * m) * (IP 1 4 4 * QI 4 m * osum (hP (-1) (2 * m + 1) 2))
        = IP 1 4 4 * (X ^ (2 * m) * QI 4 m * osum (hP (-1) (2 * m + 1) 2)) by ring,
      mul_osum (LF_hP (-1) (by omega) 2)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; simp; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) = X ^ (n * n) * QI 2 n * GI 1 (2 * n + 2) 4 := fun n => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 4)]
    refine osum_ext fun m => ?_
    simp only [hg2_def, gI]
    rw [show 2 * m + ((2 * m + 1) * n + 2 * n.choose 2) = n * n + (2 * n + 2) * m by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer']
  simp_rw [e4]
  have hk := kern_split 1 (by norm_num) 0
  rw [kern_e0, kern_o0] at hk
  rw [← show (osum fun n => IP 1 4 4 * ((((1 : ℤ) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 0) * (n + 0)) * QI 2 n *
      GI 1 (2 * n + 2) 4)) = osum fun n => IP 1 4 4 * (X ^ (n * n) * QI 2 n * GI 1 (2 * n + 2) 4) from
    osum_ext fun n => by simp, hk]
  simp

/-- **(1₀)** `ψ₀(q) = qψ(q²)H(q⁴) + F₀(q²) − 1`. -/
theorem watson_1_0 : psi0w = X * psi2w * expand 4 (by norm_num) Hw + (expand 2 two_ne_zero F0w - 1) := by
  set g : ℕ × ℕ → PowerSeries ℤ := fun p => X ^ ((p.1 + 2).choose 2 + (2 * p.1 + 2) * p.2) * (QI 1 p.1 * QI 2 p.2) with hg_def
  have hg : LF g := LF_pair fun p => by rw [choose_succ_succ_two]; nlinarith
  have e1 : psi0w = IP 1 2 2 * osum fun n => osum fun m => g (n, m) := by
    rw [psi0w, mul_osum hg.prod_outer]
    exact osum_ext fun n => psi_term _ n
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m + 1) * QI 2 m * IP (-1) (2 * m + 2) 1 := fun m => by
    rw [euler_prod (-1) (a := 2 * m + 2) (b := 1) (by omega) le_rfl, HP, mul_osum (LF_hP (-1) (by omega) 1)]
    refine osum_ext fun n => ?_
    simp only [hg_def, hP]
    rw [show (n + 2).choose 2 + (2 * n + 2) * m = 2 * m + 1 + ((2 * m + 2) * n + 1 * n.choose 2) by
      rw [choose_succ_succ_two]; ring, pow_add]
    push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun p =>
    X ^ (2 * p.1 + 1 + ((2 * p.1 + 3) * p.2 + 2 * p.2.choose 2)) * (QI 4 p.1 * QI 2 p.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun p => by nlinarith
  have hL : LF fun m => X ^ (2 * m + 1) * QI 2 m * IP (-1) (2 * m + 2) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 2 m * IP (-1) (2 * m + 2) 1) (e := fun m => 2 * m + 1)
      (fun m => by show m ≤ 2 * m + 1; omega)
  have e3 : IP 1 2 2 * (osum fun m => X ^ (2 * m + 1) * QI 2 m * IP (-1) (2 * m + 2) 1) =
      IP 1 4 4 * osum fun m => osum fun n => g2 (m, n) := by
    rw [mul_osum hL, mul_osum hg2.prod_outer]
    refine osum_ext fun m => ?_
    rw [show IP 1 2 2 * (X ^ (2 * m + 1) * QI 2 m * IP (-1) (2 * m + 2) 1)
        = X ^ (2 * m + 1) * (IP 1 2 2 * QI 2 m * IP (-1) (2 * m + 2) 1) by ring, U0,
      euler_prod (-1) (a := 2 * m + 3) (b := 2) (by omega) (by norm_num), HP,
      show X ^ (2 * m + 1) * (IP 1 4 4 * QI 4 m * osum (hP (-1) (2 * m + 3) 2))
        = IP 1 4 4 * (X ^ (2 * m + 1) * QI 4 m * osum (hP (-1) (2 * m + 3) 2)) by ring,
      mul_osum (LF_hP (-1) (by omega) 2)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; simp; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) = X ^ ((n + 1) * (n + 1)) * QI 2 n * GI 1 (2 * n + 2) 4 := fun n => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 4)]
    refine osum_ext fun m => ?_
    simp only [hg2_def, gI]
    rw [show 2 * m + 1 + ((2 * m + 3) * n + 2 * n.choose 2) = (n + 1) * (n + 1) + (2 * n + 2) * m by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer']
  simp_rw [e4]
  have hk := kern_split 1 (by norm_num) 1
  rw [kern_e1, kern_o1] at hk
  rw [← show (osum fun n => IP 1 4 4 * ((((1 : ℤ) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 1) * (n + 1)) * QI 2 n *
      GI 1 (2 * n + 2) 4)) = osum fun n => IP 1 4 4 * (X ^ ((n + 1) * (n + 1)) * QI 2 n * GI 1 (2 * n + 2) 4) from
    osum_ext fun n => by simp, hk]
  simp

/-! ### (2₁) and (3₁): `f₁ ± ϑ₄H` -/

lemma LF_H : LF fun n => X ^ (n * n + n) * QI 1 n := LF_Xpow_mul fun n => by nlinarith

/-- `f₁ ± ϑ₄H = (q)_∞ Σ_n q^{n²+n}/(q²;q²)_n · (GI₊ ± GI₋)`. -/
lemma f1_pm (s : ℤ) :
    f1w + (s : PowerSeries ℤ) * (th4w * Hw) =
      IP 1 1 1 * osum fun n => X ^ (n * n + n) * QI 2 n * (GI 1 (n + 1) 1 + (s : PowerSeries ℤ) * GI (-1) (n + 1) 1) := by
  have l1 : LF fun n => X ^ (n * n + n) * QI 2 n * GI 1 (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 2 n * GI 1 (n + 1) 1) (e := fun n => n * n + n)
      (fun n => by show n ≤ n * n + n; nlinarith)
  have l2 : LF fun n => X ^ (n * n + n) * QI 2 n * GI (-1) (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 2 n * GI (-1) (n + 1) 1) (e := fun n => n * n + n)
      (fun n => by show n ≤ n * n + n; nlinarith)
  have hf : f1w = IP 1 1 1 * osum fun n => X ^ (n * n + n) * QI 2 n * GI 1 (n + 1) 1 := by
    rw [f1w, mul_osum l1]
    refine osum_ext fun n => ?_
    rw [pow_add]
    linear_combination X ^ n * (f0_pm_step n).1
  have hg : th4w * Hw = IP 1 1 1 * osum fun n => X ^ (n * n + n) * QI 2 n * GI (-1) (n + 1) 1 := by
    rw [th4w, Hw, mul_assoc, mul_osum LF_H]
    congr 1
    refine osum_ext fun n => ?_
    rw [pow_add]
    linear_combination X ^ n * (f0_pm_step n).2
  rw [hf, hg]
  have : (osum fun n => X ^ (n * n + n) * QI 2 n * (GI 1 (n + 1) 1 + (s : PowerSeries ℤ) * GI (-1) (n + 1) 1)) =
      (osum fun n => X ^ (n * n + n) * QI 2 n * GI 1 (n + 1) 1) +
        (s : PowerSeries ℤ) * osum fun n => X ^ (n * n + n) * QI 2 n * GI (-1) (n + 1) 1 := by
    rw [← osum_smul _ l2, ← osum_add l1 (l2.mul_left _)]
    exact osum_ext fun n => by ring
  rw [this]
  ring

/-- **(3₁)** `f₁(q) + ϑ₄(q)H(q) = 2ψ(q²)G(q⁴) − 2qF₁(q²)`. -/
theorem watson_3_1 :
    f1w + th4w * Hw = 2 * psi2w * expand 4 (by norm_num) Gw - 2 * X * expand 2 two_ne_zero F1w := by
  have h := f1_pm 1
  simp only [Int.cast_one, one_mul] at h
  rw [h]
  set g : ℕ × ℕ → PowerSeries ℤ := fun q => X ^ (q.1 * q.1 + q.1 + (2 * q.1 + 2) * q.2) * (QI 2 q.1 * QI 1 (2 * q.2)) with hg_def
  have hg : LF g := LF_pair fun q => by nlinarith
  have e1 : (osum fun n => X ^ (n * n + n) * QI 2 n * (GI 1 (n + 1) 1 + GI (-1) (n + 1) 1)) =
      2 * osum fun n => osum fun m => g (n, m) := by
    rw [← osum_smul _ hg.prod_outer]
    refine osum_ext fun n => ?_
    rw [GI_pm, Aw, show X ^ (n * n + n) * QI 2 n * (2 * osum fun m => X ^ ((2 * n + 2) * m) * QI 1 (2 * m))
      = 2 * (X ^ (n * n + n) * QI 2 n * osum fun m => X ^ ((2 * n + 2) * m) * QI 1 (2 * m)) by ring,
      mul_osum (LF_Xpow_mul fun m => by nlinarith)]
    congr 1; refine osum_ext fun m => ?_
    simp only [hg_def]; rw [pow_add]; ring
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2 := fun m => by
    rw [euler_prod (-1) (a := 2 * m + 2) (b := 2) (by omega) (by norm_num), HP, mul_osum (LF_hP (-1) (by omega) 2)]
    refine osum_ext fun n => ?_
    simp only [hg_def, hP]
    rw [show n * n + n + (2 * n + 2) * m = 2 * m + ((2 * m + 2) * n + 2 * n.choose 2) by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + ((2 * q.1 + 1) * q.2 + 2 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 4 q.1 * QI 2 q.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun q => by nlinarith
  have hL : LF fun m => X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 (2 * m) * IP (-1) (2 * m + 2) 2) (e := fun m => 2 * m)
      (fun m => by show m ≤ 2 * m; omega)
  have e3 : IP 1 1 1 * (2 * osum fun m => X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2) =
      2 * (IP 1 4 4 * osum fun m => osum fun n => g2 (m, n)) := by
    rw [mul_left_comm, mul_osum hL, mul_osum hg2.prod_outer]
    congr 1; refine osum_ext fun m => ?_
    rw [show IP 1 1 1 * (X ^ (2 * m) * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2)
      = X ^ (2 * m) * (IP 1 1 1 * QI 1 (2 * m) * IP (-1) (2 * m + 2) 2) by ring, U9,
      euler_prod 1 (a := 2 * m + 1) (b := 2) (by omega) (by norm_num), HP,
      show X ^ (2 * m) * (IP 1 4 4 * QI 4 m * osum (hP 1 (2 * m + 1) 2))
        = IP 1 4 4 * (X ^ (2 * m) * QI 4 m * osum (hP 1 (2 * m + 1) 2)) by ring,
      mul_osum (LF_hP 1 (by omega) 2)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) =
      (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * QI 2 n * GI 1 (2 * n + 2) 4 := fun n => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 4)]
    refine osum_ext fun m => ?_
    simp only [hg2_def, gI]
    rw [show 2 * m + ((2 * m + 1) * n + 2 * n.choose 2) = n * n + (2 * n + 2) * m by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer']
  simp_rw [e4]
  have hk := kern_split (-1) (by norm_num) 0
  rw [kern_e0, kern_o0] at hk
  rw [← show (osum fun n => IP 1 4 4 * ((((-1 : ℤ) ^ n : ℤ) : PowerSeries ℤ) * X ^ ((n + 0) * (n + 0)) * QI 2 n *
      GI 1 (2 * n + 2) 4)) = osum fun n => IP 1 4 4 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * QI 2 n *
      GI 1 (2 * n + 2) 4) from osum_ext fun n => by simp, hk]
  push_cast; ring

/-- **(2₁)** `q(f₁(q) − ϑ₄(q)H(q)) = −2φ₁(−q²)`. -/
theorem watson_2_1 : X * (f1w - th4w * Hw) = -2 * expand 2 two_ne_zero P1w := by
  have h := f1_pm (-1)
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg] at h
  rw [h]
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (q.1 * q.1 + q.1 + (q.1 + 1) * (2 * q.2 + 1)) * (QI 2 q.1 * QI 1 (2 * q.2 + 1)) with hg_def
  have hg : LF g := LF_pair fun q => by nlinarith
  have e1 : (osum fun n => X ^ (n * n + n) * QI 2 n * (GI 1 (n + 1) 1 - GI (-1) (n + 1) 1)) =
      2 * osum fun n => osum fun m => g (n, m) := by
    rw [← osum_smul _ hg.prod_outer]
    refine osum_ext fun n => ?_
    rw [GI_mp, show X ^ (n * n + n) * QI 2 n * (2 * osum fun m => X ^ ((n + 1) * (2 * m + 1)) * QI 1 (2 * m + 1))
      = 2 * (X ^ (n * n + n) * QI 2 n * osum fun m => X ^ ((n + 1) * (2 * m + 1)) * QI 1 (2 * m + 1)) by ring,
      mul_osum (LF_Xpow_mul fun m => by nlinarith)]
    congr 1; refine osum_ext fun m => ?_
    simp only [hg_def]; rw [pow_add]; ring
  have e2 : ∀ m, (osum fun n => g (n, m)) = X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2 :=
    fun m => by
      rw [euler_prod (-1) (a := 2 * m + 3) (b := 2) (by omega) (by norm_num), HP, mul_osum (LF_hP (-1) (by omega) 2)]
      refine osum_ext fun n => ?_
      simp only [hg_def, hP]
      rw [show n * n + n + (n + 1) * (2 * m + 1) = 2 * m + 1 + ((2 * m + 3) * n + 2 * n.choose 2) by
        have := two_choose_two n; nlinarith, pow_add]
      push_cast; simp; ring
  rw [e1, osum_prod_swap hg]
  simp_rw [e2]
  set g2 : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + 1 + ((4 * q.1 + 6) * q.2 + 4 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 2 q.1 * QI 4 q.2) with hg2_def
  have hg2 : LF g2 := LF_pair fun q => by nlinarith
  have hL : LF fun m => X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2)
      (e := fun m => 2 * m + 1) (fun m => by show m ≤ 2 * m + 1; omega)
  have e3 : IP 1 1 1 * (2 * osum fun m => X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2) =
      2 * (IP 1 2 2 * osum fun m => osum fun n => g2 (m, n)) := by
    rw [mul_left_comm, mul_osum hL, mul_osum hg2.prod_outer]
    congr 1; refine osum_ext fun m => ?_
    rw [show IP 1 1 1 * (X ^ (2 * m + 1) * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2)
      = X ^ (2 * m + 1) * (IP 1 1 1 * QI 1 (2 * m + 1) * IP (-1) (2 * m + 3) 2) by ring, U10,
      euler_prod 1 (a := 4 * m + 6) (b := 4) (by omega) (by norm_num), HP,
      show X ^ (2 * m + 1) * (IP 1 2 2 * QI 2 m * osum (hP 1 (4 * m + 6) 4))
        = IP 1 2 2 * (X ^ (2 * m + 1) * QI 2 m * osum (hP 1 (4 * m + 6) 4)) by ring,
      mul_osum (LF_hP 1 (by omega) 4)]
    congr 1; refine osum_ext fun n => ?_
    simp only [hg2_def, hP]; rw [pow_add]; push_cast; ring
  have e4 : ∀ n, (osum fun m => g2 (m, n)) =
      (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n) + 4 * n + 1) * QI 4 n * GI 1 (4 * n + 2) 2 := fun n => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 2)]
    refine osum_ext fun m => ?_
    simp only [hg2_def, gI]
    rw [show 2 * m + 1 + ((4 * m + 6) * n + 4 * n.choose 2) = 2 * (n * n) + 4 * n + 1 + (4 * n + 2) * m by
      have := two_choose_two n; nlinarith, pow_add]
    push_cast; ring
  rw [e3, osum_prod_swap hg2, mul_osum hg2.prod_outer']
  simp_rw [e4]
  rw [expand2_P1w, mul_left_comm, mul_osum (LF.of_nat fun n k hk => by
      rw [show IP 1 2 2 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n) + 4 * n + 1) * QI 4 n * GI 1 (4 * n + 2) 2)
        = X ^ (2 * (n * n) + 4 * n + 1) * (IP 1 2 2 * (((-1) ^ n : ℤ) : PowerSeries ℤ) * QI 4 n * GI 1 (4 * n + 2) 2) by ring,
        coeff_X_pow_mul', if_neg (by nlinarith)])]
  rw [show (-2 : PowerSeries ℤ) * osum (fun n => (((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ (2 * ((n + 1) * (n + 1))) *
      FP 1 2 4 n) = 2 * osum (fun n => -((((-1) ^ (n + 1) : ℤ) : PowerSeries ℤ) * X ^ (2 * ((n + 1) * (n + 1))) *
      FP 1 2 4 n)) by rw [osum_neg]; ring]
  congr 1
  refine osum_ext fun n => ?_
  rw [show X * (IP 1 2 2 * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n) + 4 * n + 1) * QI 4 n * GI 1 (4 * n + 2) 2))
    = (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (2 * (n * n) + 4 * n + 1 + 1) * (IP 1 2 2 * QI 4 n * GI 1 (4 * n + 2) 2) by ring,
    u5, show 2 * (n * n) + 4 * n + 1 + 1 = 2 * ((n + 1) * (n + 1)) by ring]
  push_cast; ring

end MockTheta5All
