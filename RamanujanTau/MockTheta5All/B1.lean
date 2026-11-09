/-
# Watson's (B₁): `χ₁(q) = 2F₁(q) + q⁻¹φ₁(−q)`

G. N. Watson, *The mock theta functions (2)*, Proc. LMS (2) 42 (1937), §3, pp. 281–282. The proof is that of
(B₀) (`Watson.chi0_R1_watson`, `RamanujanTau/Watson/R1.lean`) with odd parts in place of even parts:

* By (E2), `χ₁/(q)_∞ = Σ_m qᵐ/(q)_m · A'(m+1)`, where `A'(c) = Σ_n q^{cn}/(q)_{2n+1}`.
* Split `m` by parity.
  - For even `m`, `A'(c) = B'(c)/(q^c;q²)_∞` by the odd part of Euler (`euler_odd`), and the even half gives `F₁`.
  - For odd `m = 2n+1`, `2q^{n+1}A'(2n+2) = 1/(q^{n+1};q)_∞ − 1/(−q^{n+1};q)_∞`. The first piece gives `χ₁`
    back (no second series form is needed, unlike (B₀)), and the second gives `−q⁻¹φ₁(−q)`.

Hence `2χ₁ = 2F₁ + χ₁ + q⁻¹φ₁(−q)`.
-/
import RamanujanTau.MockTheta5All.Rel

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MockTheta5All
open PowerSeries Watson Finset

/-- `A'(c) = Σ_n q^{cn}/(q)_{2n+1}`. -/
noncomputable def Aodd (c : ℕ) : PowerSeries ℤ := osum fun n => X ^ (c * n) * QI 1 (2 * n + 1)

/-- `B'(c) = Σ_p q^{cp + C(2p+1,2)}/(q)_{2p+1}`. -/
noncomputable def Bodd (c : ℕ) : PowerSeries ℤ := osum fun p => X ^ (c * p + (2 * p + 1).choose 2) * QI 1 (2 * p + 1)

lemma two_ne_zero_PS : (2 : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  rw [show (2 : PowerSeries ℤ) = C 2 by simp, coeff_C, if_pos rfl, map_zero] at this
  norm_num at this

/-- **the odd part of Euler**: `(X^c; X²)_∞ · Σ_n X^{cn}/(q;q)_{2n+1} = Σ_p X^{cp + C(2p+1,2)}/(q;q)_{2p+1}`. -/
theorem euler_odd {c : ℕ} (hc : 1 ≤ c) : IP 1 c 2 * Aodd c = Bodd c := by
  have h2 : (2 : ℕ) ≠ 0 := two_ne_zero
  set T : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ := expand 2 h2
  have hA : LF (fun n => X ^ (c * n) * QI 1 (2 * n + 1) : ℕ → PowerSeries ℤ) :=
    LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
  have hB : LF (fun p => X ^ (c * p + (2 * p + 1).choose 2) * QI 1 (2 * p + 1) : ℕ → PowerSeries ℤ) :=
    LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
  have TA : X ^ c * T (Aodd c) = osum fun n => X ^ (c * (2 * n + 1)) * QI 2 (2 * n + 1) := by
    rw [Aodd, expand_osum 2 h2 hA, mul_osum (hA.expand 2 h2)]
    refine osum_ext fun n => ?_
    rw [map_mul, map_pow, expand_X, expand_QI 2 h2 1 _ le_rfl, ← pow_mul, ← mul_assoc, ← pow_add]; ring_nf
  have TB : X ^ c * T (Bodd c) =
      osum fun p => X ^ (c * (2 * p + 1) + 2 * (2 * p + 1).choose 2) * QI 2 (2 * p + 1) := by
    rw [Bodd, expand_osum 2 h2 hB, mul_osum (hB.expand 2 h2)]
    refine osum_ext fun n => ?_
    rw [map_mul, map_pow, expand_X, expand_QI 2 h2 1 _ le_rfl, ← pow_mul, ← mul_assoc, ← pow_add]; ring_nf
  have hGdiff : GI 1 c 2 - GI (-1) c 2 = 2 * (X ^ c * T (Aodd c)) := by
    rw [TA, GI, GI, ← osum_sub (LF_gI 1 hc 2) (LF_gI (-1) hc 2)]
    have hu : LF (fun k => X ^ (c * k) * QI 2 k : ℕ → PowerSeries ℤ) :=
      LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
    rw [← osum_odd_part hu]
    refine osum_ext fun k => ?_
    simp only [gI]; push_cast; ring
  have hHdiff : HP (-1) c 2 - HP 1 c 2 = 2 * (X ^ c * T (Bodd c)) := by
    rw [TB, HP, HP, ← osum_sub (LF_hP (-1) hc 2) (LF_hP 1 hc 2)]
    have hu : LF (fun k => X ^ (c * k + 2 * k.choose 2) * QI 2 k : ℕ → PowerSeries ℤ) :=
      LF.of_nat fun n k hk => by rw [coeff_X_pow_mul', if_neg (by nlinarith)]
    rw [← osum_odd_part hu]
    refine osum_ext fun k => ?_
    simp only [hP]; push_cast; ring_nf
  have u1 := isUnit_IP 1 hc (show 1 ≤ 2 by norm_num)
  have u2 := isUnit_IP (-1) hc (show 1 ≤ 2 by norm_num)
  have hsq : IP 1 c 2 * IP (-1) c 2 = T (IP 1 c 2) := by
    rw [IP_sq 1 hc (show 1 ≤ 2 by norm_num), expand_IP 2 h2 1 hc (show 1 ≤ 2 by norm_num)]; norm_num
  have key : T (IP 1 c 2) * (2 * (X ^ c * T (Aodd c))) = 2 * (X ^ c * T (Bodd c)) := by
    rw [← hGdiff, ← hHdiff, ← euler_prod 1 hc (by norm_num), ← euler_prod (-1) hc (by norm_num),
      GI_eq 1 hc (by norm_num), GI_eq (-1) hc (by norm_num), ← hsq]
    have e1 := Ring.mul_inverse_cancel _ u1
    have e2 := Ring.mul_inverse_cancel _ u2
    linear_combination (IP (-1) c 2) * e1 - (IP 1 c 2) * e2
  apply expand_injective 2 h2
  rw [map_mul]
  have hne : (2 : PowerSeries ℤ) * X ^ c ≠ 0 := mul_ne_zero two_ne_zero_PS (pow_ne_zero _ X_ne_zero)
  apply mul_left_cancel₀ hne
  linear_combination key

/-- **Step 1** (E2 and Fubini): `χ₁/(q)_∞ = Σ_m qᵐ/(q)_m · A'(m+1)`. -/
lemma step1_chi1 : Ring.inverse (IP 1 1 1) * chi1w = osum fun m => X ^ m * QI 1 m * Aodd (m + 1) := by
  set f : ℕ × ℕ → PowerSeries ℤ := fun p => X ^ (p.1 + (p.1 + 1) * p.2) * (QI 1 (2 * p.1 + 1) * QI 1 p.2) with hf_def
  have hf : LF f := LF_pair (fun p => by nlinarith)
  have hchi : chi1w = osum fun n => X ^ n * (QF 1 n * QI 1 (2 * n + 1)) := by
    rw [chi1w]; exact osum_ext fun n => by rw [inv_chiPoch']
  rw [hchi, mul_osum (LF_Xpow_mul fun n => le_refl n)]
  have h1 : (osum fun n => Ring.inverse (IP 1 1 1) * (X ^ n * (QF 1 n * QI 1 (2 * n + 1)))) =
      osum fun n => osum fun m => f (n, m) := by
    refine osum_ext fun n => ?_
    rw [show Ring.inverse (IP 1 1 1) * (X ^ n * (QF 1 n * QI 1 (2 * n + 1)))
      = X ^ n * QI 1 (2 * n + 1) * (Ring.inverse (IP 1 1 1) * QF 1 n) by ring, QF_div_E, GI,
      mul_osum (LF_gI 1 (by omega) 1)]
    refine osum_ext fun m => ?_
    simp only [hf_def, gI]
    rw [pow_add]; push_cast; ring
  rw [h1, osum_prod_swap hf]
  refine osum_ext fun m => ?_
  rw [Aodd, mul_osum (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun n => ?_
  simp only [hf_def]
  rw [show n + (n + 1) * m = m + (m + 1) * n by ring, pow_add]; ring

lemma choose_odd_two (p : ℕ) : (2 * p + 1).choose 2 = 2 * (p * p) + p := by
  have h1 := choose_succ_two (2 * p)
  have h2 := choose_two_mul_add p
  omega

lemma unit_even2' (p : ℕ) :
    IP 1 2 2 * QI 1 (2 * p + 1) * GI 1 (2 * p + 2) 2 = Ring.inverse (FP 1 1 2 (p + 1)) := by
  symm
  apply inv_eq_of_mul_eq_one
  have s1 : IP 1 2 2 = FP 1 2 2 p * IP 1 (2 * p + 2) 2 := by
    rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) p]; ring_nf
  have e1 := QF_mul_QI 1 (2 * p + 1) le_rfl
  rw [QF_two_succ] at e1
  have e3 : IP 1 (2 * p + 2) 2 * GI 1 (2 * p + 2) 2 = 1 := euler_inv 1 (by omega) (by norm_num)
  calc FP 1 1 2 (p + 1) * (IP 1 2 2 * QI 1 (2 * p + 1) * GI 1 (2 * p + 2) 2)
      = (FP 1 1 2 (p + 1) * FP 1 2 2 p * QI 1 (2 * p + 1)) * (IP 1 (2 * p + 2) 2 * GI 1 (2 * p + 2) 2) := by
        rw [s1]; ring
    _ = 1 := by rw [e1, e3, one_mul]

/-- **T₁′**: `(q)_∞ Σ_n q^{2n}/(q)_{2n} · A'(2n+1) = F₁`. -/
lemma even_piece_chi1 : IP 1 1 1 * (osum fun n => X ^ (2 * n) * QI 1 (2 * n) * Aodd (2 * n + 1)) = F1w := by
  have hA : ∀ n, Aodd (2 * n + 1) = Ring.inverse (IP 1 (2 * n + 1) 2) * Bodd (2 * n + 1) := fun n => by
    rw [← euler_odd (show 1 ≤ 2 * n + 1 by omega), ← mul_assoc,
      Ring.inverse_mul_cancel _ (uIP 1 (show 1 ≤ 2 * n + 1 by omega) (show 1 ≤ 2 by norm_num)), one_mul]
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + ((2 * q.1 + 1) * q.2 + (2 * q.2 + 1).choose 2)) * (QI 2 q.1 * QI 1 (2 * q.2 + 1)) with hg_def
  have hg : LF g := LF_pair (fun q => by nlinarith)
  have hL : LF fun n => X ^ (2 * n) * QI 1 (2 * n) * Aodd (2 * n + 1) := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n) * Aodd (2 * n + 1)) (e := fun n => 2 * n)
      (fun n => by show n ≤ 2 * n; omega)
  rw [mul_osum hL]
  have h1 : (osum fun n => IP 1 1 1 * (X ^ (2 * n) * QI 1 (2 * n) * Aodd (2 * n + 1))) =
      IP 1 2 2 * osum fun n => osum fun p => g (n, p) := by
    rw [← osum_smul _ hg.prod_outer]
    refine osum_ext fun n => ?_
    rw [hA n, show IP 1 1 1 * (X ^ (2 * n) * QI 1 (2 * n) * (Ring.inverse (IP 1 (2 * n + 1) 2) * Bodd (2 * n + 1)))
      = X ^ (2 * n) * (IP 1 1 1 * QI 1 (2 * n) * Ring.inverse (IP 1 (2 * n + 1) 2)) * Bodd (2 * n + 1) by ring,
      unit_even1, Bodd, mul_osum (LF_Xpow_mul fun p => by nlinarith), mul_osum (hg.prod_left n)]
    refine osum_ext fun p => ?_
    simp only [hg_def]
    rw [pow_add]; ring
  rw [h1, osum_prod_swap hg, F1w, mul_osum hg.prod_outer']
  refine osum_ext fun p => ?_
  have hin : (osum fun n => g (n, p)) = X ^ (2 * (p * p + p)) * QI 1 (2 * p + 1) * GI 1 (2 * p + 2) 2 := by
    rw [GI, mul_osum (LF_gI 1 (by omega) 2)]
    refine osum_ext fun n => ?_
    simp only [hg_def, gI]
    rw [show 2 * n + ((2 * n + 1) * p + (2 * p + 1).choose 2) = 2 * (p * p + p) + (2 * p + 2) * n by
      rw [choose_odd_two]; ring, pow_add]
    push_cast; ring
  rw [hin, show IP 1 2 2 * (X ^ (2 * (p * p + p)) * QI 1 (2 * p + 1) * GI 1 (2 * p + 2) 2)
    = X ^ (2 * (p * p + p)) * (IP 1 2 2 * QI 1 (2 * p + 1) * GI 1 (2 * p + 2) 2) by ring, unit_even2']

/-- `2q^{n+1}A'(2n+2) = 1/(q^{n+1};q)_∞ − 1/(−q^{n+1};q)_∞`. -/
lemma GI_mp' (n : ℕ) : GI 1 (n + 1) 1 - GI (-1) (n + 1) 1 = 2 * (X ^ (n + 1) * Aodd (2 * n + 2)) := by
  rw [GI_mp, Aodd]
  congr 1
  rw [mul_osum (LF_Xpow_mul fun m => by nlinarith)]
  refine osum_ext fun m => ?_
  rw [← mul_assoc, ← pow_add]; ring_nf

/-- **T₂′**: `(q)_∞ Σ_n qⁿ/(q)_{2n+1} · 1/(q^{n+1};q)_∞ = χ₁`. -/
lemma odd_piece2_chi1 :
    IP 1 1 1 * (osum fun n => X ^ n * QI 1 (2 * n + 1) * GI 1 (n + 1) 1) = chi1w := by
  have hL : LF fun n => X ^ n * QI 1 (2 * n + 1) * GI 1 (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
      (e := fun n => n) (fun n => le_refl n)
  rw [mul_osum hL, chi1w]
  refine osum_ext fun n => ?_
  rw [inv_chiPoch', show IP 1 1 1 * (X ^ n * QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
    = X ^ n * QI 1 (2 * n + 1) * (IP 1 1 1 * GI 1 (n + 1) 1) by ring, E_mul_GI]
  ring

/-- **T₃′**: `(q)_∞ Σ_n qⁿ/(q)_{2n+1} · 1/(−q^{n+1};q)_∞ = Σ_m (−1)ᵐ q^{m²+2m}(q;q²)_m`. -/
lemma odd_piece3_chi1 :
    IP 1 1 1 * (osum fun n => X ^ n * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1) =
      osum fun m => (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * FP 1 1 2 m := by
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (q.1 + ((2 * q.1 + 3) * q.2 + 2 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 2 q.2 * QI 1 q.1) with hg_def
  have hg : LF g := LF_pair (fun q => by nlinarith)
  have h1 : (osum fun n => X ^ n * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1) =
      osum fun n => osum fun m => g (n, m) := by
    refine osum_ext fun n => ?_
    rw [mul_assoc, unit_odd3, euler_prod 1 (by omega) (by norm_num), HP,
      show X ^ n * (osum (hP 1 (2 * n + 3) 2) * QI 1 n) = X ^ n * QI 1 n * osum (hP 1 (2 * n + 3) 2) by ring,
      mul_osum (LF_hP 1 (by omega) 2)]
    refine osum_ext fun m => ?_
    simp only [hg_def, hP]
    rw [pow_add]; push_cast; ring
  have h2 : ∀ m, (osum fun n => g (n, m)) =
      (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * QI 2 m * GI 1 (2 * m + 1) 1 := fun m => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 1)]
    refine osum_ext fun n => ?_
    simp only [hg_def, gI]
    rw [show n + ((2 * n + 3) * m + 2 * m.choose 2) = m * m + 2 * m + (2 * m + 1) * n by
      have := two_choose_two m; nlinarith, pow_add]
    push_cast; ring
  rw [h1, osum_prod_swap hg, mul_osum hg.prod_outer']
  refine osum_ext fun m => ?_
  rw [h2 m, show IP 1 1 1 * ((((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * QI 2 m * GI 1 (2 * m + 1) 1)
    = (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * QI 2 m * (IP 1 1 1 * GI 1 (2 * m + 1) 1) by ring,
    E_mul_GI, QF_two]
  have e := QF_mul_QI 2 m (by norm_num)
  rw [QF] at e
  linear_combination ((((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * FP 1 1 2 m) * e

lemma P1w_eq : P1w = -(X * osum fun m => (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * FP 1 1 2 m) := by
  have hL : LF fun m => (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * FP 1 1 2 m :=
    LF.of_nat fun n k hk => by
      rw [show (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n + 2 * n) * FP 1 1 2 n
        = X ^ (n * n + 2 * n) * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * FP 1 1 2 n) by ring,
        coeff_X_pow_mul', if_neg (by nlinarith)]
  rw [P1w, mul_osum hL, ← osum_neg]
  refine osum_ext fun m => ?_
  rw [show (m + 1) * (m + 1) = 1 + (m * m + 2 * m) by ring, pow_add]
  push_cast; ring

/-- **Ramanujan's (B₁), proved as Watson did**: `qχ₁(q) = 2qF₁(q) + φ₁(−q)`. -/
theorem watson_B1 : X * chi1w = 2 * X * F1w + P1w := by
  have uE : IsUnit (IP 1 1 1) := uIP 1 le_rfl le_rfl
  have hh : LF fun m => X ^ m * QI 1 m * Aodd (m + 1) := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 m * Aodd (m + 1)) (e := fun m => m) (fun m => le_refl m)
  have hs := step1_chi1
  rw [osum_parity hh] at hs
  have hodd : 2 * (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * Aodd (2 * n + 1 + 1)) =
      (osum fun n => X ^ n * QI 1 (2 * n + 1) * GI 1 (n + 1) 1) -
        osum fun n => X ^ n * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 := by
    have l1 : LF fun n => X ^ n * QI 1 (2 * n + 1) * GI 1 (n + 1) 1 := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
        (e := fun n => n) (fun n => le_refl n)
    have l2 : LF fun n => X ^ n * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI (-1) (n + 1) 1)
        (e := fun n => n) (fun n => le_refl n)
    have l3 : LF fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * Aodd (2 * n + 1 + 1) := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * Aodd (2 * n + 1 + 1))
        (e := fun n => 2 * n + 1) (fun n => by show n ≤ 2 * n + 1; omega)
    rw [← osum_sub l1 l2, ← osum_smul _ l3]
    refine osum_ext fun n => ?_
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, ← mul_sub, GI_mp']; ring
  have hchi : chi1w = IP 1 1 1 * (Ring.inverse (IP 1 1 1) * chi1w) := by
    rw [← mul_assoc, Ring.mul_inverse_cancel _ uE, one_mul]
  have key : 2 * chi1w = 2 * F1w + chi1w -
      osum fun m => (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ (m * m + 2 * m) * FP 1 1 2 m := by
    rw [← odd_piece3_chi1]
    conv_rhs => rw [← odd_piece2_chi1]
    rw [← even_piece_chi1]
    conv_lhs => rw [hchi, hs]
    linear_combination (IP 1 1 1) * hodd
  rw [P1w_eq]
  linear_combination X * key
end MockTheta5All
