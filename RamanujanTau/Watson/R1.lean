/-
# Watson's proof of Ramanujan's (B₀) = R1: `χ₀(q) = 2F₀(q) − φ₀(−q)`

G. N. Watson, *The mock theta functions (2)*, Proc. LMS (2) 42 (1937), §3, pp. 280–281
(see `docs/watson1937_R1_proof.md`). In outline:

* By (E2), `2χ₀/(q)_∞ = Σ_m qᵐ/(q)_m · 2A(m+1)`, where `A(c) = Σ_n q^{cn}/(q)_{2n}`.
* Split `m` by parity.
  - For even `m`, `A(c) = B(c)/(q^c;q²)_∞` by the even part of Euler (`euler_even`).
  - For odd `m`, `2A(2n+2) = 1/(q^{n+1};q)_∞ + 1/(−q^{n+1};q)_∞`.
* This gives three pieces `T₁, T₂, T₃`, and multiplying each by `(q)_∞`:
  - `(q)_∞T₁ = 2F₀`;
  - `(q)_∞T₂ = χ₀ − 1`, by (A₀);
  - `(q)_∞T₃ = 1 − φ₀(−q)`.
-/
import RamanujanTau.Watson.A0

set_option autoImplicit false

namespace Watson
open PowerSeries Finset

/-- `F₀ = Σ q^{2n²}/(q;q²)_n`. -/
noncomputable def F0w : PowerSeries ℤ := osum fun n => X ^ (2 * (n * n)) * Ring.inverse (FP 1 1 2 n)

/-- `φ₀(−q) = Σ (−1)ⁿ q^{n²}(q;q²)_n`. -/
noncomputable def P0w : PowerSeries ℤ := osum fun n => (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * FP 1 1 2 n

/-! ### unit bookkeeping -/

lemma inv_eq_of_mul_eq_one {u v : PowerSeries ℤ} (h : u * v = 1) : Ring.inverse u = v := by
  have hu : IsUnit u := IsUnit.of_mul_eq_one v h
  calc Ring.inverse u = Ring.inverse u * (u * v) := by rw [h, mul_one]
    _ = v := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

lemma inv_mul' {u v : PowerSeries ℤ} (hu : IsUnit u) (hv : IsUnit v) :
    Ring.inverse (u * v) = Ring.inverse u * Ring.inverse v := by
  apply inv_eq_of_mul_eq_one
  calc u * v * (Ring.inverse u * Ring.inverse v) = (u * Ring.inverse u) * (v * Ring.inverse v) := by ring
    _ = 1 := by rw [Ring.mul_inverse_cancel _ hu, Ring.mul_inverse_cancel _ hv, one_mul]

lemma uFP (c : ℤ) {a : ℕ} (ha : 1 ≤ a) (b n : ℕ) : IsUnit (FP c a b n) := isUnit_FP c ha b n

lemma uIP (c : ℤ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : IsUnit (IP c a b) := isUnit_IP c ha hb

/-- `1/(q^{n+1};q)_n = (q;q)_n/(q;q)_{2n}`. -/
lemma inv_chiPoch (n : ℕ) : Ring.inverse (FP 1 (n + 1) 1 n) = QF 1 n * QI 1 (2 * n) := by
  apply inv_eq_of_mul_eq_one
  have e : QF 1 n * FP 1 (n + 1) 1 n = QF 1 (2 * n) := by
    rw [QF, QF, show 2 * n = n + n by ring, FP_add 1 1 1 n n]; ring_nf
  calc FP 1 (n + 1) 1 n * (QF 1 n * QI 1 (2 * n)) = (QF 1 n * FP 1 (n + 1) 1 n) * QI 1 (2 * n) := by ring
    _ = 1 := by rw [e, QF_mul_QI 1 _ le_rfl]

/-- `1/(q^{n+1};q)_{n+1} = (q;q)_n/(q;q)_{2n+1}`. -/
lemma inv_chiPoch' (n : ℕ) : Ring.inverse (FP 1 (n + 1) 1 (n + 1)) = QF 1 n * QI 1 (2 * n + 1) := by
  apply inv_eq_of_mul_eq_one
  have e : QF 1 n * FP 1 (n + 1) 1 (n + 1) = QF 1 (2 * n + 1) := by
    rw [QF, QF, show 2 * n + 1 = n + (n + 1) by ring, FP_add 1 1 1 n (n + 1)]; ring_nf
  calc FP 1 (n + 1) 1 (n + 1) * (QF 1 n * QI 1 (2 * n + 1))
      = (QF 1 n * FP 1 (n + 1) 1 (n + 1)) * QI 1 (2 * n + 1) := by ring
    _ = 1 := by rw [e, QF_mul_QI 1 _ le_rfl]

/-- `(q;q)_n/(q;q)_∞ = 1/(q^{n+1};q)_∞`. -/
lemma QF_div_E (n : ℕ) : Ring.inverse (IP 1 1 1) * QF 1 n = GI 1 (n + 1) 1 := by
  rw [GI_eq 1 (by omega) le_rfl, IP_split1 n, inv_mul' (uFP 1 le_rfl 1 n) (uIP 1 (by omega) le_rfl)]
  rw [mul_comm (Ring.inverse (QF 1 n)), mul_assoc, Ring.inverse_mul_cancel _ (uFP 1 le_rfl 1 n), mul_one]

lemma two_choose_two (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    nlinarith

lemma LF_pair {g : ℕ × ℕ → PowerSeries ℤ} {e : ℕ × ℕ → ℕ} (he : ∀ p, p.1 + p.2 ≤ e p) :
    LF fun p => X ^ (e p) * g p :=
  LF.of_order (fun p => p.1 + p.2)
    (fun p k hk => by
      simp only at hk
      rw [coeff_X_pow_mul', if_neg (by have := he p; omega)])
    (fun k => ((Set.finite_Iic k).prod (Set.finite_Iic k)).subset fun p hp => by
      simp only [Set.mem_setOf_eq] at hp
      exact ⟨by simp; omega, by simp; omega⟩)

/-- `A(c) = Σ_n q^{cn}/(q)_{2n}`. -/
noncomputable def Aw (c : ℕ) : PowerSeries ℤ := osum fun n => X ^ (c * n) * QI 1 (2 * n)

/-- `B(c) = Σ_p q^{cp + C(2p,2)}/(q)_{2p}`. -/
noncomputable def Bw (c : ℕ) : PowerSeries ℤ := osum fun p => X ^ (c * p + (2 * p).choose 2) * QI 1 (2 * p)

/-- **Step 1** (E2 and Fubini): `χ₀/(q)_∞ = Σ_m qᵐ/(q)_m · A(m+1)`. -/
lemma step1 : Ring.inverse (IP 1 1 1) * chiA = osum fun m => X ^ m * QI 1 m * Aw (m + 1) := by
  set f : ℕ × ℕ → PowerSeries ℤ := fun p => X ^ (p.1 + (p.1 + 1) * p.2) * (QI 1 (2 * p.1) * QI 1 p.2) with hf_def
  have hf : LF f := LF_pair (fun p => by nlinarith)
  have hchi : chiA = osum fun n => X ^ n * (QF 1 n * QI 1 (2 * n)) := by
    rw [chiA]; exact osum_ext fun n => by rw [inv_chiPoch]
  rw [hchi, mul_osum (LF_Xpow_mul fun n => le_refl n)]
  have h1 : (osum fun n => Ring.inverse (IP 1 1 1) * (X ^ n * (QF 1 n * QI 1 (2 * n)))) =
      osum fun n => osum fun m => f (n, m) := by
    refine osum_ext fun n => ?_
    rw [show Ring.inverse (IP 1 1 1) * (X ^ n * (QF 1 n * QI 1 (2 * n)))
      = X ^ n * QI 1 (2 * n) * (Ring.inverse (IP 1 1 1) * QF 1 n) by ring, QF_div_E, GI,
      mul_osum (LF_gI 1 (by omega) 1)]
    refine osum_ext fun m => ?_
    simp only [hf_def, gI]
    rw [pow_add]; push_cast; ring
  rw [h1, osum_prod_swap hf]
  refine osum_ext fun m => ?_
  rw [Aw, mul_osum (LF_Xpow_mul fun n => by nlinarith)]
  refine osum_ext fun n => ?_
  simp only [hf_def]
  rw [show n + (n + 1) * m = m + (m + 1) * n by ring, pow_add]; ring

/-! ### the even piece `T₁` -/

lemma QF_two (n : ℕ) : QF 1 (2 * n) = FP 1 1 2 n * FP 1 2 2 n := by
  rw [QF, FP_two]

lemma QF_two_succ (n : ℕ) : QF 1 (2 * n + 1) = FP 1 1 2 (n + 1) * FP 1 2 2 n := by
  rw [QF, FP_two_succ]

lemma IP_E : IP 1 1 1 = IP 1 1 2 * IP 1 2 2 := by
  rw [IP_two 1 (a := 1) (b := 1) le_rfl le_rfl]

lemma unit_even1 (n : ℕ) :
    IP 1 1 1 * QI 1 (2 * n) * Ring.inverse (IP 1 (2 * n + 1) 2) = IP 1 2 2 * QI 2 n := by
  have u1 := uFP 1 (show 1 ≤ 1 by rfl) 2 n
  have u2 := uFP 1 (show 1 ≤ 2 by norm_num) 2 n
  have u3 := uIP 1 (show 1 ≤ 2 * n + 1 by omega) (show 1 ≤ 2 by norm_num)
  apply ((u1.mul u2).mul u3).mul_right_cancel
  have s1 : IP 1 1 2 = FP 1 1 2 n * IP 1 (2 * n + 1) 2 := by
    rw [IP_split 1 (a := 1) (b := 2) le_rfl (by norm_num) n]; ring_nf
  have e1 := QF_mul_QI 1 (2 * n) le_rfl
  have e2 := QF_mul_QI 2 n (by norm_num)
  have e3 := Ring.inverse_mul_cancel _ u3
  rw [QF_two] at e1
  calc IP 1 1 1 * QI 1 (2 * n) * Ring.inverse (IP 1 (2 * n + 1) 2) * (FP 1 1 2 n * FP 1 2 2 n * IP 1 (2 * n + 1) 2)
      = IP 1 1 1 * (FP 1 1 2 n * FP 1 2 2 n * QI 1 (2 * n)) * (Ring.inverse (IP 1 (2 * n + 1) 2) * IP 1 (2 * n + 1) 2) := by ring
    _ = IP 1 2 2 * (QF 2 n * QI 2 n) * (FP 1 1 2 n * IP 1 (2 * n + 1) 2) := by
      rw [e1, e3, e2, ← s1, IP_E]; ring
    _ = IP 1 2 2 * QI 2 n * (FP 1 1 2 n * FP 1 2 2 n * IP 1 (2 * n + 1) 2) := by rw [QF]; ring

lemma unit_even2 (p : ℕ) :
    IP 1 2 2 * QI 1 (2 * p) * GI 1 (2 * p + 2) 2 = Ring.inverse (FP 1 1 2 p) := by
  have u1 := uFP 1 (show 1 ≤ 1 by rfl) 2 p
  have u2 := uFP 1 (show 1 ≤ 2 by norm_num) 2 p
  have u3 := uIP 1 (show 1 ≤ 2 * p + 2 by omega) (show 1 ≤ 2 by norm_num)
  apply ((u1.mul u2).mul u3).mul_right_cancel
  have s1 : IP 1 2 2 = FP 1 2 2 p * IP 1 (2 * p + 2) 2 := by
    rw [IP_split 1 (a := 2) (b := 2) (by norm_num) (by norm_num) p]; ring_nf
  have e1 := QF_mul_QI 1 (2 * p) le_rfl
  rw [QF_two] at e1
  have e3 : GI 1 (2 * p + 2) 2 * IP 1 (2 * p + 2) 2 = 1 := by
    rw [mul_comm]; exact euler_inv 1 (by omega) (by norm_num)
  have e4 := Ring.inverse_mul_cancel _ u1
  calc IP 1 2 2 * QI 1 (2 * p) * GI 1 (2 * p + 2) 2 * (FP 1 1 2 p * FP 1 2 2 p * IP 1 (2 * p + 2) 2)
      = IP 1 2 2 * (FP 1 1 2 p * FP 1 2 2 p * QI 1 (2 * p)) * (GI 1 (2 * p + 2) 2 * IP 1 (2 * p + 2) 2) := by ring
    _ = IP 1 2 2 := by rw [e1, e3]; ring
    _ = (Ring.inverse (FP 1 1 2 p) * FP 1 1 2 p) * (FP 1 2 2 p * IP 1 (2 * p + 2) 2) := by rw [e4, ← s1, one_mul]
    _ = Ring.inverse (FP 1 1 2 p) * (FP 1 1 2 p * FP 1 2 2 p * IP 1 (2 * p + 2) 2) := by ring

lemma choose_two_mul_add (p : ℕ) : p + (2 * p).choose 2 = 2 * (p * p) := by
  have := two_choose_two (2 * p); nlinarith

/-- **T₁**: `(q)_∞ Σ_n q^{2n}/(q)_{2n} · A(2n+1) = F₀`. -/
lemma even_piece : IP 1 1 1 * (osum fun n => X ^ (2 * n) * QI 1 (2 * n) * Aw (2 * n + 1)) = F0w := by
  have hA : ∀ n, Aw (2 * n + 1) = Ring.inverse (IP 1 (2 * n + 1) 2) * Bw (2 * n + 1) := fun n => by
    rw [Aw, Bw, ← euler_even (show 1 ≤ 2 * n + 1 by omega), ← mul_assoc,
      Ring.inverse_mul_cancel _ (uIP 1 (show 1 ≤ 2 * n + 1 by omega) (show 1 ≤ 2 by norm_num)), one_mul]
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + ((2 * q.1 + 1) * q.2 + (2 * q.2).choose 2)) * (QI 2 q.1 * QI 1 (2 * q.2)) with hg_def
  have hg : LF g := LF_pair (fun q => by nlinarith)
  have hL : LF fun n => X ^ (2 * n) * QI 1 (2 * n) * Aw (2 * n + 1) := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n) * Aw (2 * n + 1)) (e := fun n => 2 * n)
      (fun n => by show n ≤ 2 * n; omega)
  rw [mul_osum hL]
  have h1 : (osum fun n => IP 1 1 1 * (X ^ (2 * n) * QI 1 (2 * n) * Aw (2 * n + 1))) =
      IP 1 2 2 * osum fun n => osum fun p => g (n, p) := by
    rw [← osum_smul _ ((hg.prod_outer))]
    refine osum_ext fun n => ?_
    rw [hA n, show IP 1 1 1 * (X ^ (2 * n) * QI 1 (2 * n) * (Ring.inverse (IP 1 (2 * n + 1) 2) * Bw (2 * n + 1)))
      = X ^ (2 * n) * (IP 1 1 1 * QI 1 (2 * n) * Ring.inverse (IP 1 (2 * n + 1) 2)) * Bw (2 * n + 1) by ring,
      unit_even1, Bw, mul_osum (LF_Xpow_mul fun p => by nlinarith), mul_osum (hg.prod_left n)]
    refine osum_ext fun p => ?_
    simp only [hg_def]
    rw [pow_add]; ring
  rw [h1, osum_prod_swap hg, F0w, mul_osum hg.prod_outer']
  refine osum_ext fun p => ?_
  have hin : (osum fun n => g (n, p)) = X ^ (2 * (p * p)) * QI 1 (2 * p) * GI 1 (2 * p + 2) 2 := by
    rw [GI, mul_osum (LF_gI 1 (by omega) 2)]
    refine osum_ext fun n => ?_
    simp only [hg_def, gI]
    rw [show 2 * n + ((2 * n + 1) * p + (2 * p).choose 2) = 2 * (p * p) + (2 * p + 2) * n by
      have := choose_two_mul_add p; nlinarith, pow_add]
    push_cast; ring
  rw [hin, show IP 1 2 2 * (X ^ (2 * (p * p)) * QI 1 (2 * p) * GI 1 (2 * p + 2) 2)
    = X ^ (2 * (p * p)) * (IP 1 2 2 * QI 1 (2 * p) * GI 1 (2 * p + 2) 2) by ring, unit_even2]

/-! ### the odd pieces `T₂`, `T₃` -/

lemma E_mul_GI (n : ℕ) : IP 1 1 1 * GI 1 (n + 1) 1 = QF 1 n := by
  rw [← QF_div_E, ← mul_assoc, Ring.mul_inverse_cancel _ (uIP 1 le_rfl le_rfl), one_mul]

/-- **T₂**: `(q)_∞ Σ_n q^{2n+1}/(q)_{2n+1} · 1/(q^{n+1};q)_∞ = χ₀ − 1`. -/
lemma odd_piece2 :
    IP 1 1 1 * (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI 1 (n + 1) 1) = chiB - 1 := by
  have hL : LF fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI 1 (n + 1) 1 := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
      (e := fun n => 2 * n + 1) (fun n => by show n ≤ 2 * n + 1; omega)
  rw [mul_osum hL, chiB, add_sub_cancel_left]
  refine osum_ext fun n => ?_
  rw [inv_chiPoch', show IP 1 1 1 * (X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
    = X ^ (2 * n + 1) * QI 1 (2 * n + 1) * (IP 1 1 1 * GI 1 (n + 1) 1) by ring, E_mul_GI]
  ring

lemma unit_odd3 (n : ℕ) :
    QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 = IP 1 (2 * n + 3) 2 * QI 1 n := by
  have u1 := uFP 1 (show 1 ≤ 1 by rfl) 2 (n + 1)
  have u2 := uFP 1 (show 1 ≤ 2 by norm_num) 2 n
  have u3 := uIP (-1) (show 1 ≤ n + 1 by omega) (show 1 ≤ 1 by rfl)
  apply ((u1.mul u2).mul u3).mul_right_cancel
  have e1 := QF_mul_QI 1 (2 * n + 1) le_rfl
  rw [QF_two_succ] at e1
  have e2 : GI (-1) (n + 1) 1 * IP (-1) (n + 1) 1 = 1 := by
    rw [mul_comm]; exact euler_inv (-1) (by omega) le_rfl
  have s1 : IP 1 1 2 = FP 1 1 2 (n + 1) * IP 1 (2 * n + 3) 2 := by
    rw [IP_split 1 (a := 1) (b := 2) le_rfl (by norm_num) (n + 1)]; ring_nf
  have s2 : IP (-1) 1 1 = FP (-1) 1 1 n * IP (-1) (n + 1) 1 := by
    rw [IP_split (-1) (a := 1) (b := 1) le_rfl le_rfl n]; ring_nf
  have s3 : FP 1 2 2 n = QF 1 n * FP (-1) 1 1 n := by
    rw [QF, FP_sq]; norm_num
  have e4 := QF_mul_QI 1 n le_rfl
  calc QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 * (FP 1 1 2 (n + 1) * FP 1 2 2 n * IP (-1) (n + 1) 1)
      = (FP 1 1 2 (n + 1) * FP 1 2 2 n * QI 1 (2 * n + 1)) * (GI (-1) (n + 1) 1 * IP (-1) (n + 1) 1) := by ring
    _ = 1 := by rw [e1, e2, one_mul]
    _ = IP (-1) 1 1 * IP 1 1 2 := euler_E4.symm
    _ = IP 1 (2 * n + 3) 2 * QI 1 n * (FP 1 1 2 (n + 1) * FP 1 2 2 n * IP (-1) (n + 1) 1) := by
      rw [s2, s1, s3]
      linear_combination (FP (-1) 1 1 n * IP (-1) (n + 1) 1 * FP 1 1 2 (n + 1) * IP 1 (2 * n + 3) 2) * e4.symm

/-- **T₃**: `(q)_∞ Σ_n q^{2n+1}/(q)_{2n+1} · 1/(−q^{n+1};q)_∞ = 1 − φ₀(−q)`. -/
lemma odd_piece3 :
    IP 1 1 1 * (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1) = 1 - P0w := by
  set g : ℕ × ℕ → PowerSeries ℤ := fun q =>
    X ^ (2 * q.1 + 1 + ((2 * q.1 + 3) * q.2 + 2 * q.2.choose 2)) *
      ((((-1) ^ q.2 : ℤ) : PowerSeries ℤ) * QI 2 q.2 * QI 1 q.1) with hg_def
  have hg : LF g := LF_pair (fun q => by nlinarith)
  have h1 : (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1) =
      osum fun n => osum fun m => g (n, m) := by
    refine osum_ext fun n => ?_
    rw [mul_assoc, unit_odd3, euler_prod 1 (by omega) (by norm_num), HP,
      show X ^ (2 * n + 1) * (osum (hP 1 (2 * n + 3) 2) * QI 1 n)
        = X ^ (2 * n + 1) * QI 1 n * osum (hP 1 (2 * n + 3) 2) by ring,
      mul_osum (LF_hP 1 (by omega) 2)]
    refine osum_ext fun m => ?_
    simp only [hg_def, hP]
    rw [pow_add]; push_cast; ring
  have h2 : ∀ m, (osum fun n => g (n, m)) =
      (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ ((m + 1) * (m + 1)) * QI 2 m * GI 1 (2 * m + 2) 1 := fun m => by
    rw [GI, mul_osum (LF_gI 1 (by omega) 1)]
    refine osum_ext fun n => ?_
    simp only [hg_def, gI]
    rw [show 2 * n + 1 + ((2 * n + 3) * m + 2 * m.choose 2) = (m + 1) * (m + 1) + (2 * m + 2) * n by
      have := two_choose_two m; nlinarith, pow_add]
    push_cast; ring
  rw [h1, osum_prod_swap hg, mul_osum hg.prod_outer']
  have hP0 : P0w = 1 + osum fun m => -((((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ ((m + 1) * (m + 1)) * FP 1 1 2 (m + 1)) := by
    have hLP : LF fun n => (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * FP 1 1 2 n :=
      LF.of_nat fun n k hk => by
        rw [show (((-1) ^ n : ℤ) : PowerSeries ℤ) * X ^ (n * n) * FP 1 1 2 n
          = X ^ (n * n) * ((((-1) ^ n : ℤ) : PowerSeries ℤ) * FP 1 1 2 n) by ring,
          coeff_X_pow_mul', if_neg (by nlinarith)]
    rw [P0w, osum_succ hLP]
    simp only [pow_zero, Int.cast_one, mul_one, FP_zero, one_mul]
    congr 1
    refine osum_ext fun m => ?_
    push_cast; ring
  rw [hP0, osum_neg, sub_add_cancel_left, neg_neg]
  refine osum_ext fun m => ?_
  rw [h2 m, show IP 1 1 1 * ((((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ ((m + 1) * (m + 1)) * QI 2 m * GI 1 (2 * m + 2) 1)
    = (((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ ((m + 1) * (m + 1)) * QI 2 m * (IP 1 1 1 * GI 1 (2 * m + 1 + 1) 1) by ring,
    E_mul_GI, QF_two_succ]
  have e := QF_mul_QI 2 m (by norm_num)
  rw [QF] at e
  linear_combination ((((-1) ^ m : ℤ) : PowerSeries ℤ) * X ^ ((m + 1) * (m + 1)) * FP 1 1 2 (m + 1)) * e

/-- `1/(q^{n+1};q)_∞ + 1/(−q^{n+1};q)_∞ = 2A(2n+2)` (the even part of (E2)). -/
lemma GI_pm (n : ℕ) : GI 1 (n + 1) 1 + GI (-1) (n + 1) 1 = 2 * Aw (2 * n + 2) := by
  have hu : LF (fun k => X ^ ((n + 1) * k) * QI 1 k : ℕ → PowerSeries ℤ) :=
    LF_Xpow_mul (fun k => by nlinarith)
  rw [GI, GI, ← osum_add (LF_gI 1 (by omega) 1) (LF_gI (-1) (by omega) 1), Aw]
  have e : (osum fun j => X ^ ((2 * n + 2) * j) * QI 1 (2 * j)) =
      osum fun j => (fun k => X ^ ((n + 1) * k) * QI 1 k) (2 * j) :=
    osum_ext fun j => by simp only; ring_nf
  rw [e, ← osum_even_part hu]
  refine osum_ext fun k => ?_
  simp only [gI]; push_cast; ring

/-- **Ramanujan's (B₀) = R1, proved as Watson did**: `χ₀(q) = 2F₀(q) − φ₀(−q)`. -/
theorem chi0_R1_watson : chiA = 2 * F0w - P0w := by
  have uE : IsUnit (IP 1 1 1) := uIP 1 le_rfl le_rfl
  have hh : LF fun m => X ^ m * QI 1 m * Aw (m + 1) := by
    simpa [mul_assoc] using LF_Xpow_mul (g := fun m => QI 1 m * Aw (m + 1)) (e := fun m => m) (fun m => le_refl m)
  have hs := step1
  rw [osum_parity hh] at hs
  -- the odd half, doubled
  have hodd : 2 * (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * Aw (2 * n + 1 + 1)) =
      (osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI 1 (n + 1) 1) +
        osum fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 := by
    have l1 : LF fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI 1 (n + 1) 1 := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI 1 (n + 1) 1)
        (e := fun n => 2 * n + 1) (fun n => by show n ≤ 2 * n + 1; omega)
    have l2 : LF fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * GI (-1) (n + 1) 1 := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * GI (-1) (n + 1) 1)
        (e := fun n => 2 * n + 1) (fun n => by show n ≤ 2 * n + 1; omega)
    have l3 : LF fun n => X ^ (2 * n + 1) * QI 1 (2 * n + 1) * Aw (2 * n + 1 + 1) := by
      simpa [mul_assoc] using LF_Xpow_mul (g := fun n => QI 1 (2 * n + 1) * Aw (2 * n + 1 + 1))
        (e := fun n => 2 * n + 1) (fun n => by show n ≤ 2 * n + 1; omega)
    rw [← osum_add l1 l2, ← osum_smul _ l3]
    refine osum_ext fun n => ?_
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, ← mul_add, GI_pm]; ring
  have hchi : chiA = IP 1 1 1 * (Ring.inverse (IP 1 1 1) * chiA) := by
    rw [← mul_assoc, Ring.mul_inverse_cancel _ uE, one_mul]
  have key : 2 * chiA = 2 * F0w + (chiB - 1) + (1 - P0w) := by
    rw [hchi, hs, ← even_piece, ← odd_piece2, ← odd_piece3]
    linear_combination (IP 1 1 1) * hodd
  rw [← chiA_eq_chiB] at key
  linear_combination key

end Watson
