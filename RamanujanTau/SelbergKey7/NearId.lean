/-
# Seventh pass, R3 (near part): the exact identities

* `Fq_eq`: for an off-diagonal `(m,n)` with `m, n ≥ 1`,
  `Fq(t) = Z(t) · λ(m)λ(n) · G_u(m, n)`, with `|Z(t)| ≤ 1` (`norm_Zt_le`) and
  `G_u(r, s) = (rs)^{−1/2} e^{iv log s + iu(log s − log r)} W̃_{u,u+v}(4π² r s)` for real `r, s > 0`.
* `near_sum_eq`: the near part of `Σ_p Fq(p, t)` is
  `Z(t) Σ_{1≤|ℓ|≤K₀} Σ_{M₁<m≤M₂} lineTerm(P,Q,ℓ,m) · H_ℓ(m)`, `H_ℓ(r) = G_u(r, (Pr − ℓ)/Q)`.
Level 1.
-/
import RamanujanTau.SelbergKey7.Far

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex Finset RamanujanTau.SubconvexityCond RamanujanTau.SelbergKey RamanujanTau.SelbergKey4
  RamanujanTau.SelbergKey5
open scoped Real

/-- The exponent of `G_u`. -/
noncomputable def Ef (u v r s : ℝ) : ℂ :=
  ((-(1 / 2) * (Real.log r + Real.log s) : ℝ) : ℂ) +
    ((v * Real.log s + u * (Real.log s - Real.log r) : ℝ) : ℂ) * I

/-- `G_u(r, s)`. -/
noncomputable def Gf (u v r s : ℝ) : ℂ := cexp (Ef u v r s) * Wsh u (u + v) (4 * π ^ 2 * r * s)

/-- The `(m,n)`-independent factor. -/
noncomputable def Zt (a b c d : ℕ) (T x v t : ℝ) : ℂ :=
  ((phiT T t : ℝ) : ℂ) * Ulag v (t + x) *
    cexp (((v * (Real.log d - Real.log c) +
      (Real.log b + Real.log d - Real.log a - Real.log c) * (t + x)) : ℝ) * I)

lemma norm_Zt_le (a b c d : ℕ) (T x v t : ℝ) : ‖Zt a b c d T x v t‖ ≤ 1 := by
  unfold Zt
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_Ulag, Complex.norm_real,
    Real.norm_eq_abs, mul_one, mul_one]
  unfold phiT
  rw [abs_of_nonneg (Phi_nonneg _)]
  exact Phi_le_one _

/-- **The factorization of one off-diagonal term.** -/
theorem Fq_eq (a b c d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hdiag : ¬ isDiag a b c d (m, n))
    (T x v t : ℝ) :
    Fq T x v (a, b, c, d) (m, n) t = Zt a b c d T x v t * ((lam m * lam n : ℝ) : ℂ) *
      Gf (t + x) v m n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Fq
  simp only
  rw [if_neg hdiag, term_eq a b c d hm hn (t + x) v]
  unfold kap4 FW Wv Gf Zt lam
  rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0]
  have key : cexp (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) *
      cexp ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ)) *
      cexp ((omg a b c d m n * (t + x) : ℝ) * I) =
      cexp (((v * (Real.log d - Real.log c) +
        (Real.log b + Real.log d - Real.log a - Real.log c) * (t + x)) : ℝ) * I) *
      cexp ((Real.log m * (-(11 / 2)) : ℝ) : ℂ) * cexp ((Real.log n * (-(11 / 2)) : ℝ) : ℂ) *
      cexp (Ef (t + x) v m n) := by
    simp only [← Complex.exp_add]
    congr 1
    unfold Ef omg
    push_cast
    ring
  have e2 : ((((tau m : ℝ) * Real.exp (Real.log m * (-(11 / 2)))) *
      ((tau n : ℝ) * Real.exp (Real.log n * (-(11 / 2)))) : ℝ) : ℂ) =
      tauC m * tauC n * cexp ((Real.log m * (-(11 / 2)) : ℝ) : ℂ) *
        cexp ((Real.log n * (-(11 / 2)) : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_exp]
    simp only [tauC]
    ring
  rw [e2]
  calc ((phiT T t : ℝ) : ℂ) *
        (tauC m * tauC n * cexp (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) *
          cexp ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ)) *
          (Ulag v (t + x) * Wsh (t + x) (t + x + v) (4 * π ^ 2 * m * n) *
            cexp ((omg a b c d m n * (t + x) : ℝ) * I)))
      = ((phiT T t : ℝ) : ℂ) * Ulag v (t + x) * tauC m * tauC n *
          Wsh (t + x) (t + x + v) (4 * π ^ 2 * m * n) *
          (cexp (-(6 * ((Real.log m + Real.log n : ℝ) : ℂ))) *
            cexp ((v : ℂ) * I * ((Real.log d - Real.log c + Real.log n : ℝ) : ℂ)) *
            cexp ((omg a b c d m n * (t + x) : ℝ) * I)) := by ring
    _ = _ := by rw [key]; ring

/-- `ñ(r) = (Pr − ℓ)/Q`. -/
noncomputable def nt (P Q : ℕ) (ℓ : ℤ) (r : ℝ) : ℝ := ((P : ℝ) * r - ℓ) / Q

/-- `H_ℓ(r) = G_u(r, ñ(r))`. -/
noncomputable def Hl (P Q : ℕ) (ℓ : ℤ) (u v r : ℝ) : ℂ := Gf u v r (nt P Q ℓ r)

/-- The near line indices `1 ≤ |ℓ| ≤ K₀`. -/
noncomputable def Lset (T : ℝ) : Finset ℤ := (Icc (-(K0 T : ℤ)) (K0 T)).erase 0

lemma mem_Lset {T : ℝ} {ℓ : ℤ} : ℓ ∈ Lset T ↔ ℓ ≠ 0 ∧ ℓ.natAbs ≤ K0 T := by
  unfold Lset
  rw [mem_erase, mem_Icc]
  constructor
  · rintro ⟨h0, h1, h2⟩; exact ⟨h0, by omega⟩
  · rintro ⟨h0, h1⟩; exact ⟨h0, by omega, by omega⟩

/-- The `n`-sum on one line is `lineTerm`. -/
lemma sum_n_eq_lineTerm {P Q : ℕ} (hQ : 1 ≤ Q) {ℓ : ℤ} {m Nn : ℕ} (hN : P * m + ℓ.natAbs ≤ Nn) :
    (∑ n ∈ Icc 1 Nn, if ell P Q (m, n) = ℓ then lam m * lam n else 0) = lineTerm P Q ℓ m := by
  unfold lineTerm ell
  simp only
  symm
  refine sum_subset (Icc_subset_Icc le_rfl hN) fun n hn hn' => ?_
  rw [if_neg]
  intro he
  rw [mem_Icc] at hn hn'
  have h1 : P * m + ℓ.natAbs < n := by omega
  have h2 : ((P * m + ℓ.natAbs : ℕ) : ℤ) < n := by exact_mod_cast h1
  push_cast at h2
  have hk : -ℓ ≤ |ℓ| := neg_le_abs ℓ
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have : (n : ℤ) ≤ (Q : ℤ) * n := by nlinarith
  linarith

/-- **The near part of the pointwise sum, regrouped along lines.** -/
theorem near_sum_eq (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (T x v t : ℝ) :
    ∑ p ∈ nearSet (a * c) (b * d) T, Fq T x v (a, b, c, d) p t =
      Zt a b c d T x v t * ∑ ℓ ∈ Lset T, ∑ m ∈ Icc (M1 T + 1) (M2 T),
        ((lineTerm (a * c) (b * d) ℓ m : ℝ) : ℂ) * Hl (a * c) (b * d) ℓ (t + x) v m := by
  set P := a * c
  set Q := b * d
  have hQ : 1 ≤ Q := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  set F : ℕ × ℕ → ℂ := fun p => ((lam p.1 * lam p.2 : ℝ) : ℂ) * Gf (t + x) v p.1 p.2
  have h1 : ∀ p ∈ nearSet P Q T, Fq T x v (a, b, c, d) p t = Zt a b c d T x v t * F p := by
    intro p hp
    obtain ⟨m, n⟩ := p
    unfold nearSet at hp
    rw [mem_filter, mem_product, mem_Icc, mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, hn1, _⟩, hℓ, _⟩ := hp
    have hdiag : ¬ isDiag a b c d (m, n) := by
      intro h; apply hℓ; unfold isDiag at h; unfold ell; simp only at h ⊢
      have : (n : ℤ) * b * d = m * a * c := by exact_mod_cast h
      simp only [P, Q]; push_cast; linarith
    rw [Fq_eq a b c d (by omega) hn1 hdiag]
    simp only [F]; ring
  rw [sum_congr rfl h1, ← mul_sum]
  congr 1
  unfold nearSet
  rw [sum_filter, sum_product]
  -- indicator of `Lset` as a sum over `ℓ`
  have h2 : ∀ m n : ℕ, (if ell P Q (m, n) ≠ 0 ∧ (ell P Q (m, n)).natAbs ≤ K0 T then F (m, n) else 0) =
      ∑ ℓ ∈ Lset T, if ell P Q (m, n) = ℓ then F (m, n) else 0 := by
    intro m n
    rw [sum_ite_eq (Lset T) (ell P Q (m, n)) (fun _ => F (m, n))]
    simp only [mem_Lset]
  simp only [h2]
  rw [show (∑ m ∈ Icc (M1 T + 1) (M2 T), ∑ n ∈ Icc 1 (P * M2 T + K0 T), ∑ ℓ ∈ Lset T,
      if ell P Q (m, n) = ℓ then F (m, n) else 0) =
      ∑ m ∈ Icc (M1 T + 1) (M2 T), ∑ ℓ ∈ Lset T, ∑ n ∈ Icc 1 (P * M2 T + K0 T),
      if ell P Q (m, n) = ℓ then F (m, n) else 0 from sum_congr rfl fun m _ => sum_comm, sum_comm]
  refine sum_congr rfl fun ℓ hℓ => sum_congr rfl fun m hm => ?_
  rw [mem_Lset] at hℓ
  rw [mem_Icc] at hm
  have h3 : ∀ n : ℕ, (if ell P Q (m, n) = ℓ then F (m, n) else 0) =
      ((if ell P Q (m, n) = ℓ then lam m * lam n else 0 : ℝ) : ℂ) * Hl P Q ℓ (t + x) v m := by
    intro n
    split_ifs with h
    · simp only [F, Hl]
      congr 2
      unfold nt; unfold ell at h; simp only at h
      have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
      have : ((P : ℤ) : ℝ) * m - (Q : ℝ) * n = ℓ := by exact_mod_cast h
      field_simp
      push_cast at this
      linarith
    · simp
  simp only [h3]
  rw [← sum_mul, ← Complex.ofReal_sum, sum_n_eq_lineTerm hQ]
  have : P * m ≤ P * M2 T := Nat.mul_le_mul_left _ hm.2
  omega

end RamanujanTau.SelbergKey7
