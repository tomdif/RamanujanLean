import RamanujanTau.HalfHecke.SInv
import RamanujanTau.ThetaLift.AbstractForm
import RamanujanTau.AtkinSporadic.HalfHecke

/-!
# `T(Q²)` preserves `η^{−1} S_k(SL₂(ℤ))`

For a level-one cusp form `G` of weight `k`, `H = η · T F` (`F = G/η`, `T` the coset sum of
`Expansion`, with the middle constant `cMd`) is

* holomorphic, with `q`-expansion `E · Σ B(N) qᴺ` (`hasSum_TF`), hence `1`-periodic and bounded at `∞`;
* `S`-invariant of weight `k` (`TF_S`).

So `H` is a level-one modular form of weight `k`. When `cMd·gQ = s·Q^{k−2}` (the sign of the Gauss
sum; `GaussSign`), `B = heckeHalf (a·P)`, which gives **`EtaHecke Q k 1`**.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex ModularForm Finset Filter
open UpperHalfPlane hiding I
open RamanujanTau.ThetaLift
open scoped Real MatrixGroups Manifold

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℤ} (G : CuspForm 𝒮ℒ k) {Q : ℕ} [hQ : Fact Q.Prime]

/-! ### Polynomial growth of `B` -/

lemma cA_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    ‖cA G 1 n‖ ≤ C * (n : ℝ) ^ (k.toNat) := by
  obtain ⟨C, hC0, hC⟩ := norm_cA_le G (j := 1) (by norm_num)
  refine ⟨C, hC0, fun n hn => (hC n hn).trans ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (k : ℝ) / 2 - ((1 : ℕ) : ℝ) / 4 ≤ (k.toNat : ℝ) := by
    have := Int.self_le_toNat k
    have h' : (k : ℝ) ≤ (k.toNat : ℝ) := by exact_mod_cast this
    have h0 : (0 : ℝ) ≤ (k.toNat : ℝ) := by positivity
    push_cast; linarith [show (k : ℝ) / 2 ≤ max (k : ℝ) 0 from by
      rcases le_total 0 (k : ℝ) with h | h
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (by linarith)]
  gcongr
  calc (n : ℝ) ^ ((k : ℝ) / 2 - ((1 : ℕ) : ℝ) / 4) ≤ (n : ℝ) ^ ((k.toNat : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 he
    _ = _ := Real.rpow_natCast _ _

lemma Bc_bound (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (cM : ℂ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ‖Bc G Q cM N‖ ≤ C * (N : ℝ) ^ (k.toNat) := by
  obtain ⟨C, hC0, hC⟩ := cA_bound G
  set K := k.toNat
  have hQ2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hQ.out.one_lt.le)
  -- every index `m ≤ Q² N` is bounded by `C (Q²N)^K`
  have hall : ∀ N m : ℕ, 1 ≤ N → m ≤ Q ^ 2 * N → ‖cA G 1 m‖ ≤ C * ((Q : ℝ) ^ 2) ^ K * (N : ℝ) ^ K := by
    intro N m hN hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [hc0, norm_zero]; positivity
    · refine (hC m hpos).trans ?_
      rw [mul_assoc, ← mul_pow]
      gcongr
      exact_mod_cast hm
  have hchi : ∀ x : ZMod Q, ‖chiQ Q x‖ ≤ 1 := by
    intro x
    rcases (chiQ_quad Q) x with h | h | h <;> simp [h]
  refine ⟨(1 + ‖cM * gQ Q‖ + ‖(Q : ℂ) ^ (2 * k - 3)‖) * (C * ((Q : ℝ) ^ 2) ^ K), fun N hN => ?_⟩
  set A := C * ((Q : ℝ) ^ 2) ^ K * (N : ℝ) ^ K
  have hA0 : 0 ≤ A := by positivity
  have h1 : ‖(if dQ Q ≤ Q ^ 2 * N then cA G 1 (Q ^ 2 * N - dQ Q) else 0)‖ ≤ A := by
    split_ifs
    · exact hall N _ hN (Nat.sub_le _ _)
    · simpa using hA0
  have h2 : ‖cM * gQ Q * chiQ Q ((24 * (N : ℤ) - 1 : ℤ) : ZMod Q) * cA G 1 N‖ ≤ ‖cM * gQ Q‖ * A := by
    rw [norm_mul, norm_mul]
    have := hall N N hN (Nat.le_mul_of_pos_left _ (by have := hQ.out.pos; positivity))
    calc ‖cM * gQ Q‖ * ‖chiQ Q _‖ * ‖cA G 1 N‖ ≤ ‖cM * gQ Q‖ * 1 * A := by gcongr; exact hchi _
      _ = _ := by ring
  have h3 : ‖(if Q ^ 2 ∣ N + dQ Q then (Q : ℂ) ^ (2 * k - 3) * cA G 1 ((N + dQ Q) / Q ^ 2) else 0)‖ ≤
      ‖(Q : ℂ) ^ (2 * k - 3)‖ * A := by
    split_ifs
    · rw [norm_mul]
      gcongr
      apply hall N _ hN
      have hs := dQ_spec hQ5
      have hQ2N : N ≤ Q ^ 2 * N := Nat.le_mul_of_pos_left _ (by have := hQ.out.pos; positivity)
      refine le_trans (Nat.div_le_of_le_mul ?_) hQ2N
      have : dQ Q ≤ 24 * dQ Q * N := by nlinarith
      rw [← hs]; nlinarith
    · simp; positivity
  calc ‖Bc G Q cM N‖ ≤ A + ‖cM * gQ Q‖ * A + ‖(Q : ℂ) ^ (2 * k - 3)‖ * A := by
        unfold Bc
        exact (norm_add₃_le).trans (by gcongr)
    _ = _ := by simp only [A]; ring

/-! ### The modular form `H = η · T F` -/

variable (Q) in
/-- `H = E · Σ B(N) qᴺ` as a function on `ℍ`. -/
def Hf (cM : ℂ) : ℍ → ℂ := eP * fS (Bc G Q cM)

lemma good_Hf (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (cM : ℂ) : Good (Hf G Q cM) := by
  obtain ⟨C, hC⟩ := Bc_bound G hQ5 hc0 cM
  exact good_eP.mul (good_fS _ hC)

lemma Hf_eq (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (cM : ℂ) (t : ℍ) :
    Hf G Q cM t = η t * TF G Q cM t := by
  have h := hasSum_TF (G := G) Q hQ5 hc0 cM t
  have hf : fS (Bc G Q cM) t = ee (t / 24) * TF G Q cM t := by
    unfold fS qS
    refine HasSum.tsum_eq (h.congr_fun fun N => ?_)
    congr 1
    simp only [Function.Periodic.qParam, ee]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have he : η (t : ℂ) = 𝕢 (24 : ℝ) t * eP t := rfl
  have hq : 𝕢 (24 : ℝ) (t : ℂ) = ee (t / 24) := by
    simp only [Function.Periodic.qParam, ee]; congr 1; push_cast; ring
  simp only [Hf, Pi.mul_apply]
  rw [hf, he, hq]; ring

lemma Hf_T (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (cM : ℂ) :
    Hf G Q cM ∣[k] ModularGroup.T = Hf G Q cM := by
  ext t
  have hper := (good_Hf G hQ5 hc0 cM).per (t : ℂ)
  rw [SL_slash_apply, modular_T_smul]
  have hden : denom (ModularGroup.T : SL(2, ℤ)) t = 1 := by simp [denom, ModularGroup.T]
  rw [hden, one_zpow, mul_one]
  simp only [Function.comp_apply, ofComplex_apply] at hper
  rw [← hper]
  congr 1
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa using t.im_pos)]
  simp [add_comm]

lemma Hf_S (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) :
    Hf G Q (cMd k Q) ∣[k] ModularGroup.S = Hf G Q (cMd k Q) := by
  ext t
  rw [SL_slash_apply, modular_S_smul]
  have hden : denom (ModularGroup.S : SL(2, ℤ)) t = t := by simp [denom, ModularGroup.S]
  rw [hden, Hf_eq G hQ5 hc0, Hf_eq G hQ5 hc0]
  have hz := t.im_pos
  have e : ((UpperHalfPlane.mk (-(t : ℂ))⁻¹ t.im_inv_neg_coe_pos : ℍ) : ℂ) = -1 / (t : ℂ) := by
    simp [neg_div, inv_neg]
  rw [e, TF_S G hQ5 hz]
  have ht0 : (t : ℂ) ≠ 0 := t.ne_zero
  rw [zpow_neg]
  field_simp

/-- **`H` is a level-one modular form of weight `k`.** -/
def Hform (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) : ModularForm 𝒮ℒ k where
  toFun := Hf G Q (cMd k Q)
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z (Hf_S G hQ5 hc0) (Hf_T G hQ5 hc0 _) A
  holo' := (good_Hf G hQ5 hc0 _).holo
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z (Hf_S G hQ5 hc0) (Hf_T G hQ5 hc0 _)]
    exact (good_Hf G hQ5 hc0 _).bdd

/-- **Its `q`-expansion is `E · Σ B(N) qᴺ`.** -/
theorem qExp_Hform (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) :
    qExpansion (1 : ℝ) (Hform G hQ5 hc0) =
      PowerSeries.map (Int.castRingHom ℂ) MockTheta5.JTP.qfacInf * PowerSeries.mk (Bc G Q (cMd k Q)) := by
  obtain ⟨C, hC⟩ := Bc_bound G hQ5 hc0 (cMd k Q)
  change qExpansion (1 : ℝ) (eP * fS (Bc G Q (cMd k Q))) = _
  rw [qExp_mul good_eP (good_fS _ hC), qExp_eP, qExp_fS _ hC]

end

end RamanujanTau.HalfHecke
