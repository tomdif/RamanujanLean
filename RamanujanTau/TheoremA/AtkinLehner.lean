import RamanujanTau.TheoremA.TraceCosets

/-!
# Atkin–Lehner signs and the eigenvalue of `U_p` on the new subspace

For `p ∥ Mp` the matrix `W = [px, y; Mpz, pw]` has determinant `p`. Its product
with `[1 j; 0 p]` is `p` times a coset representative, so Mathlib's actual
trace from Γ₀(Mp) to Γ₀(M) satisfies

  `Tr f = f + p^(2-k) U_p (f ∣ W)`.

A form killed by the trace with `f ∣ W = p^(k/2-1) w f` therefore has
`U_p f = -w p^(k/2-1) f`. This is the eigenvalue formula of Atkin–Lehner,
derived here rather than assumed.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.AtkinLehner
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane Complex
open scoped MatrixGroups ModularForm
open TraceCosets BadPrime

variable {p M : ℕ} [hp : Fact p.Prime]

/-- The Atkin–Lehner matrix over the integers. -/
def matW (D : CosetData p M) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ) * D.x, D.y; M * p * D.z, (p : ℤ) * D.w]

lemma matW_det (D : CosetData p M) : (matW D).det = p := by
  rw [matW, det_fin_two_of]
  linear_combination (p : ℤ) * D.det_eq

/-- The Atkin–Lehner matrix acting through Mathlib's slash action. -/
noncomputable def W (D : CosetData p M) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mk'' ((matW D).map (Int.castRingHom ℝ)) (by
    have he : ((matW D).map (Int.castRingHom ℝ)).det = (p : ℝ) := by
      have h := congrArg (Int.castRingHom ℝ) (matW_det D)
      rw [RingHom.map_det] at h
      simpa using h
    rw [he]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hp.out.ne_zero))

/-- The scalar `p`, which acts on the upper half-plane trivially. -/
noncomputable def scal (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mk'' !![(p : ℝ), 0; 0, (p : ℝ)] (by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simp [Matrix.det_fin_two_of, hp0])

lemma W_mul_rep (D : CosetData p M) (j : ZMod p) :
    W D * realRep p j = scal p * SpecialLinearGroup.mapGL ℝ (D.gam j) := by
  apply Units.ext
  ext a b
  have hj := realRep_val (p := p) j
  change ((W D).val * (realRep p j).val) a b =
    ((scal p).val * (SpecialLinearGroup.mapGL ℝ (D.gam j)).val) a b
  rw [hj]
  fin_cases a <;> fin_cases b <;>
    simp [W, scal, matW, representative, CosetData.gam, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

variable {k : ℤ}

lemma scal_slash (f : ℍ → ℂ) : f ∣[k] scal p = ((p : ℂ) ^ (k - 2)) • f := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hdet : (scal p).det.val = (p : ℝ) ^ 2 := by
    change (scal p).val.det = _
    simp [scal, Matrix.det_fin_two_of, sq]
  have hsm : ∀ z : ℍ, scal p • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by rw [hdet]; positivity)]
    simp [scal, num, denom]
    field_simp
  ext z
  rw [slash_apply, hsm]
  have hden : denom (scal p) z = (p : ℂ) := by simp [scal, denom]
  rw [hden]
  simp only [σ, hdet, if_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2),
    ContinuousAlgEquiv.refl_apply, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2),
    Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_assoc, ← zpow_add₀ hpC]
  have he : ((2 : ℕ) : ℤ) * (k - 1) + -k = k - 2 := by push_cast; ring
  rw [he, mul_comm]

/-- **The trace formula.** -/
theorem trace_formula [NeZero M] [NeZero (M * p)] (D : CosetData p M)
    (f : ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) :
    (ModularForm.trace (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) f : ℍ → ℂ) =
      (f : ℍ → ℂ) + ((p : ℂ) ^ (2 - k)) • slashU p k ((f : ℍ → ℂ) ∣[k] W D) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [D.trace_eq, slashU, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, W_mul_rep, SlashAction.slash_mul, scal_slash,
    ModularForm.smul_slash]
  have hσ : ∀ c : ℂ, σ (SpecialLinearGroup.mapGL ℝ (D.gam j)) c = c := by
    intro c
    simp [σ, Matrix.SpecialLinearGroup.det_mapGL]
  rw [hσ, smul_smul, ← zpow_add₀ hpC]
  simp

/-- The classical normalized Atkin–Lehner operator `p^(1-k/2) f ∣ W`, for even `k`. -/
noncomputable def alOp (D : CosetData p M) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ((p : ℂ) ^ (1 - k / 2)) • (f ∣[k] W D)

/-- `f` is new at `p` with Atkin–Lehner sign `w`. Since `f` is an eigenvector of `W`, the two
trace conditions defining the `p`-new subspace reduce to the vanishing of the trace of `f`. -/
structure IsNewSign [NeZero M] [NeZero (M * p)] (D : CosetData p M)
    (w : ℂ) (f : ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) : Prop where
  eigen : alOp D k f = w • (f : ℍ → ℂ)
  trace_zero : (ModularForm.trace (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) f : ℍ → ℂ) = 0

/-- **Atkin–Lehner's eigenvalue formula**, `U_p f = -w p^(k/2-1) f`, on the actual forms. -/
theorem IsNewSign.slashU_eq [NeZero M] [NeZero (M * p)] {D : CosetData p M} {w : ℂ}
    {f : ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k}
    (h : IsNewSign D w f) (hk : Even k) (hw : w * w = 1) :
    slashU p k f = (-w * (p : ℂ) ^ (k / 2 - 1)) • (f : ℍ → ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hW : (f : ℍ → ℂ) ∣[k] W D = ((p : ℂ) ^ (k / 2 - 1) * w) • (f : ℍ → ℂ) := by
    have he := h.eigen
    unfold alOp at he
    have := congrArg (fun g : ℍ → ℂ => ((p : ℂ) ^ (k / 2 - 1)) • g) he
    simp only [smul_smul, ← zpow_add₀ hpC] at this
    simpa using this
  have htr := trace_formula D f
  rw [h.trace_zero, hW] at htr
  have hS : slashU p k (((p : ℂ) ^ (k / 2 - 1) * w) • (f : ℍ → ℂ)) =
      ((p : ℂ) ^ (k / 2 - 1) * w) • slashU p k (f : ℍ → ℂ) := by
    unfold slashU
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ModularForm.smul_slash]
    congr 1
    simp only [σ]
    rw [if_pos (by rw [realRep_det]; exact_mod_cast hp.out.pos)]
    rfl
  rw [hS, smul_smul] at htr
  obtain ⟨n, rfl⟩ := hk
  have hdiv : (n + n) / 2 = n := by omega
  rw [hdiv] at htr ⊢
  have hc : (p : ℂ) ^ (2 - (n + n)) * ((p : ℂ) ^ (n - 1) * w) = (p : ℂ) ^ (1 - n) * w := by
    rw [← mul_assoc, ← zpow_add₀ hpC]
    congr 2
    ring
  rw [hc] at htr
  have hu : ((p : ℂ) ^ (1 - n) * w) • slashU p (n + n) (f : ℍ → ℂ) = -(f : ℍ → ℂ) :=
    (neg_eq_of_add_eq_zero_right htr.symm).symm
  have := congrArg (fun g : ℍ → ℂ => ((p : ℂ) ^ (n - 1) * w) • g) hu
  simp only [smul_smul, smul_neg] at this
  have hone : (p : ℂ) ^ (n - 1) * w * ((p : ℂ) ^ (1 - n) * w) = 1 := by
    calc _ = (p : ℂ) ^ ((n - 1) + (1 - n)) * (w * w) := by rw [zpow_add₀ hpC]; ring
      _ = 1 := by rw [hw]; simp
  rw [hone, one_smul] at this
  rw [this]
  funext z
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The same formula on the q-expansion. -/
theorem IsNewSign.U_qExpansion [NeZero M] [NeZero (M * p)] {D : CosetData p M} {w : ℂ}
    {f : ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k}
    (h : IsNewSign D w f) (hk : Even k) (hw : w * w = 1) :
    BoylanWebb.U p (qExpansion 1 f) =
      (-w * (p : ℂ) ^ (k / 2 - 1)) • qExpansion 1 f := by
  have hN : p ∣ M * p := dvd_mul_left _ _
  rw [← qExpansion_modularU hN f]
  have he : ((modularU hN f : ModularForm _ k) : ℍ → ℂ) =
      (-w * (p : ℂ) ^ (k / 2 - 1)) • (f : ℍ → ℂ) := by
    funext z
    exact congrFun (h.slashU_eq hk hw) z
  rw [he]
  exact ModularFormClass.qExpansion_smul one_pos one_period _ f

end RamanujanTau.TheoremA.AtkinLehner
