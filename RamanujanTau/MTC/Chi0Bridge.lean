/-
# From the `f_{12,9,3}` cones to `f_{2,3,2}` at the HM points

* `Cp_parity`: splitting `s = 2v + w`, `Cp k ex ey = Cq k ex (2ey+3) − Cq (k+ey) (ex+9) (2ey+9)`, where
  `Cq K a b = Σ_{r,v≥0} Q^{K + ar + bv + 12C(r,2) + 18rv + 12C(v,2)}` is the positive cone of `f_{2,3,2}(−Q^a, −Q^b, Q⁶)`;
* `f232_cones`: for `q = t^{36}` (`Q = t⁶`), `Q^K f_{2,3,2}(−Q^a, −Q^b, Q⁶) = Cq K a b − Cq (K+42−a−b) (42−a) (42−b)`,
  the value being `ev (fS H232.hq36 (6b) (−1)) (6a) (−1)` of the HM machinery.
-/
import RamanujanTau.MTC.Chi0D
import RamanujanTau.MTC.HM232Real

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

/-! ## Pulling a summable family back along an injection -/

section Pull
variable {α β : Type*}

noncomputable def pullF (s : SummableFamily ℤ ℂ β) (f : α → β) (hf : Function.Injective f) :
    SummableFamily ℤ ℂ α where
  toFun a := s (f a)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono fun n hn => by
    simp only [Set.mem_iUnion] at hn ⊢
    obtain ⟨a, ha⟩ := hn; exact ⟨f a, ha⟩
  finite_co_support' n := (s.finite_co_support n).preimage hf.injOn

@[simp] lemma pullF_apply (s : SummableFamily ℤ ℂ β) (f : α → β) (hf) (a : α) : pullF s f hf a = s (f a) := rfl

lemma hs_zeroF {ι : Type*} (s : SummableFamily ℤ ℂ ι) (h : ∀ i, s i = 0) : hs s = 0 := by
  rw [hs_eq_finset_sum ∅ fun i _ => h i]; simp

lemma hs_split' {κ₁ κ₂ : Type*} (s : SummableFamily ℤ ℂ β) (e : κ₁ ⊕ κ₂ ≃ β) :
    hs s = hs (pullF s (e ∘ Sum.inl) (e.injective.comp Sum.inl_injective)) +
      hs (pullF s (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)) :=
  hs_split s _ _ e (fun _ => rfl) (fun _ => rfl)

end Pull

/-! ## `f_{2,3,2}` cones -/

def qE (K a b : ℕ) (p : ℕ × ℕ) : ℤ :=
  6 * ((K : ℤ) + a * p.1 + b * p.2 + 12 * c2 p.1 + 18 * p.1 * p.2 + 12 * c2 p.2)

lemma qE_ge (K a b : ℕ) (p : ℕ × ℕ) : (p.1 : ℤ) + p.2 - 2 ≤ qE K a b p := by
  unfold qE
  have := c2_nat_ge p.1; have := c2_nat_ge p.2; have := c2_nat_nonneg p.1; have := c2_nat_nonneg p.2
  have : (0 : ℤ) ≤ (a : ℤ) * p.1 := by positivity
  have : (0 : ℤ) ≤ (b : ℤ) * p.2 := by positivity
  have : (0 : ℤ) ≤ 18 * (p.1 : ℤ) * p.2 := by positivity
  have : (0 : ℤ) ≤ K := by positivity
  omega

noncomputable def cqF (K a b : ℕ) : SummableFamily ℤ ℂ (ℕ × ℕ) :=
  monoFam (qE K a b) (fun _ => 1) (-2) (fun p => by have := qE_ge K a b p; omega)
    (fun n => box2_fin n _ (qE_ge K a b))

/-- the positive cone of `f_{2,3,2}(−Q^a, −Q^b, Q⁶)`, shifted by `Q^K`. -/
noncomputable def Cq (K a b : ℕ) : L := hs (cqF K a b)

/-- `ℕ × ℕ ⊕ ℕ × ℕ ≃ ℕ × ℕ`, `(r, v) ↦ (r, 2v)` and `(r, 2v+1)`. -/
def ePar : ℕ × ℕ ⊕ ℕ × ℕ ≃ ℕ × ℕ where
  toFun x := Sum.elim (fun p => (p.1, 2 * p.2)) (fun p => (p.1, 2 * p.2 + 1)) x
  invFun p := if p.2 % 2 = 0 then Sum.inl (p.1, p.2 / 2) else Sum.inr (p.1, p.2 / 2)
  left_inv x := by
    rcases x with ⟨r, v⟩ | ⟨r, v⟩
    · simp only [Sum.elim_inl]; rw [if_pos (by omega)]; congr; omega
    · simp only [Sum.elim_inr]; rw [if_neg (by omega)]; congr; omega
  right_inv p := by
    obtain ⟨r, s⟩ := p
    by_cases h : s % 2 = 0
    · simp only [h, if_true, Sum.elim_inl, Prod.mk.injEq, true_and]; omega
    · simp only [h, if_false, Sum.elim_inr, Prod.mk.injEq, true_and]; omega

theorem Cp_parity (k ex ey : ℕ) : Cp k ex ey = Cq k ex (2 * ey + 3) - Cq (k + ey) (ex + 9) (2 * ey + 9) := by
  rw [sub_eq_add_neg, Cp, Cq, Cq]
  have : hs (cpF k ex ey) = hs (cqF k ex (2 * ey + 3)) + hs ((-1 : L) • cqF (k + ey) (ex + 9) (2 * ey + 9)) :=
    hs_split _ _ _ ePar
      (fun p => by
        simp only [cpF, cqF, monoFam_apply, ePar, Equiv.coe_fn_mk, Sum.elim_inl]
        refine mono_ext ?_ (by rw [pow_mul]; norm_num)
        unfold cE qE
        have h1 := two_c2 ((2 * p.2 : ℕ) : ℤ); have h2 := two_c2 (p.2 : ℤ)
        apply cancel2
        push_cast at h1 ⊢
        linear_combination 18 * h1 - 72 * h2)
      (fun p => by
        simp only [cpF, cqF, monoFam_apply, ePar, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
          HahnSeries.of_symm_smul_of_eq_mul, neg_one_mul_mono]
        refine mono_ext ?_ (by rw [pow_succ, pow_mul]; norm_num)
        unfold cE qE
        have h1 := two_c2 ((2 * p.2 + 1 : ℕ) : ℤ); have h2 := two_c2 (p.2 : ℤ)
        apply cancel2
        push_cast at h1 ⊢
        linear_combination 18 * h1 - 72 * h2)
  rw [this, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_smul]
  ring

/-! ## `ev fS` at a real point as two cones -/

lemma coef_one (k s : ℤ) : (1 : ℂ) = (-1) ^ k * (-1) ^ k * (thC (-1) s) := by
  unfold thC; rw [neg_one_zpow_sq, neg_one_zpow_sq, one_mul]

section Bridge
variable (a b : ℕ) (ex ey : ℤ) (hex : ex = 6 * a) (hey : ey = 6 * b)
include hex hey

lemma row_pos (K : ℕ) (r : ℕ) :
    hs (row (cqF K a b) r) = mono (6 * K) 1 * evFam (H232.fS_ent H232.hq36 ey (-1)) ex (-1) (r : ℤ) := by
  subst hex hey
  rw [evFam_apply]
  unfold H232.fS H232.SK
  rw [if_pos (by positivity)]
  unfold thR
  rw [hs_split' _ eZ, hs_zeroF (pullF _ (eZ ∘ Sum.inr) _) (fun s => by
    simp only [pullF_apply, monoFam_apply, Function.comp_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inr]
    rw [if_neg (by omega)]; simp [mono]), add_zero]
  rw [show ∀ A B C D : L, A * (B * D * C) = (A * B * C) * D from fun _ _ _ _ => by ring]
  refine hs_eq_mul' _ fun s => ?_
  simp only [row_apply, cqF, monoFam_apply, pullF_apply, Function.comp_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inl]
  rw [if_pos (by positivity), mono_mul, mono_mul, mono_mul]
  refine mono_ext ?_ ?_
  · unfold qE thE; push_cast; ring
  · rw [one_mul]; exact coef_one _ _

lemma row_neg (K K' a' b' : ℕ) (hK : K' + a + b = K + 42) (ha : a' + a = 42) (hb : b' + b = 42) (r : ℕ) :
    hs (row (cqF K' a' b') r) = -(mono (6 * K) 1 * evFam (H232.fS_ent H232.hq36 ey (-1)) ex (-1) (-1 - (r : ℤ))) := by
  subst hex hey
  rw [evFam_apply]
  unfold H232.fS H232.SK
  rw [if_neg (by omega)]
  unfold thR
  rw [hs_split' _ eZ, hs_zeroF (pullF _ (eZ ∘ Sum.inl) _) (fun s => by
    simp only [pullF_apply, monoFam_apply, Function.comp_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inl]
    rw [if_neg (by omega)]; simp [mono]), zero_add]
  rw [show ∀ A B C D : L, -(A * (B * -D * C)) = (A * B * C) * D from fun _ _ _ _ => by ring]
  refine hs_eq_mul' _ fun s => ?_
  simp only [row_apply, cqF, monoFam_apply, pullF_apply, Function.comp_apply, eZ, Equiv.coe_fn_mk, Sum.elim_inr]
  rw [if_pos (by omega), mono_mul, mono_mul, mono_mul]
  refine mono_ext ?_ ?_
  · unfold qE thE
    rw [c2_neg_one_sub, c2_neg_one_sub]
    have hK' : (K' : ℤ) + a + b = K + 42 := by exact_mod_cast hK
    have ha' : (a' : ℤ) + a = 42 := by exact_mod_cast ha
    have hb' : (b' : ℤ) + b = 42 := by exact_mod_cast hb
    push_cast
    linear_combination 6 * hK' + (6 * (r : ℤ)) * ha' + (6 * (s : ℤ)) * hb'
  · rw [one_mul]; exact coef_one _ _

/-- **`f_{2,3,2}` at a real HM point as two cones**:
`Q^K f_{2,3,2}(−Q^a, −Q^b, Q⁶) = Cq K a b − Cq (K+42−a−b) (42−a) (42−b)` (`Q = t⁶`, `q = t^{36}`). -/
theorem f232_cones (K K' a' b' : ℕ) (hK : K' + a + b = K + 42) (ha : a' + a = 42) (hb : b' + b = 42) :
    mono (6 * K) 1 * ev (H232.fS H232.hq36 ey (-1)) ex (-1) = Cq K a b - Cq K' a' b' := by
  have hE := H232.fS_ent H232.hq36 ey (-1)
  rw [ev_eq hE, hs_split' _ eZ, mul_add, Cq, Cq]
  have h1 : hs (cqF K a b) = hs ((mono (6 * K) 1 : L) • pullF (evFam hE ex (-1)) (eZ ∘ Sum.inl)
      (eZ.injective.comp Sum.inl_injective)) :=
    hsum_fubini _ _ (row (cqF K a b)) (fun _ _ => rfl) fun r => by
      simp only [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, pullF_apply, Function.comp_apply,
        eZ, Equiv.coe_fn_mk, Sum.elim_inl]
      exact (row_pos a b ex ey hex hey K r).symm
  have h2 : hs (cqF K' a' b') = hs ((-mono (6 * K) 1 : L) • pullF (evFam hE ex (-1)) (eZ ∘ Sum.inr)
      (eZ.injective.comp Sum.inr_injective)) :=
    hsum_fubini _ _ (row (cqF K' a' b')) (fun _ _ => rfl) fun r => by
      simp only [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, pullF_apply, Function.comp_apply,
        eZ, Equiv.coe_fn_mk, Sum.elim_inr]
      rw [row_neg a b ex ey hex hey K K' a' b' hK ha hb r]; ring
  rw [h1, h2, hs_eq, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_smul, SummableFamily.hsum_smul]
  ring

end Bridge

lemma Cq_swap (K a b : ℕ) : Cq K a b = Cq K b a := by
  rw [Cq, Cq]
  symm
  refine (hsum_reindex (cqF K a b) (cqF K b a) (Equiv.prodComm ℕ ℕ) 1 fun p => ?_).trans (one_mul _)
  obtain ⟨r, s⟩ := p
  simp only [cqF, monoFam_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, one_mul_mono]
  exact mono_ext (by unfold qE; ring) rfl

/-- **the Hecke side of χ₀ at the seven HM points** (`q = t^{36}`, `Q = t⁶`): with `F(a,b) = f_{2,3,2}(−Q^a, −Q^b, Q⁶)`,
`(Q;Q)_∞ (χ₀(Q) − 2) = −F(7,7) + Q²F(16,13) + 2Q F(11,13) − Q⁵F(22,17) − Q⁶F(20,19) − Q⁴F(16,19) + Q¹²F(25,25)`. -/
theorem chi0_hecke_HM :
    ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) - 2 * ιN h6 MockTheta5.JTP.qfacInf =
      -ev (H232.fS H232.hq36 42 (-1)) 42 (-1) + mono 12 1 * ev (H232.fS H232.hq36 78 (-1)) 96 (-1) +
        2 * (mono 6 1 * ev (H232.fS H232.hq36 78 (-1)) 66 (-1)) - mono 30 1 * ev (H232.fS H232.hq36 102 (-1)) 132 (-1) -
        mono 36 1 * ev (H232.fS H232.hq36 114 (-1)) 120 (-1) - mono 24 1 * ev (H232.fS H232.hq36 114 (-1)) 96 (-1) +
        mono 72 1 * ev (H232.fS H232.hq36 150 (-1)) 150 (-1) := by
  have e1 := f232_cones 7 7 42 42 (by norm_num) (by norm_num) 0 28 35 35 (by norm_num) (by norm_num) (by norm_num)
  have e2 := f232_cones 16 13 96 78 (by norm_num) (by norm_num) 2 15 26 29 (by norm_num) (by norm_num) (by norm_num)
  have e3 := f232_cones 11 13 66 78 (by norm_num) (by norm_num) 1 19 31 29 (by norm_num) (by norm_num) (by norm_num)
  have e4 := f232_cones 22 17 132 102 (by norm_num) (by norm_num) 5 8 20 25 (by norm_num) (by norm_num) (by norm_num)
  have e5 := f232_cones 20 19 120 114 (by norm_num) (by norm_num) 6 9 22 23 (by norm_num) (by norm_num) (by norm_num)
  have e6 := f232_cones 16 19 96 114 (by norm_num) (by norm_num) 4 11 26 23 (by norm_num) (by norm_num) (by norm_num)
  have e7 := f232_cones 25 25 150 150 (by norm_num) (by norm_num) 12 4 17 17 (by norm_num) (by norm_num) (by norm_num)
  have p1 : Cp 0 7 2 = Cq 0 7 7 - Cq 2 16 13 := Cp_parity 0 7 2
  have p2 : Cp 15 26 13 = Cq 15 26 29 - Cq 28 35 35 := Cp_parity 15 26 13
  have p3 : Cp 1 13 4 = Cq 1 13 11 - Cq 5 22 17 := Cp_parity 1 13 4
  have p4 : Cp 8 20 11 = Cq 8 20 25 - Cq 19 29 31 := Cp_parity 8 20 11
  have p5 : Cp 1 11 5 = Cq 1 11 13 - Cq 6 20 19 := Cp_parity 1 11 5
  have p6 : Cp 9 22 10 = Cq 9 22 23 - Cq 19 31 29 := Cp_parity 9 22 10
  have p7 : Cp 4 16 8 = Cq 4 16 19 - Cq 12 25 25 := Cp_parity 4 16 8
  have p8 : Cp 4 17 7 = Cq 4 17 17 - Cq 11 26 23 := Cp_parity 4 17 7
  have s1 := Cq_swap 1 13 11
  have s2 := Cq_swap 19 29 31
  rw [qfac_chi0_garvan]
  norm_num at e1 e2 e3 e4 e5 e6 e7
  linear_combination -p1 - p2 + p3 + p4 + p5 + p6 - p7 - p8 + s1 - s2 + e1 - e2 - 2 * e3 + e4 + e5 + e6 - e7
