/-
# Infinite sums of entire series

A family `G : ℤ → (ℤ → L)` with a uniform bound `val(G i k) ≥ A|k| + |i| − C` (for every `A`) sums to an
entire series `sumS G` (`Ent.sumS`), and evaluation commutes with the sum (`ev_sumS`).
-/
import RamanujanTau.MTC.Conv

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-- uniform decay of a family of series. -/
def UDec (G : ℤ → ℤ → L) : Prop := ∀ A : ℤ, ∃ C : ℤ, ∀ i k, vge (G i k) (A * |k| + |i| - C)

section SumS
variable {G : ℤ → ℤ → L}

lemma udec_lb (hG : UDec G) : ∃ C : ℤ, ∀ i k n, (G i k).coeff n ≠ 0 → |i| - C ≤ n := by
  obtain ⟨C, hC⟩ := hG 0
  exact ⟨C, fun i k n hn => by have := hC i k n hn; linarith⟩

/-- the family `i ↦ G i k`. -/
noncomputable def colFam (hG : UDec G) (k : ℤ) : SummableFamily ℤ ℂ ℤ :=
  ofSupp (fun i => G i k) (-(Classical.choose (udec_lb hG)))
    (fun i n hn => by
      by_contra h
      have := Classical.choose_spec (udec_lb hG) i k n h
      have : 0 ≤ |i| := abs_nonneg i
      omega)
    (fun n => (Set.finite_Icc (-(n + Classical.choose (udec_lb hG)))
        (n + Classical.choose (udec_lb hG))).subset fun i hi => by
      have := Classical.choose_spec (udec_lb hG) i k n hi
      have h2 : |i| ≤ n + Classical.choose (udec_lb hG) := by linarith
      exact ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩)

/-- the sum of the family (zero if the bound fails). -/
noncomputable def sumS (G : ℤ → ℤ → L) : ℤ → L := by
  classical
  exact if h : UDec G then fun k => hs (colFam h k) else fun _ => 0

lemma sumS_eq (hG : UDec G) (k : ℤ) : sumS G k = hs (colFam hG k) := by
  unfold sumS; rw [dif_pos hG]

lemma Ent.sumS (hG : UDec G) : Ent (MTC.sumS G) := fun A => by
  obtain ⟨C, hC⟩ := hG A
  refine ⟨C, fun k => ?_⟩
  rw [sumS_eq hG]
  exact vge_hs _ fun i => vge_mono (hC i k) (by have := abs_nonneg i; linarith)

lemma UDec.ent (hG : UDec G) (i : ℤ) : Ent (G i) := fun A => by
  obtain ⟨C, hC⟩ := hG A
  exact ⟨C - |i|, fun k => vge_mono (hC i k) (by linarith)⟩

/-- the evaluation family over `ℤ × ℤ`. -/
lemma ev2_lb (hG : UDec G) (e : ℤ) (c : ℂ) :
    ∃ C : ℤ, ∀ i k n, (G i k * mono (e * k) (c ^ k)).coeff n ≠ 0 → |i| + |k| - C ≤ n := by
  obtain ⟨C, hC⟩ := hG (|e| + 1)
  refine ⟨C, fun i k n hn => ?_⟩
  have h := vge_mul (hC i k) (vge_single (e * k) (c ^ k)) n hn
  have : -(|e| * |k|) ≤ e * k := by rw [← abs_mul]; exact neg_abs_le _
  nlinarith

noncomputable def ev2Fam (hG : UDec G) (e : ℤ) (c : ℂ) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp (fun p => G p.1 p.2 * mono (e * p.2) (c ^ p.2)) (-(Classical.choose (ev2_lb hG e c)))
    (fun p n hn => by
      by_contra h
      have := Classical.choose_spec (ev2_lb hG e c) p.1 p.2 n h
      have := abs_nonneg p.1; have := abs_nonneg p.2
      omega)
    (fun n => by
      set C := Classical.choose (ev2_lb hG e c)
      refine ((Set.finite_Icc (-(n + C)) (n + C)).prod (Set.finite_Icc (-(n + C)) (n + C))).subset ?_
      rintro ⟨i, k⟩ hp
      have := Classical.choose_spec (ev2_lb hG e c) i k n hp
      have hi : |i| ≤ n + C := by have := abs_nonneg k; linarith
      have hk : |k| ≤ n + C := by have := abs_nonneg i; linarith
      exact ⟨⟨(abs_le.mp hi).1, (abs_le.mp hi).2⟩, ⟨(abs_le.mp hk).1, (abs_le.mp hk).2⟩⟩)

/-- the family of values `i ↦ ev (G i)`. -/
noncomputable def evColFam (hG : UDec G) (e : ℤ) (c : ℂ) : SummableFamily ℤ ℂ ℤ :=
  rowFam (ev2Fam hG e c)

lemma evColFam_apply (hG : UDec G) (e : ℤ) (c : ℂ) (i : ℤ) : evColFam hG e c i = ev (G i) e c := by
  rw [evColFam, rowFam_apply, ev_eq (hG.ent i)]
  refine hsum_congr _ _ fun k => ?_
  simp [ev2Fam, row_apply]

/-- **evaluation commutes with the sum**. -/
theorem ev_sumS (hG : UDec G) (e : ℤ) (c : ℂ) : ev (MTC.sumS G) e c = hs (evColFam hG e c) := by
  rw [evColFam, hs_rowFam, ev_eq (Ent.sumS hG)]
  -- sum the `(i, k)` family by columns `k`
  have hsw : hs (ev2Fam hG e c) = hs (SummableFamily.Equiv (Equiv.prodComm ℤ ℤ) (ev2Fam hG e c)) := by
    rw [hs, hs, SummableFamily.hsum_equiv]
  rw [hsw, ← hs_rowFam]
  refine hsum_congr _ _ fun k => ?_
  simp only [evFam_apply, rowFam_apply]
  rw [sumS_eq hG, hs, hs, mul_comm, ← SummableFamily.hsum_smul]
  congr 1
  ext i : 1
  simp [colFam, ev2Fam, row_apply, HahnSeries.of_symm_smul_of_eq_mul, mul_comm]

end SumS

/-! ## Finite Cauchy products -/

section CProd

/-- the Cauchy product of a list of series (the unit series `1` for the empty list). -/
noncomputable def cprodL : List (ℤ → L) → ℤ → L
  | [] => monoS 0 1
  | F :: l => MTC.conv F (cprodL l)

lemma Ent.cprodL : ∀ (l : List (ℤ → L)), (∀ F ∈ l, Ent F) → Ent (MTC.cprodL l)
  | [], _ => ent_monoS 0 1
  | F :: l, h => (h F (List.mem_cons_self ..)).conv (Ent.cprodL l fun G hG => h G (List.mem_cons_of_mem _ hG))

lemma ev_cprodL : ∀ (l : List (ℤ → L)), (∀ F ∈ l, Ent F) → ∀ (e : ℤ) {c : ℂ}, c ≠ 0 →
    ev (MTC.cprodL l) e c = (l.map fun F => ev F e c).prod
  | [], _, e, c, _ => by simp [cprodL, ev_monoS, mono]
  | F :: l, h, e, c, hc => by
      rw [cprodL, ev_conv (h F (List.mem_cons_self ..))
        (Ent.cprodL l fun G hG => h G (List.mem_cons_of_mem _ hG)) e hc,
        ev_cprodL l (fun G hG => h G (List.mem_cons_of_mem _ hG)) e hc]
      simp

end CProd

end MTC
