import RamanujanTau.HardyRamanujan.Main

/-!
# Growth of the partition function along arithmetic progressions

From Hardy–Ramanujan (`HardyRamanujan.hardy_ramanujan_isEquivalent`):
for naturals `1 ≤ β < α`, `p(αn)/p(βn) → ∞`. Also `p` is monotone and positive.
-/

set_option autoImplicit false

namespace RamanujanTau.BWSharpAll
open Filter Asymptotics
open scoped Real Topology

/-- `p(n) ≤ p(n+1)`: add a part equal to `1`. -/
theorem card_partition_le_succ (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ Fintype.card (Nat.Partition (n + 1)) := by
  let f : Nat.Partition n → Nat.Partition (n + 1) := fun q =>
    { parts := 1 ::ₘ q.parts
      parts_pos := by
        intro i hi
        rcases Multiset.mem_cons.mp hi with rfl | h
        · exact Nat.one_pos
        · exact q.parts_pos h
      parts_sum := by rw [Multiset.sum_cons, q.parts_sum]; ring }
  apply Fintype.card_le_of_injective f
  intro a b h
  have : a.parts = b.parts := by
    have := congrArg Nat.Partition.parts h
    exact (Multiset.cons_inj_right 1).mp this
  exact Nat.Partition.ext this

theorem card_partition_mono : Monotone fun n => Fintype.card (Nat.Partition n) :=
  monotone_nat_of_le_succ card_partition_le_succ

theorem card_partition_pos (n : ℕ) : 0 < Fintype.card (Nat.Partition n) :=
  Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

/-- **`p(αn)/p(βn) → ∞` for `1 ≤ β < α`.** -/
theorem ratio_tendsto_atTop {α β : ℕ} (hβ : 1 ≤ β) (hαβ : β < α) :
    Tendsto (fun n : ℕ => (Fintype.card (Nat.Partition (α * n)) : ℝ) /
      Fintype.card (Nat.Partition (β * n))) atTop atTop := by
  set f : ℕ → ℝ := fun n => Real.exp (π * √(2 * n / 3)) / (4 * √3 * n)
  have hA : Tendsto (fun n : ℕ => α * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hB : Tendsto (fun n : ℕ => β * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have e1 := HardyRamanujan.hardy_ramanujan_isEquivalent.comp_tendsto hA
  have e2 := HardyRamanujan.hardy_ramanujan_isEquivalent.comp_tendsto hB
  have e := e1.div e2
  refine e.symm.tendsto_atTop ?_
  have hα0 : (0 : ℝ) < α := by exact_mod_cast (show 0 < α by omega)
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast (show 0 < β by omega)
  set c : ℝ := π * (√(2 * α / 3) - √(2 * β / 3))
  have hc : 0 < c := by
    apply mul_pos Real.pi_pos
    rw [sub_pos]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : (β : ℝ) < α := by exact_mod_cast hαβ
    linarith
  have hg : Tendsto (fun n : ℕ => (β / α : ℝ) * Real.exp (c * √(n : ℝ))) atTop atTop := by
    apply Tendsto.const_mul_atTop (by positivity)
    apply Real.tendsto_exp_atTop.comp
    apply Tendsto.const_mul_atTop hc
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine hg.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, Pi.div_apply]
  push_cast
  have hsA : √(2 * (α * n) / 3) = √(2 * α / 3) * √n := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have hsB : √(2 * (β * n) / 3) = √(2 * β / 3) * √n := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  rw [hsA, hsB]
  have h3 : (0 : ℝ) < √3 := by positivity
  have hexp : Real.exp (c * √n) = Real.exp (π * (√(2 * α / 3) * √n)) /
      Real.exp (π * (√(2 * β / 3) * √n)) := by
    rw [← Real.exp_sub]; congr 1; simp only [c]; ring
  rw [hexp]
  field_simp
