/-
# A packaged Phragmén–Lindelöf principle for vertical strips

`pl_strip`: if `f` is holomorphic on a half-plane `Re s > a'` containing the closed strip
`a ≤ Re s ≤ b` (width `< 2π`), grows at most like `K e^{L|Im s|}` inside, and is bounded by
`C` on both edges, then `‖f‖ ≤ C` on the whole closed strip.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinSharp

open Complex Real Set Filter Topology Asymptotics

theorem pl_strip {f : ℂ → ℂ} {a b a' C K L : ℝ} (ha' : a' < a) (hab : a < b)
    (hw : b - a < 2 * π) (hf : DifferentiableOn ℂ f {s : ℂ | a' < s.re})
    (hg : ∀ s : ℂ, a < s.re → s.re < b → 1 ≤ |s.im| → ‖f s‖ ≤ K * Real.exp (L * |s.im|))
    (hA : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C) (hB : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) : ‖f s‖ ≤ C := by
  have hclos : closure (re ⁻¹' Ioo a b) ⊆ {s : ℂ | a' < s.re} := by
    rw [closure_preimage_re, closure_Ioo hab.ne]
    intro z hz; simp only [mem_preimage, mem_Icc] at hz; simp; linarith [hz.1]
  refine PhragmenLindelof.vertical_strip (hf.mono hclos).diffContOnCl
    ⟨1 / 2, ?_, 2 * |L|, ?_⟩ hA hB h1 h2
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · refine IsBigO.of_bound |K| ?_
    have him : ∀ᶠ z : ℂ in comap (_root_.abs ∘ im) atTop, 1 ≤ |z.im| :=
      tendsto_comap.eventually (eventually_ge_atTop (1:ℝ))
    have hstrip : ∀ᶠ z : ℂ in 𝓟 (re ⁻¹' Ioo a b), z ∈ re ⁻¹' Ioo a b :=
      eventually_principal.2 fun z hz => hz
    filter_upwards [him.filter_mono inf_le_left, hstrip.filter_mono inf_le_right] with z hz1 hz2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (hg z hz2.1 hz2.2 hz1).trans ?_
    have ht : 0 ≤ |z.im| := abs_nonneg _
    have he := Real.add_one_le_exp (1 / 2 * |z.im|)
    have hL : L * |z.im| ≤ 2 * |L| * Real.exp (1 / 2 * |z.im|) := by
      have : L * |z.im| ≤ |L| * |z.im| := mul_le_mul_of_nonneg_right (le_abs_self L) ht
      nlinarith [abs_nonneg L]
    calc K * Real.exp (L * |z.im|) ≤ |K| * Real.exp (L * |z.im|) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
      _ ≤ |K| * Real.exp (2 * |L| * Real.exp (1 / 2 * |z.im|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hL) (abs_nonneg K)

end RamanujanTau.RankinSharp
