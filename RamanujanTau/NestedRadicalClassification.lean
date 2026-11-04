import RamanujanTau.NestedRadicalAffine

/-!
# Converse for affine radicands and linear limits

With nonnegative `A`, `B`, and step `h`, the finite radicals whose radicands
are `A+B*(x+n*h)` and multipliers are `x+n*h` converge to `x+d` for every
`x ≥ 0` if and only if `A=d²` and `B=d-h` (`d > 0`).
This is a converse about actual limits, not just a formal algebraic identity.
-/

namespace Ramanujan.NestedRadical
open Filter
open scoped Topology

noncomputable def linearTrunc (A B h : ℝ) : ℕ → ℝ → ℝ
  | 0, x => Real.sqrt (A+B*x)
  | N+1, x => Real.sqrt (A+B*x+x*linearTrunc A B h N (x+h))

theorem linearTrunc_affine (d h : ℝ) (N : ℕ) (x : ℝ) :
    linearTrunc (d^2) (d-h) h N x = affineTrunc d h N x := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih => simp only [linearTrunc,affineTrunc_succ,ih]

/-- Continuity forces every claimed linear limit to obey the layer identity. -/
theorem identity_of_linear_limit {A B h d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) (hd : 0 < d)
    (H : ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun N => linearTrunc A B h N x) atTop (𝓝 (x+d))) :
    ∀ x : ℝ, 0 ≤ x → (x+d)^2=A+B*x+x*(x+h+d) := by
  intro x hx
  have hs : Tendsto (fun N => linearTrunc A B h (N+1) x) atTop (𝓝 (x+d)) :=
    (H x hx).comp (tendsto_add_atTop_nat 1)
  have hr := ((H (x+h) (by positivity)).const_mul x).const_add (A+B*x)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have he : x+d=Real.sqrt (A+B*x+x*(x+h+d)) :=
    tendsto_nhds_unique hs (by simpa only [linearTrunc] using hroot)
  rw [he,Real.sq_sqrt (by positivity)]

/-- Exact classification of affine radicands whose limits are `x+d` for all starts. -/
theorem linear_limit_iff {A B h d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) (hd : 0 < d) :
    (∀ x : ℝ, 0 ≤ x →
      Tendsto (fun N => linearTrunc A B h N x) atTop (𝓝 (x+d))) ↔
      A=d^2 ∧ B=d-h := by
  constructor
  · intro H
    exact (affine_identity_iff A B d h).mp (identity_of_linear_limit hA hB hh hd H)
  · rintro ⟨rfl,rfl⟩ x hx
    simpa only [linearTrunc_affine] using
      tendsto_affineTrunc hd hh (by linarith) hx

/-- Existence of any positive-offset linear limit is equivalent to one coefficient equation. -/
theorem exists_linear_limit_iff {A B h : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) :
    (∃ d : ℝ, 0 < d ∧ ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun N => linearTrunc A B h N x) atTop (𝓝 (x+d))) ↔
      A=(B+h)^2 ∧ 0 < B+h := by
  constructor
  · rintro ⟨d,hd,H⟩
    obtain ⟨hAd,hBd⟩ := (linear_limit_iff hA hB hh hd).mp H
    have he : d=B+h := by linarith
    simpa only [he] using And.intro hAd hd
  · rintro ⟨hEq,hpos⟩
    refine ⟨B+h,hpos,(linear_limit_iff hA hB hh hpos).mpr ⟨hEq,?_⟩⟩
    ring

end Ramanujan.NestedRadical
