/-
# Opposite partners after deleting zero-amplitude vectors
-/
import RamanujanTau.MultiQuintuplePhasePartners
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

theorem supported_opposite_partner_of_finite_shell
    {I : Type*} [Fintype I] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (rho C : ℂ) (hC : C ≠ 0) (hrho : rho^p = -1)
    (hprimitive : IsPrimitiveRoot (rho^2) p) (P : I → Prop)
    (phase : I → ZMod (2*p)) (antipode : I ≃ I)
    (hP : ∀ x, P (antipode x) ↔ P x)
    (hanti : ∀ x, P x → phase (antipode x)=(p : ZMod (2*p))-phase x)
    (A : I → ℂ) (hsupported : ∀ x, P x → A x=C*rho^(phase x).val)
    (hunsupported : ∀ x, ¬P x → A x=0) (hzero : (∑ x, A x)=0) :
    ∀ x, P x → ∃ y, P y ∧ phase y=phase x+p := by
  classical
  let e : {x // P x} ≃ {x // P x} := antipode.subtypeEquiv (fun x => (hP x).symm)
  have he (x : {x // P x}) : phase (e x)=(p : ZMod (2*p))-phase x := hanti x x.property
  have hs : (∑' x : {x // P x}, C*rho^(phase x).val)=0 := by
    change (∑' x : ↑(setOf P), C*rho^(phase x.val).val)=0
    rw [tsum_subtype (setOf P) (fun x => C*rho^(phase x).val)]
    have hf : (setOf P).indicator (fun x => C*rho^(phase x).val)=A := by
      funext x
      by_cases hx : P x
      · simp [Set.indicator_apply,hx,hsupported x hx]
      · simp [Set.indicator_apply,hx,hunsupported x hx]
    rw [hf,tsum_fintype,hzero]
  rw [tsum_mul_left] at hs
  have hz : (∑ x : {x // P x}, rho^(phase x).val)=0 := by
    simpa only [tsum_fintype] using (mul_eq_zero.mp hs).resolve_left hC
  have hpartners := opposite_phase_partner_of_antipodal_sum_zero hp hp2 rho hrho hprimitive
    (fun x : {x // P x} => phase x) e he hz
  intro x hx
  obtain ⟨y,hy⟩ := hpartners ⟨x,hx⟩
  exact ⟨y,y.property,hy⟩

end Ramanujan.MultiQuintuple
