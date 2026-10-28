import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluating absolutely convergent power series at a point is a ring homomorphism
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open PowerSeries

variable (q : ℂ)

lemma coeff_mul_pow (f g : PowerSeries ℂ) (N : ℕ) :
    coeff N (f * g) * q ^ N =
      ∑ kl ∈ Finset.antidiagonal N, (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2) := by
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [← Finset.mem_antidiagonal.mp hkl, pow_add]; ring

/-- absolute convergence at `q`. -/
def AC (f : PowerSeries ℂ) : Prop := Summable fun N => ‖coeff N f * q ^ N‖

lemma AC_mul {f g : PowerSeries ℂ} (hf : AC q f) (hg : AC q g) : AC q (f * g) := by
  unfold AC at *
  simp_rw [coeff_mul_pow]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun N => coeff N f * q ^ N)
    (g := fun N => coeff N g * q ^ N) hf hg

lemma AC_C (a : ℂ) : AC q (C a) := by
  unfold AC
  apply summable_of_ne_finset_zero (s := {0})
  intro N hN
  simp only [Finset.mem_singleton] at hN
  simp [coeff_C, hN]

lemma AC_add {f g : PowerSeries ℂ} (hf : AC q f) (hg : AC q g) : AC q (f + g) := by
  unfold AC at *
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_) (hf.add hg)
  rw [map_add, add_mul]; exact norm_add_le _ _

lemma AC_neg {f : PowerSeries ℂ} (hf : AC q f) : AC q (-f) := by
  unfold AC at *
  simpa using hf

/-- power series absolutely convergent at `q`. -/
def acRing : Subring (PowerSeries ℂ) where
  carrier := {f | AC q f}
  mul_mem' := AC_mul q
  one_mem' := by simpa using AC_C q 1
  add_mem' := AC_add q
  zero_mem' := by simpa using AC_C q 0
  neg_mem' := AC_neg q

lemma mem_acRing {f : PowerSeries ℂ} : f ∈ acRing q ↔ AC q f := Iff.rfl

/-- evaluation at `q`. -/
def val (f : PowerSeries ℂ) : ℂ := ∑' N, coeff N f * q ^ N

lemma val_C (a : ℂ) : val q (C a) = a := by
  rw [val, tsum_eq_single 0]
  · simp
  · intro N hN; simp [coeff_C, hN]

/-- evaluation at `q` as a ring homomorphism on `acRing q`. -/
def valHom : acRing q →+* ℂ where
  toFun f := val q f
  map_one' := by simpa using val_C q 1
  map_mul' f g := by
    simp only [val, Subring.coe_mul]
    simp_rw [coeff_mul_pow]
    exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun N => coeff N f.1 * q ^ N) (g := fun N => coeff N g.1 * q ^ N) f.2 g.2).symm
  map_zero' := by simp [val]
  map_add' f g := by
    simp only [val, Subring.coe_add, map_add, add_mul]
    exact (f.2.of_norm).tsum_add g.2.of_norm

lemma valHom_apply (f : acRing q) : valHom q f = val q f := rfl

end TateFormal
