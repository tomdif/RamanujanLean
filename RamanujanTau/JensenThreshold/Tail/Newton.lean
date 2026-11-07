/-
# The Newton forward-difference identity in degrees 6 and 7
-/
import RamanujanTau.JensenThreshold.Tail.Box2

set_option autoImplicit false

namespace JensenThreshold.Tail

open Finset

theorem newton6 : NewtonId 6 := by
  intro w Z
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Nat.choose]
  ring

theorem newton7 : NewtonId 7 := by
  intro w Z
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Nat.choose]
  ring

end JensenThreshold.Tail
