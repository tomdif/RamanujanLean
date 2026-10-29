import RamanujanTau.TheoremA.EtaRescale
import RamanujanTau.TheoremA.LevelSixGenerators

/-! Exact finite word certificates; regenerate with
`scripts/frontier/pattern/gen_eta_generator_data.py`. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open scoped MatrixGroups

def dilation (j : Fin 4) : ℕ :=
  match j.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 6

theorem dilation_pos (j : Fin 4) : 0 < dilation j := by revert j; decide

def basisExponent (a : Fin 3) (j : Fin 4) : ℤ :=
  match a.val, j.val with
  | 0, 0 => 3 | 0, 2 => 3 | 1, 1 => 3 | 1, 3 => 3
  | 2, 0 => 2 | 2, 1 => -1 | 2, 2 => -2 | 2, 3 => 7 | _, _ => 0

def generatorWord (b : Bool) (i : Fin 12) (j : Fin 4) : List Step :=
  match b, i.val, j.val with
  | false, 0, 0 => [.t (0)]
  | false, 0, 1 => [.t (0)]
  | false, 0, 2 => [.t (0)]
  | false, 0, 3 => [.t (0)]
  | false, 1, 0 => [.s, .s, .t (0)]
  | false, 1, 1 => [.s, .s, .t (0)]
  | false, 1, 2 => [.s, .s, .t (0)]
  | false, 1, 3 => [.s, .s, .t (0)]
  | false, 2, 0 => [.t (-1), .s, .t (-6), .s, .s, .s, .t (0)]
  | false, 2, 1 => [.t (-2), .s, .t (-3), .s, .s, .s, .t (0)]
  | false, 2, 2 => [.t (-3), .s, .t (-2), .s, .s, .s, .t (0)]
  | false, 2, 3 => [.t (-5), .s, .t (1)]
  | false, 3, 0 => [.t (-1), .s, .t (-2), .s, .t (-4), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 3, 1 => [.t (-1), .s, .t (-6), .s, .s, .s, .t (-1)]
  | false, 3, 2 => [.t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-2)]
  | false, 3, 3 => [.t (-3), .s, .t (-2), .s, .s, .s, .t (-3)]
  | false, 4, 0 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 4, 1 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-1)]
  | false, 4, 2 => [.t (-1), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 4, 3 => [.t (-1), .s, .t (-1)]
  | false, 5, 0 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 5, 1 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-1)]
  | false, 5, 2 => [.t (-1), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 5, 3 => [.t (-1), .s, .t (-1)]
  | false, 6, 0 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (0)]
  | false, 6, 1 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (1)]
  | false, 6, 2 => [.t (-1), .s, .t (-2), .s, .s, .s, .t (2)]
  | false, 6, 3 => [.t (-1), .s, .t (5)]
  | false, 7, 0 => [.t (0), .s, .t (-6), .s, .s, .s, .t (0)]
  | false, 7, 1 => [.t (0), .s, .t (-3), .s, .s, .s, .t (0)]
  | false, 7, 2 => [.t (0), .s, .t (-2), .s, .s, .s, .t (0)]
  | false, 7, 3 => [.t (1), .s, .t (1)]
  | false, 8, 0 => [.t (0), .s, .t (-3), .s, .t (-3), .s, .t (-2), .s, .t (-2), .s, .t (-1)]
  | false, 8, 1 => [.t (0), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-3), .s, .t (-1)]
  | false, 8, 2 => [.t (1), .s, .t (-6), .s, .s, .s, .t (-1)]
  | false, 8, 3 => [.t (2), .s, .t (-3), .s, .s, .s, .t (-2)]
  | false, 9, 0 => [.t (0), .s, .t (-3), .s, .t (-2), .s, .t (-3), .s, .s, .s, .t (0)]
  | false, 9, 1 => [.t (0), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (0)]
  | false, 9, 2 => [.t (1), .s, .t (-4), .s, .s, .s, .t (1)]
  | false, 9, 3 => [.t (2), .s, .t (-2), .s, .s, .s, .t (2)]
  | false, 10, 0 => [.t (0), .s, .t (-6), .s, .s, .s, .t (0)]
  | false, 10, 1 => [.t (0), .s, .t (-3), .s, .s, .s, .t (0)]
  | false, 10, 2 => [.t (0), .s, .t (-2), .s, .s, .s, .t (0)]
  | false, 10, 3 => [.t (1), .s, .t (1)]
  | false, 11, 0 => [.t (0), .s, .t (-4), .s, .t (-3), .s, .t (-2), .s, .s, .s, .t (-1)]
  | false, 11, 1 => [.t (0), .s, .t (-2), .s, .t (-5), .s, .t (-1)]
  | false, 11, 2 => [.t (0), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-2)]
  | false, 11, 3 => [.t (1), .s, .t (-2), .s, .t (-2), .s, .t (-3)]
  | true, 0, 0 => [.t (1)]
  | true, 0, 1 => [.t (2)]
  | true, 0, 2 => [.t (3)]
  | true, 0, 3 => [.t (6)]
  | true, 1, 0 => [.t (0)]
  | true, 1, 1 => [.t (0)]
  | true, 1, 2 => [.t (0)]
  | true, 1, 3 => [.t (0)]
  | true, 2, 0 => [.t (0)]
  | true, 2, 1 => [.t (0)]
  | true, 2, 2 => [.t (0)]
  | true, 2, 3 => [.t (0)]
  | true, 3, 0 => [.t (0)]
  | true, 3, 1 => [.t (0)]
  | true, 3, 2 => [.t (0)]
  | true, 3, 3 => [.t (0)]
  | true, 4, 0 => [.t (0)]
  | true, 4, 1 => [.t (0)]
  | true, 4, 2 => [.t (0)]
  | true, 4, 3 => [.t (0)]
  | true, 5, 0 => [.t (0)]
  | true, 5, 1 => [.t (0)]
  | true, 5, 2 => [.t (0)]
  | true, 5, 3 => [.t (0)]
  | true, 6, 0 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-1)]
  | true, 6, 1 => [.t (-1), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-1)]
  | true, 6, 2 => [.t (-1), .s, .t (-2), .s, .t (-1)]
  | true, 6, 3 => [.t (-1), .s, .s, .s, .t (-1)]
  | true, 7, 0 => [.t (0)]
  | true, 7, 1 => [.t (0)]
  | true, 7, 2 => [.t (0)]
  | true, 7, 3 => [.t (0)]
  | true, 8, 0 => [.t (0)]
  | true, 8, 1 => [.t (0)]
  | true, 8, 2 => [.t (0)]
  | true, 8, 3 => [.t (0)]
  | true, 9, 0 => [.t (0), .s, .t (-3), .s, .t (-2), .s, .t (-3), .s, .t (-1)]
  | true, 9, 1 => [.t (0), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2)]
  | true, 9, 2 => [.t (1), .s, .t (-4), .s, .t (-2)]
  | true, 9, 3 => [.t (2), .s, .t (-2), .s, .t (-4)]
  | true, 10, 0 => [.t (0)]
  | true, 10, 1 => [.t (0)]
  | true, 10, 2 => [.t (0)]
  | true, 10, 3 => [.t (0)]
  | true, 11, 0 => [.t (0), .s, .t (-4), .s, .t (-3), .s, .t (-2), .s, .t (-1)]
  | true, 11, 1 => [.t (0), .s, .t (-2), .s, .t (-5), .s, .s, .s, .t (-1)]
  | true, 11, 2 => [.t (0), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2), .s, .t (-2)]
  | true, 11, 3 => [.t (1), .s, .t (-2), .s, .t (-2), .s, .s, .s, .t (-3)]
  | _, _, _ => []

theorem dilation_dvd_generator (b : Bool) (i : Fin 12) (j : Fin 4) :
    (dilation j : ℤ) ∣ LevelSix.generator (b, i) 1 0 := by
  revert b i j
  decide +kernel

theorem generatorWord_matrix (b : Bool) (i : Fin 12) (j : Fin 4) :
    wordMatrix (generatorWord b i j) = rescale (dilation j)
      (LevelSix.generator (b, i)) (dilation_dvd_generator b i j) := by
  revert b i j
  decide +kernel

theorem basisExponent_sum (a : Fin 3) : ∑ j : Fin 4, basisExponent a j = 6 := by
  revert a
  decide +kernel

theorem generator_phase_dvd (a : Fin 3) (b : Bool) (i : Fin 12) :
    (12 : ℤ) ∣ ∑ j : Fin 4, wordExponent (generatorWord b i j) * basisExponent a j := by
  revert a b i
  decide +kernel

end RamanujanTau.TheoremA.EtaSquared
