#!/usr/bin/env python3
"""Generate the checked numeric minor; does not prove its arithmetic identification."""
from pathlib import Path
import json
r=Path(__file__).resolve().parents[1];p=607;q=p*p
rec=json.loads((r/'docs/verification/rank607-uniform-n2.json').read_text());M=rec['witness_matrix'];n=len(M)
U=[[x%q for x in row] for row in M];E=[[int(i==j) for j in range(n)] for i in range(n)]
for j in range(n-1):
 k=next(k for k in range(j,n) if U[k][j]%p)
 U[j],U[k]=U[k],U[j];E[j],E[k]=E[k],E[j]
 a=pow(U[j][j],-1,q);U[j]=[x*a%q for x in U[j]];E[j]=[x*a%q for x in E[j]]
 for i in range(j+1,n):
  a=U[i][j];U[i]=[(x-a*y)%q for x,y in zip(U[i],U[j])];E[i]=[(x-a*y)%q for x,y in zip(E[i],E[j])]
assert all(sum(E[i][k]*M[k][j] for k in range(n))%q==U[i][j] for i in range(n) for j in range(n))
assert U[-1][-1]!=0
print('last triangular entry',U[-1][-1])
text='''import RamanujanTau.FiniteArithmetic.DeterminantRank
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Kernel-checked arithmetic for the saved prime-607 coefficient minor

This checks the numerical matrix itself. Identifying its entries with the
actual infinite partition iterates is a separate, explicit hypothesis below.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace RamanujanTau.FiniteArithmetic
namespace Rank607Witness
open Matrix

'''
for name,A in [('matrix',M),('elimination',E),('upper',U)]:
 text+='def '+name+' : Matrix (Fin 25) (Fin 25) (ZMod (607^2)) :=\n  !['+',\n    '.join('!['+', '.join(map(str,row))+']' for row in A)+']\n\n'
text+='''theorem elimination_checked : elimination * matrix = upper := by decide +kernel

theorem upper_triangular : upper.BlockTriangular id := by
  unfold Matrix.BlockTriangular
  decide +kernel

theorem diagonal_nonzero : (∏ i : Fin 25, upper i i) ≠ 0 := by decide +kernel

/-- A kernel proof that the saved 25-by-25 matrix has a nonzero determinant
modulo 607². This statement is about the saved matrix, not yet its arithmetic identification. -/
theorem determinant_nonzero : matrix.det ≠ 0 := by
  have hu : upper.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular upper_triangular]
    exact diagonal_nonzero
  intro h
  apply hu
  rw [← elimination_checked, Matrix.det_mul, h, mul_zero]

/-- Exact entry identification is the remaining input to the actual partition theorem. -/
theorem actual_rank_of_entries
    (hentries : ∀ i j, rank607Matrix i j = matrix i j) (m : ℕ) (hm : 2 ≤ m) :
    BLBound.rEll 607 m = 25 := by
  apply rank607_eq_of_det _ m hm
  have he : rank607Matrix = matrix := funext fun i => funext fun j => hentries i j
  rw [he]
  exact determinant_nonzero

end Rank607Witness
end RamanujanTau.FiniteArithmetic
'''
(r/'RamanujanTau/FiniteArithmetic/Rank607Witness.lean').write_text(text)
