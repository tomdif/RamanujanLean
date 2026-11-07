/-
Ported from PrimeNumberTheoremAnd (Apache-2.0), file PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
(commit of 2026-08-30, toolchain v4.32) to this repo (v4.30). Changes: blueprint annotations
stripped; `convert!`/`using!` -> `convert`/`using`; sorried `prelim_decay_2/3`, `decay_alt` and the
AP section removed; Sobolev/Fourier/SmoothExistence/Wiener in namespace `RamanujanTau.WI`. See docs/WIENER_IKEHARA.md.
-/
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
