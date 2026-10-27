/-
# Evaluation of certified polynomials commutes with ring homomorphisms

Used to transport the certified theta identities from `ℂ((t))` back to `ℤ⟦q⟧` along an injective ring map.
-/
import RamanujanTau.SPoly

set_option autoImplicit false

namespace SPoly

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma evalL_map (x : List R) (e : List ℕ) : f (evalL x e) = evalL (x.map f) e := by
  induction x generalizing e with
  | nil => simp [evalL]
  | cons y ys ih =>
    cases e with
    | nil => simp [evalL]
    | cons a es => simp [evalL, ih]

lemma evalM_map (x : List R) (m : Mono) : f (evalM x m) = evalM (x.map f) m := evalL_map f x _

lemma evalP_map (x : List R) (p : Poly) : f (evalP x p) = evalP (x.map f) p := by
  induction p with
  | nil => simp
  | cons t p ih => rw [evalP_cons, evalP_cons, map_add, map_mul, map_intCast, evalM_map, ih]

lemma PE.eval_map (x : List R) : ∀ e : PE, f (e.eval x) = e.eval (x.map f)
  | .lit p => evalP_map f x p
  | .add a b => by simp [PE.eval, PE.eval_map x a, PE.eval_map x b]
  | .sub a b => by simp [PE.eval, PE.eval_map x a, PE.eval_map x b]
  | .mul a b => by simp [PE.eval, PE.eval_map x a, PE.eval_map x b]
  | .smul c a => by simp [PE.eval, PE.eval_map x a]
  | .pow a n => by simp [PE.eval, PE.eval_map x a]

/-- an identity at the image point pulls back along an injective ring map. -/
theorem PE.eval_eq_zero_of_map (hf : Function.Injective f) (x : List R) (e : PE) (h : e.eval (x.map f) = 0) :
    e.eval x = 0 :=
  hf (by rw [PE.eval_map, h, map_zero])

end SPoly
