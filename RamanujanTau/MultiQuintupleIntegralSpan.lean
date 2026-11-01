/-
# Kernel-checkable integral spanning certificates

Determinants and Bezout's identity certify integral span, rather than merely
rational span. This is used for the short-generator certificates.
-/
import RamanujanTau.MultiQuintupleDualShortGeometry

namespace Ramanujan.MultiQuintuple

def ternaryPointDet (x y z : TernaryIntPoint) : ℤ :=
  ternaryDet x.1.1 x.1.2 x.2 y.1.1 y.1.2 y.2 z.1.1 z.1.2 z.2

/-- Cramer's identity in the integral ambient module; no inverse is used. -/
theorem ternaryPointDet_smul (x y z t : TernaryIntPoint) :
    ternaryPointDet x y z • t = ternaryPointDet t y z • x +
      ternaryPointDet x t z • y + ternaryPointDet x y t • z := by
  apply Prod.ext
  · apply Prod.ext <;>
      simp [ternaryPointDet, ternaryDet] <;> ring
  · simp [ternaryPointDet, ternaryDet]
    ring

theorem determinant_smul_mem (P : Submodule ℤ TernaryIntPoint)
    (x y z t : TernaryIntPoint) (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) :
    ternaryPointDet x y z • t ∈ P := by
  rw [ternaryPointDet_smul]
  exact P.add_mem (P.add_mem (P.smul_mem _ hx) (P.smul_mem _ hy)) (P.smul_mem _ hz)

theorem integer_gcd_smul_mem (P : Submodule ℤ TernaryIntPoint)
    (m n : ℤ) (t : TernaryIntPoint) (hm : m • t ∈ P) (hn : n • t ∈ P) :
    (Int.gcd m n : ℤ) • t ∈ P := by
  rw [Int.gcd_eq_gcd_ab, add_smul]
  simpa only [smul_smul, mul_comm] using
    P.add_mem (P.smul_mem (Int.gcdA m n) hm) (P.smul_mem (Int.gcdB m n) hn)

def integerListGcd : List ℤ → ℤ
  | [] => 0
  | a :: as => Int.gcd a (integerListGcd as)

theorem integerListGcd_smul_mem (P : Submodule ℤ TernaryIntPoint)
    (ds : List ℤ) (t : TernaryIntPoint) (hd : ∀ d ∈ ds, d • t ∈ P) :
    integerListGcd ds • t ∈ P := by
  induction ds with
  | nil => simp [integerListGcd]
  | cons a as ih =>
      exact integer_gcd_smul_mem P a (integerListGcd as) t
        (hd a (by simp)) (ih (fun d hd' => hd d (by simp [hd'])))

/-- If a list of triples from S has determinant gcd one, S generates the
entire integer module, with no saturation assumption. -/
theorem span_eq_top_of_determinant_gcd_one
    (S : Set TernaryIntPoint)
    (triples : List ((TernaryIntPoint × TernaryIntPoint) × TernaryIntPoint))
    (hmem : ∀ a ∈ triples, a.1.1 ∈ S ∧ a.1.2 ∈ S ∧ a.2 ∈ S)
    (hgcd : integerListGcd (triples.map (fun a => ternaryPointDet a.1.1 a.1.2 a.2)) = 1) :
    Submodule.span ℤ S = ⊤ := by
  apply top_unique
  intro t _
  have hh := integerListGcd_smul_mem (Submodule.span ℤ S)
    (triples.map (fun a => ternaryPointDet a.1.1 a.1.2 a.2)) t (by
      intro d hd
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
      obtain ⟨h1,h2,h3⟩ := hmem a ha
      exact determinant_smul_mem _ _ _ _ _
        (Submodule.subset_span h1) (Submodule.subset_span h2) (Submodule.subset_span h3))
  simpa [hgcd] using hh

/-- Pairs of distinct list positions, in their original order. -/
def generatorPairs : List TernaryIntPoint → List (TernaryIntPoint × TernaryIntPoint)
  | [] => []
  | x :: xs => xs.map (fun y => (x,y)) ++ generatorPairs xs

theorem generatorPairs_mem (vs : List TernaryIntPoint) :
    ∀ a ∈ generatorPairs vs, a.1 ∈ vs ∧ a.2 ∈ vs := by
  induction vs with
  | nil => simp [generatorPairs]
  | cons x xs ih =>
      intro a ha
      simp only [generatorPairs, List.mem_append, List.mem_map] at ha
      rcases ha with ⟨y,hy,rfl⟩ | ha
      · simp [hy]
      · obtain ⟨h1,h2⟩ := ih a ha
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Minors from increasing list positions suffice. This avoids computing
the zero minors with repeated rows and all six permutations of each minor. -/
def generatorTriples : List TernaryIntPoint →
    List ((TernaryIntPoint × TernaryIntPoint) × TernaryIntPoint)
  | [] => []
  | x :: xs => (generatorPairs xs).map (fun a => ((x,a.1),a.2)) ++ generatorTriples xs

theorem generatorTriples_mem (vs : List TernaryIntPoint) :
    ∀ a ∈ generatorTriples vs, a.1.1 ∈ vs ∧ a.1.2 ∈ vs ∧ a.2 ∈ vs := by
  induction vs with
  | nil => simp [generatorTriples]
  | cons x xs ih =>
      intro a ha
      simp only [generatorTriples, List.mem_append, List.mem_map] at ha
      rcases ha with ⟨b,hb,rfl⟩ | ha
      · obtain ⟨h1,h2⟩ := generatorPairs_mem xs b hb
        exact ⟨by simp, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · obtain ⟨h1,h2,h3⟩ := ih a ha
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2,
          List.mem_cons_of_mem _ h3⟩

def generatorDetGcd (vs : List TernaryIntPoint) : ℤ :=
  integerListGcd ((generatorTriples vs).map (fun a => ternaryPointDet a.1.1 a.1.2 a.2))

theorem span_list_eq_top_of_generatorDetGcd
    (vs : List TernaryIntPoint) (hgcd : generatorDetGcd vs = 1) :
    Submodule.span ℤ {x | x ∈ vs} = ⊤ := by
  apply span_eq_top_of_determinant_gcd_one _ (generatorTriples vs) _ hgcd
  exact generatorTriples_mem vs

end Ramanujan.MultiQuintuple
