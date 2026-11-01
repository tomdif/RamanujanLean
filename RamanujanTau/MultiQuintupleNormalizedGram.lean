/-
# The actual normalized projective lattice as an integral Gram form
-/
import RamanujanTau.MultiQuintupleLatticeNormalization
import RamanujanTau.MultiQuintupleIntegralGram

namespace Ramanujan.MultiQuintuple

def normalizedGram (p j k : ℕ) : IntegralTernaryGram :=
  ⟨(1+(j : ℤ)^2+(k : ℤ)^2)/p,p,p,j,k,0⟩

theorem normalizedGram_relation (p j k : ℕ)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) :
    (p : ℤ)*(normalizedGram p j k).a = 1+(j : ℤ)^2+(k : ℤ)^2 :=
  Int.mul_ediv_cancel' hi

theorem normalizedGram_norm (p j k : ℕ)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) (x : TernaryIntPoint) :
    (p : ℤ)*(normalizedGram p j k).norm x = ternaryIntNorm (normalizedDualMap p j k x) := by
  have hh := normalizedGram_relation p j k hi
  change (p : ℤ)*((normalizedGram p j k).a*x.1.1*x.1.1+
    (p : ℤ)*x.1.2*x.1.2+(p : ℤ)*x.2*x.2+
    (j : ℤ)*(x.1.1*x.1.2+x.1.2*x.1.1)+(k : ℤ)*(x.1.1*x.2+x.2*x.1.1)+
    0*(x.1.2*x.2+x.2*x.1.2)) =
      x.1.1^2+((j : ℤ)*x.1.1+(p : ℤ)*x.1.2)^2+((k : ℤ)*x.1.1+(p : ℤ)*x.2)^2
  linear_combination x.1.1^2*hh

theorem normalizedDualMap_injective {p : ℕ} (hp : p ≠ 0) (j k : ℕ) :
    Function.Injective (normalizedDualMap p j k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have h1 := congrArg (fun y : TernaryIntPoint => y.1.1) hx
  have h2 := congrArg (fun y : TernaryIntPoint => y.1.2) hx
  have h3 := congrArg (fun y : TernaryIntPoint => y.2) hx
  change x.1.1=0 at h1
  change (j : ℤ)*x.1.1+(p : ℤ)*x.1.2=0 at h2
  change (k : ℤ)*x.1.1+(p : ℤ)*x.2=0 at h3
  rw [h1,mul_zero,zero_add] at h2 h3
  exact Prod.ext (Prod.ext h1 ((mul_eq_zero.mp h2).resolve_left hpZ))
    ((mul_eq_zero.mp h3).resolve_left hpZ)

theorem ternaryIntNorm_pos {x : TernaryIntPoint} (hx : x ≠ 0) : 0 < ternaryIntNorm x := by
  have h1 := sq_nonneg x.1.1
  have h2 := sq_nonneg x.1.2
  have h3 := sq_nonneg x.2
  by_contra hn
  have hz : x.1.1=0 ∧ x.1.2=0 ∧ x.2=0 := by
    dsimp [ternaryIntNorm,ternaryNorm] at hn
    constructor
    · nlinarith
    constructor <;> nlinarith
  exact hx (Prod.ext (Prod.ext hz.1 hz.2.1) hz.2.2)

theorem normalizedGram_positive {p : ℕ} (hp : 0 < p) (j k : ℕ)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) : (normalizedGram p j k).Positive := by
  intro x hx
  have hx' : normalizedDualMap p j k x ≠ 0 := by
    intro hz
    exact hx (normalizedDualMap_injective hp.ne' j k (by simpa using hz))
  have hh := ternaryIntNorm_pos hx'
  rw [← normalizedGram_norm p j k hi] at hh
  exact (mul_pos_iff_of_pos_left (by exact_mod_cast hp : (0 : ℤ) < p)).mp hh

theorem normalizedGram_det (p j k : ℕ)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) : (normalizedGram p j k).det = p := by
  have hh := normalizedGram_relation p j k hi
  change (normalizedGram p j k).a*(p : ℤ)*p+2*(j : ℤ)*k*0-
    (normalizedGram p j k).a*0^2-(p : ℤ)*(k : ℤ)^2-(p : ℤ)*(j : ℤ)^2=(p : ℤ)
  linear_combination (p : ℤ)*hh

theorem congruence_norm_ge_three {p i j k : ℕ}
    (hi : 0 < i) (hij : i < j) (hjk : j < k) (hkp : 2*k < p)
    (x : TernaryIntPoint) (hx : x ≠ 0)
    (hmem : x ∈ congruenceLattice p (((i : ℤ),(j : ℤ)),(k : ℤ))) :
    3 ≤ ternaryIntNorm x := by
  by_contra hn
  rcases x with ⟨⟨a,b⟩,c⟩
  change (p : ℤ) ∣ (i : ℤ)*a+(j : ℤ)*b+(k : ℤ)*c at hmem
  change ¬3 ≤ a^2+b^2+c^2 at hn
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b,sq_nonneg c]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a,sq_nonneg c]
  have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [sq_nonneg a,sq_nonneg b]
  have hsmall : ∀ z : ℤ, -(p : ℤ) < z → z < p → (p : ℤ) ∣ z → z=0 := by
    intro z hl hu ⟨d,hd⟩
    have hpZ : (0 : ℤ) < p := by omega
    by_cases hd0 : d=0
    · simp [hd,hd0]
    · have hdcase : d ≤ -1 ∨ 1 ≤ d := by omega
      rcases hdcase with h | h <;> nlinarith
  obtain ⟨hal,hau⟩ := ha
  obtain ⟨hbl,hbu⟩ := hb
  obtain ⟨hcl,hcu⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num at hn <;> norm_num at hx <;> norm_num at hmem <;>
    have he := hsmall _ (by omega) (by omega) hmem <;> omega

def ternaryIntCross (x y : TernaryIntPoint) : TernaryIntPoint :=
  ((x.1.2*y.2-x.2*y.1.2,x.2*y.1.1-x.1.1*y.2),x.1.1*y.1.2-x.1.2*y.1.1)

def normalizedDualCross (p j k : ℕ) (x y : TernaryIntPoint) : TernaryIntPoint :=
  let c := ternaryIntCross x y
  (((p : ℤ)*c.1.1-(j : ℤ)*c.1.2-(k : ℤ)*c.2,c.1.2),c.2)

theorem normalizedDualCross_mem (p j k : ℕ) (x y : TernaryIntPoint) :
    normalizedDualCross p j k x y ∈ congruenceLattice p ((1,(j : ℤ)),(k : ℤ)) := by
  refine ⟨(ternaryIntCross x y).1.1,?_⟩
  simp [ternaryIntDot,ternaryDot,normalizedDualCross]
  ring

set_option maxHeartbeats 0 in
theorem normalizedDualCross_norm (p j k : ℕ)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) (x y : TernaryIntPoint) :
    ternaryIntNorm (normalizedDualCross p j k x y) =
      (normalizedGram p j k).norm x*(normalizedGram p j k).norm y-
        (normalizedGram p j k).dot x y^2 := by
  have hh := normalizedGram_relation p j k hi
  unfold ternaryIntNorm ternaryNorm normalizedDualCross ternaryIntCross
    IntegralTernaryGram.norm IntegralTernaryGram.dot
  dsimp [normalizedGram] at hh ⊢
  linear_combination -((x.2*y.1.1-x.1.1*y.2)^2+(x.1.1*y.1.2-x.1.2*y.1.1)^2)*hh

theorem normalizedDualCross_ne_zero {p : ℕ} (hp : p ≠ 0) (j k : ℕ)
    (B : TernaryUnimodularBasis) : normalizedDualCross p j k B.x B.y ≠ 0 := by
  intro hz
  have h2 := congrArg (fun x : TernaryIntPoint => x.1.2) hz
  have h3 := congrArg (fun x : TernaryIntPoint => x.2) hz
  have h1 := congrArg (fun x : TernaryIntPoint => x.1.1) hz
  change (ternaryIntCross B.x B.y).1.2=0 at h2
  change (ternaryIntCross B.x B.y).2=0 at h3
  change (p : ℤ)*(ternaryIntCross B.x B.y).1.1-
    (j : ℤ)*(ternaryIntCross B.x B.y).1.2-(k : ℤ)*(ternaryIntCross B.x B.y).2=0 at h1
  rw [h2,h3,mul_zero,mul_zero,sub_zero,sub_zero] at h1
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hc1 := (mul_eq_zero.mp h1).resolve_left hpZ
  have hd : ternaryPointDet B.x B.y B.z = 0 := by
    have hid : ternaryPointDet B.x B.y B.z =
        (ternaryIntCross B.x B.y).1.1*B.z.1.1+
        (ternaryIntCross B.x B.y).1.2*B.z.1.2+(ternaryIntCross B.x B.y).2*B.z.2 := by
      simp [ternaryIntCross,ternaryPointDet,ternaryDet]; ring
    rw [hid,hc1,h2,h3]
    simp
  rcases B.det_unit with h | h <;> omega

theorem normalizedGram_minor_ge_three {p j k : ℕ}
    (hj : 1 < j) (hjk : j < k) (hkp : 2*k < p)
    (hi : (p : ℤ) ∣ 1+(j : ℤ)^2+(k : ℤ)^2) (B : TernaryUnimodularBasis) :
    3 ≤ (B.gram (normalizedGram p j k)).minor := by
  have hh := congruence_norm_ge_three (by decide : 0 < 1) hj hjk hkp
    (normalizedDualCross p j k B.x B.y) (normalizedDualCross_ne_zero (by omega) j k B)
    (normalizedDualCross_mem p j k B.x B.y)
  simpa only [normalizedDualCross_norm p j k hi,TernaryUnimodularBasis.gram,
    IntegralTernaryGram.minor] using hh

end Ramanujan.MultiQuintuple
