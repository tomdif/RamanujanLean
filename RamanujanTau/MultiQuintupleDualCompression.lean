/-
# Cubic compression of Poisson-dual Watson amplitudes

The apparent eight-term Fourier amplitude of a projective dual vector is
much smaller than it first appears.  If

  w_s = lambda * a_s + p * z_s

and `q` is an inverse of `3*k` modulo `p`, then every affine phase difference
is not merely even: it is a multiple of `2*p`.  More precisely,

  delta_s = 2*p*(z_s - 3*z_3*q*a_s - lambda*a_s*t),

where `3*q*k = 1 + p*t`.  Consequently a supported factor sees only one of
the two nontrivial cube roots of unity.  The signed eight-vertex cube thus
collapses to one common cubic factor times a single `6*p`-th-root phase per
dual vector.

This is the arithmetic reduction needed before applying sparse
roots-of-unity rigidity: a shell of `V` supported vectors has cyclotomic
weight `V`, not `8*V`.  Its compressed phases are themselves divisible by
three, reducing the root order to `2*p`; for an even complete shell, the
first possible non-pairing weight is consequently `2*p`.
-/
import RamanujanTau.MultiQuintupleDualPerfect

namespace Ramanujan.MultiQuintuple

/-- The integral quotient left after removing the forced factor `2*p` from
a projective Watson phase difference. -/
def dualWatsonReducedDelta
    (q lambda a z3 zs inverseError : ℤ) : ℤ :=
  zs - 3 * z3 * q * a - lambda * a * inverseError

/-- **Projective phase quantization.**  Every Watson phase difference of a
projective dual lift is exactly `2*p` times an integer. -/
theorem dualWatsonDelta_projectiveLift_eq_two_mul_p
    (p q lambda a k w3 ws z3 zs inverseError : ℤ)
    (hw3 : w3 = lambda * k + p * z3)
    (hws : ws = lambda * a + p * zs)
    (hinverse : 3 * q * k = 1 + p * inverseError) :
    dualWatsonDelta q a w3 ws =
      2 * p * dualWatsonReducedDelta q lambda a z3 zs inverseError := by
  simp only [dualWatsonDelta, dualWatsonReducedDelta]
  rw [hw3, hws]
  linear_combination -2 * lambda * a * hinverse

/-- Congruence-level inverse data always supplies the integral error and the
quantized phase formula used above. -/
theorem exists_dualWatsonDelta_projectiveLift_quantization
    (p q lambda a k w3 ws z3 zs : ℤ)
    (hw3 : w3 = lambda * k + p * z3)
    (hws : ws = lambda * a + p * zs)
    (hinverse : p ∣ 3 * q * k - 1) :
    ∃ inverseError : ℤ,
      3 * q * k = 1 + p * inverseError ∧
      dualWatsonDelta q a w3 ws =
        2 * p * dualWatsonReducedDelta
          q lambda a z3 zs inverseError := by
  rcases hinverse with ⟨inverseError, hinverse⟩
  have hinverse' : 3 * q * k = 1 + p * inverseError := by
    linarith
  exact ⟨inverseError, hinverse',
    dualWatsonDelta_projectiveLift_eq_two_mul_p
      p q lambda a k w3 ws z3 zs inverseError hw3 hws hinverse'⟩

/-- After the forced `2*p` is removed, divisibility by `6*p` is exactly
divisibility of the reduced phase by three. -/
theorem six_mul_p_dvd_two_mul_p_iff_three_dvd
    (p t : ℤ) (hp : p ≠ 0) :
    6 * p ∣ 2 * p * t ↔ 3 ∣ t := by
  constructor
  · rintro ⟨c, hc⟩
    have hcancel : 2 * t = 6 * c := by
      apply mul_left_cancel₀ hp
      nlinarith
    exact ⟨c, by linarith⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

/-- Support of one projective coordinate is therefore a purely mod-three
condition on its reduced phase. -/
theorem projectiveDual_coordinate_supported_iff_three_not_dvd
    (p q lambda a k w3 ws z3 zs inverseError : ℤ) (hp : p ≠ 0)
    (hw3 : w3 = lambda * k + p * z3)
    (hws : ws = lambda * a + p * zs)
    (hinverse : 3 * q * k = 1 + p * inverseError) :
    ¬(6 * p ∣ dualWatsonDelta q a w3 ws) ↔
      ¬(3 ∣ dualWatsonReducedDelta q lambda a z3 zs inverseError) := by
  rw [dualWatsonDelta_projectiveLift_eq_two_mul_p
    p q lambda a k w3 ws z3 zs inverseError hw3 hws hinverse,
    six_mul_p_dvd_two_mul_p_iff_three_dvd p
      (dualWatsonReducedDelta q lambda a z3 zs inverseError) hp]

/-- The full three-coordinate support predicate is exactly the conjunction
of three nonzero cubic residues. -/
theorem dualWatsonSupported_projectiveLift_iff_cubic
    (p q lambda i j k w1 w2 w3 z1 z2 z3 inverseError : ℤ) (hp : p ≠ 0)
    (hw1 : w1 = lambda * i + p * z1)
    (hw2 : w2 = lambda * j + p * z2)
    (hw3 : w3 = lambda * k + p * z3)
    (hinverse : 3 * q * k = 1 + p * inverseError) :
    DualWatsonSupported p q i j k w1 w2 w3 ↔
      ¬(3 ∣ dualWatsonReducedDelta q lambda i z3 z1 inverseError) ∧
      ¬(3 ∣ dualWatsonReducedDelta q lambda j z3 z2 inverseError) ∧
      ¬(3 ∣ dualWatsonReducedDelta q lambda k z3 z3 inverseError) := by
  simp only [DualWatsonSupported]
  rw [projectiveDual_coordinate_supported_iff_three_not_dvd
      p q lambda i k w3 w1 z3 z1 inverseError hp hw3 hw1 hinverse,
    projectiveDual_coordinate_supported_iff_three_not_dvd
      p q lambda j k w3 w2 z3 z2 inverseError hp hw3 hw2 hinverse,
    projectiveDual_coordinate_supported_iff_three_not_dvd
      p q lambda k k w3 w3 z3 z3 inverseError hp hw3 hw3 hinverse]

/-- An integer not divisible by three is congruent to exactly one of the two
signs modulo three, in a quotient-bearing form convenient for phase powers. -/
theorem exists_three_mul_add_sign_of_three_not_dvd
    (t : ℤ) (ht : ¬(3 ∣ t)) :
    (∃ r : ℤ, t = 3 * r + 1) ∨ (∃ r : ℤ, t = 3 * r - 1) := by
  have hnonzero : t % 3 ≠ 0 := by
    intro hzero
    exact ht (Int.dvd_iff_emod_eq_zero.mpr hzero)
  have hnonneg : 0 ≤ t % 3 := Int.emod_nonneg t (by norm_num)
  have hlt : t % 3 < 3 := Int.emod_lt_of_pos t (by norm_num)
  have hdivision := Int.mul_ediv_add_emod t 3
  have hcases : t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hcases with hone | htwo
  · exact Or.inl ⟨t / 3, by omega⟩
  · exact Or.inr ⟨t / 3 + 1, by omega⟩

/-- Boolean-valued version of the two nonzero residue classes modulo three. -/
theorem exists_three_mul_add_one_sub_two_mul_bit_of_three_not_dvd
    (t : ℤ) (ht : ¬(3 ∣ t)) :
    ∃ r b : ℤ, (b = 0 ∨ b = 1) ∧ t = 3 * r + 1 - 2 * b := by
  rcases exists_three_mul_add_sign_of_three_not_dvd t ht with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, 0, Or.inl rfl, by omega⟩
  · exact ⟨r, 1, Or.inr rfl, by omega⟩

/-- **Two-cubic-value theorem.**  A supported projective phase difference is
congruent to `+2*p` or `-2*p` modulo `6*p`; no other root-of-unity value can
occur in an individual Watson factor. -/
theorem supported_projectiveDual_delta_eq_two_mul_p_add_six_mul_p
    (p q lambda a k w3 ws z3 zs inverseError : ℤ) (hp : p ≠ 0)
    (hw3 : w3 = lambda * k + p * z3)
    (hws : ws = lambda * a + p * zs)
    (hinverse : 3 * q * k = 1 + p * inverseError)
    (hsupported : ¬(6 * p ∣ dualWatsonDelta q a w3 ws)) :
    (∃ r : ℤ, dualWatsonDelta q a w3 ws = 2 * p + 6 * p * r) ∨
      (∃ r : ℤ, dualWatsonDelta q a w3 ws = -2 * p + 6 * p * r) := by
  have hreduced :
      ¬(3 ∣ dualWatsonReducedDelta q lambda a z3 zs inverseError) :=
    (projectiveDual_coordinate_supported_iff_three_not_dvd
      p q lambda a k w3 ws z3 zs inverseError hp hw3 hws hinverse).mp
        hsupported
  have hdelta := dualWatsonDelta_projectiveLift_eq_two_mul_p
    p q lambda a k w3 ws z3 zs inverseError hw3 hws hinverse
  rcases exists_three_mul_add_sign_of_three_not_dvd
      (dualWatsonReducedDelta q lambda a z3 zs inverseError) hreduced with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨r, by rw [hdelta, hr]; ring⟩
  · exact Or.inr ⟨r, by rw [hdelta, hr]; ring⟩

/-! ### Algebraic collapse of the three support factors -/

/-- At a sixth root `rho` with `rho^3 = -1`, the conjugate cubic Watson
factor differs from the standard one by exactly the phase `rho`. -/
theorem one_sub_fourth_eq_mul_one_sub_square_of_cube_eq_neg_one
    {A : Type*} [CommRing A] (rho : A) (hcube : rho ^ 3 = -1) :
    1 - rho ^ 4 = rho * (1 - rho ^ 2) := by
  calc
    1 - rho ^ 4 = 1 - rho * rho ^ 3 := by ring
    _ = 1 + rho := by rw [hcube]; ring
    _ = rho - rho ^ 3 := by rw [hcube]; ring
    _ = rho * (1 - rho ^ 2) := by ring

/-- Select the `+2p` cubic factor (`false`) or its `-2p` conjugate
(`true`). -/
def cubicWatsonFactor
    {A : Type*} [CommRing A] (rho : A) (conjugate : Bool) : A :=
  if conjugate then 1 - rho ^ 4 else 1 - rho ^ 2

/-- Number of conjugate factors among the three Watson coordinates. -/
def cubicWatsonConjugateCount (b1 b2 b3 : Bool) : ℕ :=
  (if b1 then 1 else 0) + (if b2 then 1 else 0) +
    (if b3 then 1 else 0)

/-- **Eight-to-one cubic factor collapse.**  Every choice of the three
supported projective factors is one common cube times a single sixth-root
phase.  This is the algebraic identity behind the compressed dual scanner. -/
theorem product_cubicWatsonFactor_eq_common_cube
    {A : Type*} [CommRing A] (rho : A) (hcube : rho ^ 3 = -1)
    (b1 b2 b3 : Bool) :
    cubicWatsonFactor rho b1 * cubicWatsonFactor rho b2 *
        cubicWatsonFactor rho b3 =
      rho ^ cubicWatsonConjugateCount b1 b2 b3 *
        (1 - rho ^ 2) ^ 3 := by
  have hconjugate :=
    one_sub_fourth_eq_mul_one_sub_square_of_cube_eq_neg_one rho hcube
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp [cubicWatsonFactor, cubicWatsonConjugateCount, hconjugate] <;> ring

/-! ### Antipodal symmetry after compression -/

/-- Integer representative of the compressed vector phase: the old base
phase plus one shift by `p` for every conjugate cubic factor. -/
def dualWatsonCompressedPhase (p base conjugateCount : ℤ) : ℤ :=
  base + p * conjugateCount

/-- Negating a dual vector negates its uncompressed base phase. -/
theorem dualWatsonBasePhase_neg
    (q R u w1 w2 w3 : ℤ) :
    dualWatsonBasePhase q R (-u) (-w1) (-w2) (-w3) =
      -dualWatsonBasePhase q R u w1 w2 w3 := by
  simp only [dualWatsonBasePhase]
  ring

/-- Negation swaps the two cubic values in all three coordinates.  Hence if
one vector has `n` conjugate factors, its antipode has `3-n`, and their
compressed phases are related by `E(-w)=3p-E(w)`. -/
theorem dualWatsonCompressedPhase_antipodal
    (p base conjugateCount : ℤ) :
    dualWatsonCompressedPhase p (-base) (3 - conjugateCount) =
      3 * p - dualWatsonCompressedPhase p base conjugateCount := by
  simp only [dualWatsonCompressedPhase]
  ring

/-! ### The compressed phase has order `2*p`, not `6*p` -/

/-- If the three reduced phase differences are written with signs
`1-2*b_s`, then counting the negative signs cancels their entire residue
modulo three.  The compressed phase is therefore divisible by three. -/
theorem three_dvd_compressedPhase_of_signed_reduced
    (p q i j k R u w1 w2 w3 t1 t2 t3 r1 r2 r3 b1 b2 b3 : ℤ)
    (hw1 : w1 = 3 * w3 * q * i + p * t1)
    (hw2 : w2 = 3 * w3 * q * j + p * t2)
    (hw3 : w3 = 3 * w3 * q * k + p * t3)
    (ht1 : t1 = 3 * r1 + 1 - 2 * b1)
    (ht2 : t2 = 3 * r2 + 1 - 2 * b2)
    (ht3 : t3 = 3 * r3 + 1 - 2 * b3) :
    3 ∣ dualWatsonCompressedPhase p
      (dualWatsonBasePhase q R u w1 w2 w3) (b1 + b2 + b3) := by
  have hsum : w1 + w2 + w3 =
      3 * w3 * q * (i + j + k) + p * (t1 + t2 + t3) := by
    linear_combination hw1 + hw2 + hw3
  refine ⟨2 * w3 * q * R + 2 * u - w3 * q * (i + j + k) -
      p * (r1 + r2 + r3 + 1 - (b1 + b2 + b3)), ?_⟩
  simp only [dualWatsonCompressedPhase, dualWatsonBasePhase]
  rw [show w1 + w2 + w3 =
    3 * w3 * q * (i + j + k) + p * (t1 + t2 + t3) from hsum,
    ht1, ht2, ht3]
  ring

/-- **Order reduction for the projective amplitude.**  For every supported
projective lift, there are mod-three sign choices (recorded here as
zero-one integers) for which the compressed phase is a multiple of three.
Thus, after removal of the common cubic factor, all vector phases are
`2*p`-th roots of unity. -/
theorem exists_projective_compressedPhase_three_dvd
    (p q lambda i j k R u w1 w2 w3 z1 z2 z3 inverseError : ℤ) (hp : p ≠ 0)
    (hw1 : w1 = lambda * i + p * z1)
    (hw2 : w2 = lambda * j + p * z2)
    (hw3 : w3 = lambda * k + p * z3)
    (hinverse : 3 * q * k = 1 + p * inverseError)
    (hsupported : DualWatsonSupported p q i j k w1 w2 w3) :
    ∃ b1 b2 b3 : ℤ,
      (b1 = 0 ∨ b1 = 1) ∧ (b2 = 0 ∨ b2 = 1) ∧
      (b3 = 0 ∨ b3 = 1) ∧
      (∃ r1 : ℤ, dualWatsonReducedDelta
        q lambda i z3 z1 inverseError = 3 * r1 + 1 - 2 * b1) ∧
      (∃ r2 : ℤ, dualWatsonReducedDelta
        q lambda j z3 z2 inverseError = 3 * r2 + 1 - 2 * b2) ∧
      (∃ r3 : ℤ, dualWatsonReducedDelta
        q lambda k z3 z3 inverseError = 3 * r3 + 1 - 2 * b3) ∧
      3 ∣ dualWatsonCompressedPhase p
        (dualWatsonBasePhase q R u w1 w2 w3) (b1 + b2 + b3) := by
  have hcubic := (dualWatsonSupported_projectiveLift_iff_cubic
    p q lambda i j k w1 w2 w3 z1 z2 z3 inverseError hp
      hw1 hw2 hw3 hinverse).mp hsupported
  rcases hcubic with ⟨ht1, ht2, ht3⟩
  obtain ⟨r1, b1, hb1, hr1⟩ :=
    exists_three_mul_add_one_sub_two_mul_bit_of_three_not_dvd _ ht1
  obtain ⟨r2, b2, hb2, hr2⟩ :=
    exists_three_mul_add_one_sub_two_mul_bit_of_three_not_dvd _ ht2
  obtain ⟨r3, b3, hb3, hr3⟩ :=
    exists_three_mul_add_one_sub_two_mul_bit_of_three_not_dvd _ ht3
  refine ⟨b1, b2, b3, hb1, hb2, hb3, ⟨r1, hr1⟩, ⟨r2, hr2⟩,
    ⟨r3, hr3⟩, ?_⟩
  apply three_dvd_compressedPhase_of_signed_reduced
    p q i j k R u w1 w2 w3
      (dualWatsonReducedDelta q lambda i z3 z1 inverseError)
      (dualWatsonReducedDelta q lambda j z3 z2 inverseError)
      (dualWatsonReducedDelta q lambda k z3 z3 inverseError)
      r1 r2 r3 b1 b2 b3
  · simp only [dualWatsonReducedDelta]
    rw [hw1, hw3]
    linear_combination -lambda * i * hinverse
  · simp only [dualWatsonReducedDelta]
    rw [hw2, hw3]
    linear_combination -lambda * j * hinverse
  · simp only [dualWatsonReducedDelta]
    rw [hw3]
    linear_combination -lambda * k * hinverse
  · exact hr1
  · exact hr2
  · exact hr3

/-! ### Exact `2*p` pairing threshold -/

/-- Arithmetic core of the sparse `2*p`-th-root pairing theorem.  In the
prime-bucket normal form, a zero cyclotomic sum has one constant signed
bucket difference `c`.  Its weight is at least `p*|c|`, and its parity is
the parity of `p*c`.  Thus an even zero of weight below `2*p` forces `c=0`,
which is exactly opposite-phase balance in every bucket. -/
theorem constant_bucket_difference_eq_zero_of_even_weight_lt_two_mul
    (p weight c : ℤ) (hp : 0 < p)
    (hpodd : ∃ a : ℤ, p = 2 * a + 1)
    (hweightEven : ∃ b : ℤ, weight = 2 * b)
    (hweightParity : ∃ z : ℤ, weight = p * c + 2 * z)
    (hlower : p * |c| ≤ weight)
    (hupper : weight < 2 * p) :
    c = 0 := by
  obtain ⟨a, rfl⟩ := hpodd
  obtain ⟨b, hweight⟩ := hweightEven
  obtain ⟨z, hparity⟩ := hweightParity
  have hcEven : ∃ d : ℤ, c = 2 * d := by
    refine ⟨b - a * c - z, ?_⟩
    nlinarith
  obtain ⟨d, rfl⟩ := hcEven
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg (by omega : 0 ≤ 2 * d)] at hlower
    by_cases hd0 : d = 0
    · simp [hd0]
    · exfalso
      have hproduct : 0 ≤ (2 * a + 1) * (2 * d - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  · rw [abs_of_nonpos (by omega : 2 * d ≤ 0)] at hlower
    exfalso
    have hproduct : 0 ≤ (2 * a + 1) * (-2 * d - 2) :=
      mul_nonneg (by omega) (by omega)
    nlinarith

end Ramanujan.MultiQuintuple
