import RamanujanTau.BLBound.Threshold

/-!
# Lower bounds for Boylan–Webb's threshold in rank two

The rank-two analogue of `BLBound.not_mem_of_errors`. Suppose
`L(2n+5) − k₁ L(2n+3) − k₀ L(2n+1) = ℓ^(n+1) G_n` for every `n`, two functionals `o₁, o₂`
separate `L(2n+1), L(2n+3)` modulo `ℓ` (unit determinant), and a third functional `obs`
kills `U L(2n+1)` but sees `U G_n` modulo `ℓ`. Then `L(2k+1) ∉ Λ^odd(2k+3, m)` whenever
`k + 2 ≤ m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrienFinal BoylanWebb AtkinOBrien

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- the determinant of two functionals on two series. -/
def det2 (o₁ o₂ : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (x y : PS ℓ) : ℤ_[ℓ] := o₁ x * o₂ y - o₁ y * o₂ x

/-- **Rank-two `ℓ`-adic criterion for `L(2k+1) ∉ Λ^odd(2k+3, m)`**, at one index `k`: the
observation only has to see the error `G k`. -/
theorem not_mem_of_errors2_at (k₀ k₁ : ℤ_[ℓ]) (G : ℕ → PS ℓ) (o₁ o₂ obs : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (hrec : ∀ n, Ll ℓ (2 * n + 5) - k₁ • Ll ℓ (2 * n + 3) - k₀ • Ll ℓ (2 * n + 1) =
      (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n)
    (hind : ∀ n, PadicInt.toZMod (det2 o₁ o₂ (Ll ℓ (2 * n + 1)) (Ll ℓ (2 * n + 3))) ≠ 0)
    (heven : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (Ll ℓ (2 * n + 1)))) = 0)
    (m k : ℕ) (hk : k + 2 ≤ m) (herr : PadicInt.toZMod (obs (Ulin ℓ (G k))) ≠ 0) :
    redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1) := by
  intro hmem
  set π := PadicInt.toZModPow (p := ℓ) m
  have hred : ∀ b, redm ℓ m (L ℓ b) = PowerSeries.map π (Ll ℓ b) := fun b =>
    (toZModPow_Ll m b).symm
  set Y := Ll ℓ (2 * k + 3)
  set Z := Ll ℓ (2 * k + 5)
  -- Step 1: every later odd iterate is a combination of `Y, Z` modulo `ℓ^(k+2)`.
  have hpair : ∀ j, (∃ a c : ℤ_[ℓ], Dvd (ℓ : ℤ_[ℓ]) (k + 2)
      (Ll ℓ (2 * (k + 1 + j) + 1) - a • Y - c • Z)) ∧
      (∃ a c : ℤ_[ℓ], Dvd (ℓ : ℤ_[ℓ]) (k + 2) (Ll ℓ (2 * (k + 1 + j) + 3) - a • Y - c • Z)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨1, 0, 0, ?_⟩, ⟨0, 1, 0, ?_⟩⟩
      · simp only [Y, add_zero, one_smul, zero_smul, sub_zero, smul_zero]
        rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, sub_self]
      · simp only [Z, add_zero, one_smul, zero_smul, sub_zero, smul_zero]
        rw [show 2 * (k + 1) + 3 = 2 * k + 5 by ring]; simp
    | succ j ih =>
      obtain ⟨⟨a₀, c₀, h₀⟩, ⟨a₁, c₁, h₁⟩⟩ := ih
      refine ⟨⟨a₁, c₁, ?_⟩, ⟨k₁ * a₁ + k₀ * a₀, k₁ * c₁ + k₀ * c₀, ?_⟩⟩
      · rwa [show 2 * (k + 1 + (j + 1)) + 1 = 2 * (k + 1 + j) + 3 by ring]
      · have hr := hrec (k + 1 + j)
        have he : Ll ℓ (2 * (k + 1 + (j + 1)) + 3) - (k₁ * a₁ + k₀ * a₀) • Y -
            (k₁ * c₁ + k₀ * c₀) • Z =
            k₁ • (Ll ℓ (2 * (k + 1 + j) + 3) - a₁ • Y - c₁ • Z) +
              k₀ • (Ll ℓ (2 * (k + 1 + j) + 1) - a₀ • Y - c₀ • Z) +
              (ℓ : ℤ_[ℓ]) ^ (k + 1 + j + 1) • G (k + 1 + j) := by
          rw [← hr, show 2 * (k + 1 + (j + 1)) + 3 = 2 * (k + 1 + j) + 5 by ring]
          simp only [smul_sub, add_smul, mul_smul]
          abel
        rw [he]
        exact Dvd_add (Dvd_add (Dvd_smul _ h₁) (Dvd_smul _ h₀))
          (Dvd_mono (by omega) ⟨G (k + 1 + j), rfl⟩)
  -- Step 2: the same modulo `ℓ^m`, for every element of the module.
  set ϖ : Rm ℓ m := (ℓ : Rm ℓ m) ^ (k + 2)
  have hP : ∀ y ∈ Lam ℓ m (2 * (k + 1) + 1), ∃ a c : Rm ℓ m, ∃ V : PowerSeries (Rm ℓ m),
      y = a • PowerSeries.map π Y + c • PowerSeries.map π Z + ϖ • V := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨a, c, W, hW⟩ := (hpair (i - (k + 1))).1
      rw [show k + 1 + (i - (k + 1)) = i by omega] at hW
      refine ⟨π a, π c, PowerSeries.map π W, ?_⟩
      have hm := congrArg (PowerSeries.map π) hW
      rw [map_sub, map_sub, map_smul_PS, map_smul_PS, map_smul_PS, map_pow, map_natCast] at hm
      rw [hred]
      rw [← hm]; abel
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, c, V, rfl⟩ := hx
      obtain ⟨b, d, W, rfl⟩ := hy
      exact ⟨a + b, c + d, V + W, by rw [add_smul, add_smul, smul_add]; abel⟩
    | smul e x _ hx =>
      obtain ⟨a, c, V, rfl⟩ := hx
      exact ⟨e * a, e * c, e • V, by rw [smul_add, smul_add, mul_smul, mul_smul, smul_comm e ϖ]⟩
  obtain ⟨a, c, V, hV⟩ := hP _ hmem
  -- Step 3: lift to `ℤ_ℓ`.
  set aL : ℤ_[ℓ] := ((a.val : ℕ) : ℤ_[ℓ])
  set cL : ℤ_[ℓ] := ((c.val : ℕ) : ℤ_[ℓ])
  have haL : π aL = a := by rw [map_natCast, ZMod.natCast_zmod_val]
  have hcL : π cL = c := by rw [map_natCast, ZMod.natCast_zmod_val]
  have hD : Dvd (ℓ : ℤ_[ℓ]) (k + 2) (Ll ℓ (2 * k + 1) - aL • Y - cL • Z) := by
    have h0 : PowerSeries.map π
        (Ll ℓ (2 * k + 1) - aL • Y - cL • Z - (ℓ : ℤ_[ℓ]) ^ (k + 2) • liftPS m V) = 0 := by
      rw [map_sub, map_sub, map_sub, map_smul_PS, map_smul_PS, map_smul_PS, map_liftPS, haL, hcL,
        map_pow, map_natCast, ← hred, hV]
      abel
    obtain ⟨E, hE⟩ := Dvd_of_map_eq_zero m h0
    refine ⟨(ℓ : ℤ_[ℓ]) ^ (m - (k + 2)) • E + liftPS m V, ?_⟩
    rw [smul_add, ← mul_smul, ← pow_add, show k + 2 + (m - (k + 2)) = m by omega, ← hE]
    abel
  -- Step 4: three scalar observations.
  set X := Ll ℓ (2 * k + 1)
  set P : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ (k + 1)
  have hobs : ∀ f : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ], ∃ w : ℤ_[ℓ],
      (1 - cL * k₀) * f X - (aL + cL * k₁) * f Y = P * (cL * f (G k) + ℓ * w) := by
    intro f
    obtain ⟨E, hE⟩ := hD
    refine ⟨f E, ?_⟩
    have hZ : Z = k₁ • Y + k₀ • X + P • G k := by
      rw [← hrec k]; simp only [Z, Y, X]; abel
    have h1 := congrArg f hE
    rw [hZ, map_sub, map_sub, map_smul, map_smul, map_add, map_add, map_smul, map_smul, map_smul,
      map_smul] at h1
    simp only [smul_eq_mul] at h1
    rw [show (ℓ : ℤ_[ℓ]) ^ (k + 2) = P * ℓ by simp only [P]; ring] at h1
    linear_combination h1
  obtain ⟨w₁, hw₁⟩ := hobs o₁
  obtain ⟨w₂, hw₂⟩ := hobs o₂
  obtain ⟨w₃, hw₃⟩ := hobs (obs ∘ₗ Ulin ℓ)
  simp only [LinearMap.comp_apply] at hw₃
  set α := 1 - cL * k₀
  set β := aL + cL * k₁
  set Δ := det2 o₁ o₂ X Y
  set r₁ := cL * o₁ (G k) + ℓ * w₁
  set r₂ := cL * o₂ (G k) + ℓ * w₂
  have hα : α * Δ = P * (r₁ * o₂ Y - r₂ * o₁ Y) := by
    simp only [Δ, det2]; linear_combination o₂ Y * hw₁ - o₁ Y * hw₂
  have hβ : β * Δ = P * (r₁ * o₂ X - r₂ * o₁ X) := by
    simp only [Δ, det2]; linear_combination o₂ X * hw₁ - o₁ X * hw₂
  have hP0 : P ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hcancel : (r₁ * o₂ Y - r₂ * o₁ Y) * obs (Ulin ℓ X) - (r₁ * o₂ X - r₂ * o₁ X) * obs (Ulin ℓ Y) =
      Δ * (cL * obs (Ulin ℓ (G k)) + ℓ * w₃) := by
    apply mul_left_cancel₀ hP0
    linear_combination Δ * hw₃ - obs (Ulin ℓ X) * hα + obs (Ulin ℓ Y) * hβ
  have hz := congrArg PadicInt.toZMod hcancel
  have hX0 : PadicInt.toZMod (obs (Ulin ℓ X)) = 0 := heven k
  have hY0 : PadicInt.toZMod (obs (Ulin ℓ Y)) = 0 := by
    simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] using heven (k + 1)
  simp only [map_sub, map_mul, map_add, hX0, hY0, toZMod_prime, mul_zero, zero_mul, sub_zero,
    add_zero] at hz
  have hc0 : PadicInt.toZMod cL = 0 := by
    rcases mul_eq_zero.mp hz.symm with h | h
    · exact absurd h (hind k)
    · exact (mul_eq_zero.mp h).resolve_right herr
  have h1 := congrArg PadicInt.toZMod hα
  simp only [α, P, map_sub, map_one, map_mul, map_pow, hc0, toZMod_prime, zero_mul, sub_zero,
    one_mul, zero_pow (Nat.succ_ne_zero k)] at h1
  exact hind k h1

/-- **Rank-two `ℓ`-adic criterion for `L(2k+1) ∉ Λ^odd(2k+3, m)`.** -/
theorem not_mem_of_errors2 (k₀ k₁ : ℤ_[ℓ]) (G : ℕ → PS ℓ) (o₁ o₂ obs : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (hrec : ∀ n, Ll ℓ (2 * n + 5) - k₁ • Ll ℓ (2 * n + 3) - k₀ • Ll ℓ (2 * n + 1) =
      (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n)
    (hind : ∀ n, PadicInt.toZMod (det2 o₁ o₂ (Ll ℓ (2 * n + 1)) (Ll ℓ (2 * n + 3))) ≠ 0)
    (heven : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (Ll ℓ (2 * n + 1)))) = 0)
    (herr : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (G n))) ≠ 0)
    (m k : ℕ) (hk : k + 2 ≤ m) :
    redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1) :=
  not_mem_of_errors2_at k₀ k₁ G o₁ o₂ obs hrec hind heven m k hk (herr k)

end

end RamanujanTau.BLBound
