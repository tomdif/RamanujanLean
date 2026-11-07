import RamanujanTau.BLBound.Threshold2

/-!
# Lower bounds for Boylan–Webb's threshold for a recurrence of order `q + 1`

Suppose `L(2n+2q+3) − Σ_{j ≤ q} k_j L(2(n+j)+1) = ℓ^(n+1) G_n` for every `n`, functionals
`o₀, …, o_q` have unit determinant on `L(2k+1), …, L(2(k+q)+1)` modulo `ℓ`, and `obs` kills
`U L(2n+1)` modulo `ℓ` for every `n` but not `U G_k`. Then `L(2k+1) ∉ Λ^odd(2k+3, m)` when
`k + 2 ≤ m`. For `q = 1` this is `not_mem_of_errors2_at`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrienFinal BoylanWebb AtkinOBrien

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma isUnit_of_toZMod {x : ℤ_[ℓ]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hu
  apply h
  have : x ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal x).mpr hu
  rw [← PadicInt.ker_toZMod] at this
  exact this

/-- **Order-`(q+1)` `ℓ`-adic criterion for `L(2K+1) ∉ Λ^odd(2K+3, m)`.** -/
theorem not_mem_of_errorsR (q : ℕ) (k : ℕ → ℤ_[ℓ]) (G : ℕ → PS ℓ)
    (o : Fin (q + 1) → PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (obs : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (hrec : ∀ n, Ll ℓ (2 * n + 2 * q + 3) - ∑ j ∈ Finset.range (q + 1), k j • Ll ℓ (2 * (n + j) + 1) =
      (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n)
    (heven : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (Ll ℓ (2 * n + 1)))) = 0)
    (m K : ℕ) (hK : K + 2 ≤ m)
    (hind : PadicInt.toZMod (Matrix.det (fun i j : Fin (q + 1) => o i (Ll ℓ (2 * (K + j.val) + 1)))) ≠ 0)
    (herr : PadicInt.toZMod (obs (Ulin ℓ (G K))) ≠ 0) :
    redm ℓ m (L ℓ (2 * K + 1)) ∉ Lam ℓ m (2 * (K + 1) + 1) := by
  intro hmem
  set π := PadicInt.toZModPow (p := ℓ) m
  have hred : ∀ b, redm ℓ m (L ℓ b) = PowerSeries.map π (Ll ℓ b) := fun b =>
    (toZModPow_Ll m b).symm
  set Y : ℕ → PS ℓ := fun i => Ll ℓ (2 * (K + 1 + i) + 1) with hY
  -- Step 1: every later odd iterate is a combination of `Y 0, …, Y q` modulo `ℓ^(K+2)`.
  have hcomb : ∀ n, K + 1 ≤ n → ∃ a : ℕ → ℤ_[ℓ],
      Dvd (ℓ : ℤ_[ℓ]) (K + 2) (Ll ℓ (2 * n + 1) - ∑ i ∈ Finset.range (q + 1), a i • Y i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hsmall : n < K + 1 + (q + 1)
      · obtain ⟨t, rfl⟩ : ∃ t, n = K + 1 + t := ⟨n - (K + 1), by omega⟩
        refine ⟨fun i => if i = t then 1 else 0, 0, ?_⟩
        rw [smul_zero]
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_range,
          if_pos (show t < q + 1 by omega), Y, sub_self]
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + (q + 1) := ⟨n - (q + 1), by omega⟩
        have hr := hrec n'
        choose a ha using fun j : ℕ => fun (hj : j < q + 1) =>
          ih (n' + j) (by omega) (by omega)
        let b : ℕ → ℤ_[ℓ] := fun i => ∑ j ∈ (Finset.range (q + 1)).attach,
          k j.1 * a j.1 (Finset.mem_range.mp j.2) i
        refine ⟨b, ?_⟩
        have he : Ll ℓ (2 * (n' + (q + 1)) + 1) - ∑ i ∈ Finset.range (q + 1), b i • Y i =
            ∑ j ∈ (Finset.range (q + 1)).attach, k j.1 • (Ll ℓ (2 * (n' + j.1) + 1) -
              ∑ i ∈ Finset.range (q + 1), a j.1 (Finset.mem_range.mp j.2) i • Y i) +
            (ℓ : ℤ_[ℓ]) ^ (n' + 1) • G n' := by
          rw [← hr, show 2 * (n' + (q + 1)) + 1 = 2 * n' + 2 * q + 3 by ring]
          simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, b, Finset.sum_smul,
            mul_smul]
          rw [Finset.sum_comm (s := Finset.range (q + 1)),
            ← Finset.sum_attach (Finset.range (q + 1)) (fun j => k j • Ll ℓ (2 * (n' + j) + 1))]
          abel
        rw [he]
        refine Dvd_add (?_) (Dvd_mono (by omega) ⟨G n', rfl⟩)
        have : ∀ s : Finset {x // x ∈ Finset.range (q + 1)},
            Dvd (ℓ : ℤ_[ℓ]) (K + 2) (∑ j ∈ s, k j.1 • (Ll ℓ (2 * (n' + j.1) + 1) -
              ∑ i ∈ Finset.range (q + 1), a j.1 (Finset.mem_range.mp j.2) i • Y i)) := by
          intro s
          classical
          induction s using Finset.induction_on with
          | empty => exact ⟨0, by simp⟩
          | insert x s hx ihs =>
            rw [Finset.sum_insert hx]
            exact Dvd_add (Dvd_smul _ (ha x.1 (Finset.mem_range.mp x.2))) ihs
        exact this _
  -- Step 2: the same modulo `ℓ^m`, for every element of the module.
  have hsm : ∀ (c : ℤ_[ℓ]) (F : PS ℓ), PowerSeries.map π (c • F) = π c • PowerSeries.map π F :=
    fun c F => map_smul_PS m c F
  set ϖ : Rm ℓ m := (ℓ : Rm ℓ m) ^ (K + 2)
  have hP : ∀ y ∈ Lam ℓ m (2 * (K + 1) + 1), ∃ a : ℕ → Rm ℓ m, ∃ V : PowerSeries (Rm ℓ m),
      y = ∑ i ∈ Finset.range (q + 1), a i • PowerSeries.map π (Y i) + ϖ • V := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨a, W, hW⟩ := hcomb i (by omega)
      refine ⟨fun j => π (a j), PowerSeries.map π W, ?_⟩
      have hm := congrArg (PowerSeries.map π) hW
      rw [map_sub, map_sum, hsm, map_pow, map_natCast] at hm
      simp only [hsm] at hm
      rw [hred, ← sub_eq_iff_eq_add']
      exact hm
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, V, rfl⟩ := hx
      obtain ⟨b, W, rfl⟩ := hy
      refine ⟨a + b, V + W, ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    | smul e x _ hx =>
      obtain ⟨a, V, rfl⟩ := hx
      refine ⟨fun i => e * a i, e • V, ?_⟩
      rw [smul_add, Finset.smul_sum, smul_comm e ϖ]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]
  obtain ⟨a, V, hV⟩ := hP _ hmem
  -- Step 3: lift to `ℤ_ℓ`.
  set aL : ℕ → ℤ_[ℓ] := fun i => (((a i).val : ℕ) : ℤ_[ℓ])
  have haL : ∀ i, π (aL i) = a i := fun i => by rw [map_natCast, ZMod.natCast_zmod_val]
  have hD : Dvd (ℓ : ℤ_[ℓ]) (K + 2)
      (Ll ℓ (2 * K + 1) - ∑ i ∈ Finset.range (q + 1), aL i • Y i) := by
    have h0 : PowerSeries.map π
        (Ll ℓ (2 * K + 1) - ∑ i ∈ Finset.range (q + 1), aL i • Y i -
          (ℓ : ℤ_[ℓ]) ^ (K + 2) • liftPS m V) = 0 := by
      rw [map_sub, map_sub, map_sum, hsm, map_liftPS, map_pow, map_natCast, ← hred, hV]
      simp only [hsm, haL]
      abel
    obtain ⟨E, hE⟩ := Dvd_of_map_eq_zero m h0
    refine ⟨(ℓ : ℤ_[ℓ]) ^ (m - (K + 2)) • E + liftPS m V, ?_⟩
    rw [smul_add, ← mul_smul, ← pow_add, show K + 2 + (m - (K + 2)) = m by omega, ← hE]
    abel
  -- Step 4: scalar observations.
  set Z : ℕ → PS ℓ := fun j => Ll ℓ (2 * (K + j) + 1) with hZ
  set P : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ (K + 1)
  set γ : ℕ → ℤ_[ℓ] := fun j => (if j = 0 then 1 else -aL (j - 1)) - aL q * k j
  have hobs : ∀ f : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ], ∃ w : ℤ_[ℓ],
      ∑ j ∈ Finset.range (q + 1), γ j * f (Z j) = P * (aL q * f (G K) + ℓ * w) := by
    intro f
    obtain ⟨E, hE⟩ := hD
    refine ⟨f E, ?_⟩
    have hYZ : ∀ i, Y i = Z (i + 1) := fun i => by simp only [Y, Z]; congr 2; ring
    have hYq : Y q = ∑ j ∈ Finset.range (q + 1), k j • Z j + P • G K := by
      rw [hYZ, ← hrec K]; simp only [Z, P]
      rw [show 2 * (K + (q + 1)) + 1 = 2 * K + 2 * q + 3 by ring]; abel
    have h1 := congrArg f hE
    rw [Finset.sum_range_succ, hYq] at h1
    simp only [map_sub, map_add, map_sum, map_smul, smul_eq_mul, hYZ] at h1
    rw [show (ℓ : ℤ_[ℓ]) ^ (K + 2) = P * ℓ by simp only [P]; ring] at h1
    have hX : Ll ℓ (2 * K + 1) = Z 0 := by simp [Z]
    rw [hX] at h1
    have e3 : ∑ j ∈ Finset.range (q + 1), (if j = 0 then 1 else -aL (j - 1)) * f (Z j) =
        f (Z 0) - ∑ x ∈ Finset.range q, aL x * f (Z (x + 1)) := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, Nat.succ_ne_zero, Nat.add_sub_cancel, neg_mul, Finset.sum_neg_distrib,
        one_mul]
      ring
    have e4 : ∑ j ∈ Finset.range (q + 1), aL q * k j * f (Z j) =
        aL q * ∑ x ∈ Finset.range (q + 1), k x * f (Z x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e5 : ∑ j ∈ Finset.range (q + 1), γ j * f (Z j) =
        ∑ j ∈ Finset.range (q + 1), ((if j = 0 then 1 else -aL (j - 1)) * f (Z j) -
          aL q * k j * f (Z j)) := Finset.sum_congr rfl fun j _ => by simp only [γ]; ring
    rw [e5, Finset.sum_sub_distrib, e3, e4]
    linear_combination h1
  -- Step 5: the separating functionals force `γ ≡ 0 (mod P)`.
  set Mx : Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ_[ℓ] := fun i j => o i (Z j.val)
  have hMx : Mx = fun i j : Fin (q + 1) => o i (Ll ℓ (2 * (K + j.val) + 1)) := rfl
  have hunit : IsUnit Mx.det := isUnit_of_toZMod (by rw [hMx]; exact hind)
  choose w hw using fun i => hobs (o i)
  set gv : Fin (q + 1) → ℤ_[ℓ] := fun j => γ j.val
  have hmul : Mx.mulVec gv = P • fun i => aL q * o i (G K) + ℓ * w i := by
    ext i
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← hw i,
      ← Fin.sum_univ_eq_sum_range (fun j => γ j * o i (Z j))]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  set u := Mx⁻¹.mulVec fun i => aL q * o i (G K) + ℓ * w i
  have hgv : gv = P • u := by
    have := congrArg (Matrix.mulVec Mx⁻¹) hmul
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
    exact this
  have hγ : ∀ j (hj : j < q + 1), γ j = P * u ⟨j, hj⟩ := fun j hj => by
    have := congrFun hgv ⟨j, hj⟩
    simpa [gv] using this
  -- Step 6: `obs ∘ U` sees only `a_q G_K`.
  obtain ⟨w₀, hw₀⟩ := hobs (obs ∘ₗ Ulin ℓ)
  simp only [LinearMap.comp_apply] at hw₀
  have hP0 : P ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hcancel : ∑ j ∈ Finset.range (q + 1),
      (if h : j < q + 1 then u ⟨j, h⟩ else 0) * obs (Ulin ℓ (Z j)) = aL q * obs (Ulin ℓ (G K)) + ℓ * w₀ := by
    apply mul_left_cancel₀ hP0
    rw [← hw₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hγ j hj', dif_pos hj']; ring
  have hz := congrArg PadicInt.toZMod hcancel
  rw [map_sum] at hz
  simp only [map_mul, map_add, toZMod_prime, zero_mul, add_zero] at hz
  have h0 : ∀ j ∈ Finset.range (q + 1), PadicInt.toZMod (if h : j < q + 1 then u ⟨j, h⟩ else 0) *
      PadicInt.toZMod (obs (Ulin ℓ (Z j))) = 0 := fun j _ => by
    rw [show PadicInt.toZMod (obs (Ulin ℓ (Z j))) = 0 from heven (K + j), mul_zero]
  rw [Finset.sum_eq_zero h0] at hz
  have haq : PadicInt.toZMod (aL q) = 0 := (mul_eq_zero.mp hz.symm).resolve_right herr
  have hγ0 := congrArg PadicInt.toZMod (hγ 0 (by omega))
  simp only [γ, ↓reduceIte, map_sub, map_one, map_mul, haq, zero_mul, sub_zero, P, map_pow,
    toZMod_prime, zero_pow (Nat.succ_ne_zero K)] at hγ0
  exact one_ne_zero hγ0

end

end RamanujanTau.BLBound
