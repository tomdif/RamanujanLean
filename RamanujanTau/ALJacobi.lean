/-
# `κ = −(q;q)_∞³`

`K₀ = θ(x)A(x,1)` (`kappa_eq`) equals `Σ_u u(−1)^u q^{C(u,2)} = −Σ_{m≥0}(−1)^m(2m+1)q^{m(m+1)/2}`,
which is `−(q;q)_∞³` by Jacobi's identity (`jacobi_cube_identity`).
-/
import RamanujanTau.ALExt
import RamanujanTau.MockTheta5JacobiCubeProof

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section Jacobi
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `ℤ⟦X⟧ → ℂ((t))`, `X ↦ t^N` (i.e. `X ↦ q`). -/
noncomputable def ιN : PowerSeries ℤ →+* L :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp ((PowerSeries.map (Int.castRingHom ℂ)).comp
    (PowerSeries.expand N (by omega)).toRingHom)

/-- a monomial family with exponents `N·C(u,2)` and arbitrary coefficients. -/
noncomputable def cFam (c : ℤ → ℂ) : SummableFamily ℤ ℂ ℤ :=
  monoFam (thE N 0) c _ (thE_lb hN 0) (thE_fin hN 0)

lemma cFam_add (c d : ℤ → ℂ) : hs (cFam hN c) + hs (cFam hN d) = hs (cFam hN (c + d)) := by
  rw [hs_eq, hs_eq, ← SummableFamily.hsum_add, ← hs_eq]
  refine hsum_congr _ _ fun u => ?_
  simp [cFam, mono, single_add]

omit hN in
lemma natcast_toNat (a : ℤ) (h : 0 ≤ a) : ((a.toNat : ℕ) : ℂ) = (a : ℂ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

omit hN in
lemma cone_count (u : ℤ) : ∑ᶠ j, (if cone (u - j) j then sgnC (u - j) else 0 : ℂ) = u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [finsum_eq_sum_of_support_subset (s := Finset.Ico u 0)]
    · rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℂ)) fun j hj => by
        have := Finset.mem_Ico.mp hj
        rw [if_pos (show cone (u - j) j from Or.inr ⟨by omega, by omega⟩), sgnC, if_neg (by omega)]]
      simp only [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_neg, mul_one]
      rw [natcast_toNat _ (by omega)]; push_cast; ring
    · intro j hj
      rw [Function.mem_support] at hj
      split_ifs at hj with hc
      · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · simp only [Finset.coe_Ico, Set.mem_Ico]; omega
      · exact absurd rfl hj
  · rw [Int.cast_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [if_neg (by unfold cone; omega)]
  · rw [finsum_eq_sum_of_support_subset (s := Finset.Ico 0 u)]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun j hj => by
        have := Finset.mem_Ico.mp hj
        rw [if_pos (show cone (u - j) j from Or.inl ⟨by omega, by omega⟩), sgnC, if_pos (by omega)]]
      simp only [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, sub_zero]
      rw [natcast_toNat _ (by omega)]
    · intro j hj
      rw [Function.mem_support] at hj
      split_ifs at hj with hc
      · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [Finset.coe_Ico, Set.mem_Ico]; omega
        · omega
      · exact absurd rfl hj

/-- `(r, j) ↦ (r + j, j)`. -/
def eU : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- `K₀ = Σ_u u(−1)^u q^{C(u,2)}`. -/
lemma hs_kF0 : hs (kF hN 0) = hs (cFam hN fun u => (u : ℂ) * (-1) ^ u) := by
  have h1 : hs (kF hN 0) = hs (rowFam (SummableFamily.Equiv eU (kF hN 0))) := by
    rw [hs_rowFam, hs_eq, hs_eq, SummableFamily.hsum_equiv]
  rw [h1]
  refine hsum_congr _ _ fun u => ?_
  rw [rowFam_apply]
  ext n
  rw [hs, SummableFamily.coeff_hsum]
  simp only [row_apply, SummableFamily.Equiv_toFun, cFam, monoFam_apply]
  simp only [show ∀ j, eU.symm (u, j) = (u - j, j) from fun _ => rfl]
  simp only [kF_apply, mono, coeff_single, thE, zero_mul, add_zero]
  by_cases hn : N * c2 u = n
  · have : ∀ j, ((if cone (u - j) j then
        single (N * (c2 (u - j + j) + c2 0 - 0)) (sgnC (u - j) * (-1) ^ (u - j - j)) else 0 : L)).coeff n
        = (-1) ^ u * (if cone (u - j) j then sgnC (u - j) else 0) := by
      intro j
      split_ifs with hc
      · rw [coeff_single, if_pos (by rw [← hn]; simp [c2])]
        rw [show u - j - j = u + (-2) * j by ring, zpow_add₀ (by norm_num), zpow_mul]; norm_num; ring
      · simp
    rw [finsum_congr this, ← mul_finsum, cone_count, if_pos hn.symm]
    ring
  · rw [if_neg (Ne.symm hn)]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    split_ifs with hc
    · rw [coeff_single, if_neg]; intro h; apply hn; rw [h]; simp [c2]
    · simp


/-- pairing `u ↔ 1 − u`: `Σ_u u(−1)^u q^{C(u,2)} = Σ_{u≥1} (2u−1)(−1)^u q^{C(u,2)}`. -/
lemma pairing : hs (cFam hN fun u => (u : ℂ) * (-1) ^ u) =
    hs (cFam hN fun u => if 1 ≤ u then (2 * (u : ℂ) - 1) * (-1) ^ u else 0) := by
  set cA : ℤ → ℂ := fun u => if 1 ≤ u then (u : ℂ) * (-1) ^ u else 0
  set cB : ℤ → ℂ := fun u => if 1 ≤ u then 0 else (u : ℂ) * (-1) ^ u
  set cB' : ℤ → ℂ := fun u => if 1 ≤ u then ((u : ℂ) - 1) * (-1) ^ u else 0
  have h1 : (fun u : ℤ => (u : ℂ) * (-1) ^ u) = cA + cB := by
    funext u; simp only [Pi.add_apply, cA, cB]; split_ifs <;> simp
  have h2 : hs (cFam hN cB) = hs (cFam hN cB') := by
    refine (hsum_reindex' (cFam hN cB') (cFam hN cB) (Equiv.subLeft 1) 1 fun u => ?_).trans (one_mul _)
    simp only [sv, cFam, monoFam_apply, Equiv.subLeft_apply, one_mul, thE, zero_mul, add_zero,
      c2_one_sub, cB, cB']
    congr 1
    by_cases hu : 1 ≤ u
    · rw [if_neg (by omega), if_pos hu, zpow_neg_one_one_sub]; push_cast; ring
    · rw [if_pos (by omega), if_neg hu]
  have h3 : (cA + cB') = fun u : ℤ => if 1 ≤ u then (2 * (u : ℂ) - 1) * (-1) ^ u else 0 := by
    funext u; simp only [Pi.add_apply, cA, cB']; split_ifs <;> ring
  rw [h1, ← cFam_add, h2, cFam_add, h3]

/-- the triangular family `m ↦ (−1)^m (2m+1) q^{m(m+1)/2}`. -/
noncomputable def jN : SummableFamily ℤ ℂ ℕ :=
  monoFam (fun m : ℕ => (N : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ)) (fun m => (-1) ^ m * (2 * m + 1)) 0
    (fun m => by positivity)
    (fun n => (Set.finite_Iic n.toNat).subset fun m hm => by
      simp only [Set.mem_setOf_eq] at hm
      simp only [Set.mem_Iic]
      have := MockTheta5.JTP.tri_ge m
      have h1 : ((m : ℕ) : ℤ) ≤ ((m * (m + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast this
      have h2 : ((m * (m + 1) / 2 : ℕ) : ℤ) ≤ N * ((m * (m + 1) / 2 : ℕ) : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by exact_mod_cast hN)
      omega)

/-- `Σ_{u≥1} (2u−1)(−1)^u q^{C(u,2)} = −Σ_{m≥0} (−1)^m(2m+1) q^{m(m+1)/2}`. -/
lemma tri_shift : hs (cFam hN fun u => if 1 ≤ u then (2 * (u : ℂ) - 1) * (-1) ^ u else 0) = -hs (jN hN) := by
  set e : ℕ ↪ ℤ := ⟨fun m => (m : ℤ) + 1, fun a b h => by simpa using h⟩
  have h := hsum_congr (cFam hN fun u => if 1 ≤ u then (2 * (u : ℂ) - 1) * (-1) ^ u else 0)
    ((-1 : L) • (jN hN).embDomain e) fun u => by
      simp only [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, cFam, monoFam_apply]
      by_cases hu : 1 ≤ u
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, u = (m : ℤ) + 1 := ⟨(u - 1).toNat, by omega⟩
        have he : ((jN hN).embDomain e) (e m) = jN hN m := SummableFamily.embDomain_image _ _
        change _ = (-1 : L) * ((jN hN).embDomain e) (e m)
        rw [he, if_pos hu, jN, monoFam_apply, thE]
        have hT : ((m * (m + 1) / 2 : ℕ) : ℤ) = c2 ((m : ℤ) + 1) := by
          have h1 := two_c2 ((m : ℤ) + 1)
          have h2 : 2 * (m * (m + 1) / 2) = m * (m + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
          have : (2 : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ) = (m : ℤ) * (m + 1) := by exact_mod_cast h2
          nlinarith
        rw [hT, mono, mono, show (-1 : L) * single (N * c2 ((m : ℤ) + 1)) ((-1) ^ m * (2 * (m : ℂ) + 1))
          = single (N * c2 ((m : ℤ) + 1)) (-((-1) ^ m * (2 * (m : ℂ) + 1))) by rw [single_neg]; ring]
        congr 1
        · ring
        · rw [zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
      · rw [if_neg hu, SummableFamily.embDomain_notin_range]
        · simp [mono]
        · rintro ⟨m, hm⟩; simp [e] at hm; omega
  rw [h, hs_eq, hs_eq, SummableFamily.hsum_smul, SummableFamily.hsum_embDomain]; ring


lemma ιN_coeff_neg (f : PowerSeries ℤ) {n : ℤ} (hn : n < 0) : (ιN hN f).coeff n = 0 := by
  simp only [ιN, RingHom.coe_comp, Function.comp_apply]
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by rintro ⟨k, hk⟩; simp at hk; omega)

lemma ιN_coeff_nat (f : PowerSeries ℤ) (k : ℕ) :
    (ιN hN f).coeff (k : ℤ) = if N ∣ k then ((PowerSeries.coeff (k / N) f : ℤ) : ℂ) else 0 := by
  simp only [ιN, RingHom.coe_comp, Function.comp_apply, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coeff_expand]
  split_ifs <;> simp

lemma jN_coeff (n : ℤ) : (hs (jN hN)).coeff n = ∑ᶠ m : ℕ,
    if (N : ℤ) * ((m * (m + 1) / 2 : ℕ) : ℤ) = n then (-1 : ℂ) ^ m * (2 * m + 1) else 0 := by
  rw [jN, monoFam_coeff]

/-- `Σ_m (−1)^m(2m+1) q^{m(m+1)/2}` is the image of `jacobiCubeSum`. -/
lemma jN_eq : hs (jN hN) = ιN hN MockTheta5.JTP.jacobiCubeSum := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  ext n
  rw [jN_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ιN_coeff_neg hN _ hn]
    refine finsum_eq_zero_of_forall_eq_zero fun m => if_neg ?_
    intro h; have : (0 : ℤ) ≤ N * ((m * (m + 1) / 2 : ℕ) : ℤ) := by positivity
    omega
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    rw [ιN_coeff_nat]
    split_ifs with hd
    · obtain ⟨K, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ (by omega), MockTheta5.JTP.coeff_jacobiCubeSum (le_refl (K + 1))]
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (K + 1))]
      · rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
        have hNn : ((N * K : ℕ) : ℤ) = N * (K : ℤ) := by push_cast; ring
        by_cases hT : m * (m + 1) / 2 = K
        · rw [if_pos (by rw [hT, hNn]), if_pos (le_of_eq hT), if_pos (by omega)]; push_cast; ring
        · rw [if_neg (by
            intro h; apply hT; rw [hNn] at h
            have := mul_left_cancel₀ hN0 h; exact_mod_cast this)]
          split_ifs with h1 h2
          · exfalso; omega
          · simp
          · simp
      · intro m hm
        rw [Function.mem_support] at hm
        split_ifs at hm with h
        · simp only [Finset.coe_range, Set.mem_Iio]
          have := MockTheta5.JTP.tri_ge m
          have h2 : ((m * (m + 1) / 2 : ℕ) : ℤ) = K := by
            have := mul_left_cancel₀ hN0 (h.trans (by push_cast; ring : ((N * K : ℕ) : ℤ) = N * (K : ℤ)))
            exact this
          omega
        · exact absurd rfl hm
    · refine finsum_eq_zero_of_forall_eq_zero fun m => if_neg ?_
      intro h; apply hd
      refine ⟨m * (m + 1) / 2, ?_⟩
      exact_mod_cast h.symm

/-- **`κ = −(q;q)_∞³`**: `θ(x)A(x,1) = −(q;q)_∞³` for every `x` with `−N < val x < N`, `x ≠ 1`. -/
theorem kappa_jacobi : hs (kF hN 0) = -(ιN hN MockTheta5.JTP.qfacInf) ^ 3 := by
  rw [hs_kF0, pairing, tri_shift, jN_eq, ← map_pow, MockTheta5.JTP.jacobi_cube_identity]

theorem kappa_eq_jacobi {a : ℤ} (hlo : -N < a + 0) (hhi : a + 0 < N) {cx : ℂ} (hx : cx ≠ 0)
    (h1 : mono a cx ≠ 1) : θ hN a cx * Ab hN hlo hhi cx 1 = -(ιN hN MockTheta5.JTP.qfacInf) ^ 3 := by
  rw [kappa_eq hN hlo hhi hx h1, kappa_jacobi]

end Jacobi

end ALz
