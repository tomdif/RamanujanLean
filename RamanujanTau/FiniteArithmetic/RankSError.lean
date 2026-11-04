import RamanujanTau.FiniteArithmetic.RankSLift

/-!
# The contracting error modulo `ℓ²`, with `s` observations

`Rank2Error` with `s` coefficient functionals `obs_a = Σ w_{ak} a_{k+1}` (`a < s`), each killing
`U` of the space `a₁ = … = a_s = 0` modulo `ℓ` (`hkill`). For `F` in the first even envelope,
`obs_a(Y F)` modulo `ℓ²` is `ℓ Σ cᵢ z_{ai}` (`obs_Y`). If `D F ≡ 0 (mod ℓ)`, the vector of
observations is multiplied by an `s × s` matrix `θ` (`divided_step`, in `RankSMain`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankS
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ s : ℕ} [hℓ : Fact ℓ.Prime]

/-- The observation `F ↦ Σ wₖ a_{k+1}(F)`. -/
noncomputable def obs (w : Fin (s + 2) → ℤ) : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  ∑ k : Fin (s + 2), ((w k : ℤ) : ℤ_[ℓ]) • PowerSeries.coeff (k.val + 1)

lemma obs_apply (w : Fin (s + 2) → ℤ) (F : PS ℓ) :
    obs w F = ∑ k : Fin (s + 2), ((w k : ℤ) : ℤ_[ℓ]) * coeff (k.val + 1) F := by
  simp [obs]

lemma obs_reduce (w : Fin (s + 2) → ℤ) (F : PS ℓ) : PadicInt.toZMod (obs w F) =
    ∑ k : Fin (s + 2), ((w k : ℤ) : ZMod ℓ) * coeff (k.val + 1) (PowerSeries.map (PadicInt.toZMod (p := ℓ)) F) := by
  rw [obs_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_intCast, coeff_map]

noncomputable def Yop : Module.End ℤ_[ℓ] (PS ℓ) := (Ulin ℓ).comp (Dlin ℓ)

/-- The mod-`ℓ²` data. -/
structure Data2 (ℓ s : ℕ) [Fact ℓ.Prime] extends Data ℓ s where
  hlow : ℓ * s < δ ℓ
  P : Fin (s + 2) → Poly ℓ
  hP : ∀ i, ModP.Iso (P i) (ℓ - 1)
  hev : ∀ i, ModP.ev ℤ_[ℓ] (P i) = PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (f i)
  hBinvB : ∀ i j, ∑ k, Binv i k * B k j = if i = j then 1 else 0
  w : Fin s → Fin (s + 2) → ℤ
  lam : Fin s → Fin s → ZMod ℓ
  /-- `ω_a U = Σ_t λ_{at} B_t`, with `ω_{aj} = Σₖ w_{ak} B k j`: `obs_a ∘ U` kills
  `a₁ = … = a_s = 0`. -/
  hkill : ∀ a i, ∑ j, (∑ k, ((w a k : ℤ) : ZMod ℓ) * B k j) * Umat j i =
    ∑ t, lam a t * B (Fin.castAdd 2 t) i
  z : Fin s → Fin (s + 2) → ℤ
  hz : ∀ a i, ∃ t : ℤ_[ℓ], obs (w a) (Yop (PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (f i) *
    Einv ℓ hℓ5)) = (ℓ : ℤ_[ℓ]) * ((z a i : ℤ_[ℓ]) + ℓ * t)
  θ : Fin s → Fin s → ZMod ℓ
  μ : Fin s → Fin (s + 2) → ZMod ℓ
  hθ : ∀ a i, ((z a i : ℤ) : ZMod ℓ) =
    ∑ b, θ a b * (∑ k, ((w b k : ℤ) : ZMod ℓ) * B k i) + ∑ j, μ a j * Dmat j i

namespace Data2
variable (D : Data2 ℓ s)

/-- `ω_{ai} = obs_a(fᵢ)` modulo `ℓ`. -/
def ω (a : Fin s) (i : Fin (s + 2)) : ZMod ℓ := ∑ k, ((D.w a k : ℤ) : ZMod ℓ) * D.B k i

noncomputable def fLift (i : Fin (s + 2)) : PS ℓ :=
  PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (D.f i) * Einv ℓ D.hℓ5

lemma obsBar_comb (a : Fin s) (e : Fin (s + 2) → ZMod ℓ) :
    ∑ k : Fin (s + 2), ((D.w a k : ℤ) : ZMod ℓ) * coeff (k.val + 1) (D.comb e) =
      ∑ i, D.ω a i * e i := by
  simp only [Data.coeff_comb, ω, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma comb_zero_iff (v : Fin (s + 2) → ZMod ℓ) (h : D.comb v = 0) : v = 0 := by
  have hl : ∀ k : Fin (s + 2), ∑ i, D.B k i * v i = 0 := fun k => by
    rw [← D.coeff_comb, h, map_zero]
  ext i
  have : v i = ∑ k, D.Binv i k * (∑ j, D.B k j * v j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ k, D.Binv i k * (D.B k j * v j) = (if i = j then 1 else 0) * v j := fun j => by
      rw [← D.hBinvB i j, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [this]; simp [hl]

lemma comb_inj {v v' : Fin (s + 2) → ZMod ℓ} (h : D.comb v = D.comb v') : v = v' := by
  have h0 : D.comb (v + (-1 : ZMod ℓ) • v') = 0 := by
    rw [D.comb_add, D.comb_smul, h, map_neg, map_one]; ring
  have := D.comb_zero_iff _ h0
  ext i; have hi := congrFun this i; simp at hi; linear_combination hi

variable (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

/-! ### Lifts and decomposition -/

theorem fraction_env (P : Poly ℓ) (hP : ModP.Iso P (ℓ - 1)) :
    Env ℓ D.hℓ5 1 (α ℓ) (ModP.ev ℤ_[ℓ] P * Einv ℓ D.hℓ5) := by
  intro N
  obtain ⟨c, hc, hc0, hDv⟩ := DBound.decompN D.hℓ5 N 1 P (by simpa using hP)
  refine ⟨2, c, hc, by simpa only [pow_one] using hDv, fun i => ?_⟩
  by_cases hi : i ≤ 1
  · have hα : α ℓ i ≤ 1 := by
      interval_cases i
      · exact (α_zero_le D.hℓ5)
      · unfold α
        rw [Int.ceil_le]
        have : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
        rw [div_le_iff₀ this]
        push_cast; linarith
    have he : (max 0 (α ℓ i - 1)).toNat = 0 := by omega
    rw [he]
    exact ⟨c i, by simp⟩
  · rw [hc0 i (by omega)]
    exact Dvd_zero _

lemma fLift_env (i : Fin (s + 2)) : Env ℓ D.hℓ5 1 (α ℓ) (D.fLift i) := by
  have h := D.fraction_env (D.P i) (D.hP i)
  rwa [D.hev i] at h

lemma fLift_cusp (i : Fin (s + 2)) : coeff 0 (D.fLift i) = 0 := by
  rw [fLift, coeff_zero_eq_constantCoeff, map_mul, ← coeff_zero_eq_constantCoeff, coeff_map,
    D.cusp i, map_zero, zero_mul]

lemma fLift_reduce (i : Fin (s + 2)) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (D.fLift i) = Ψ ℓ (D.f i) := by
  rw [fLift, map_mul, map_map_int, map_Einv, mul_one]

lemma map_sum_lift (c : Fin (s + 2) → ℤ_[ℓ]) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (∑ i, c i • D.fLift i) =
      D.comb (fun i => PadicInt.toZMod (c i)) := by
  simp only [map_sum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, D.fLift_reduce, Data.comb]

include h29 in
/-- Every cusp in the first even envelope has `s + 2` coordinates and a divided tail. -/
theorem decompose (F : PS ℓ) (hF : F ∈ envSub D.hℓ5 1 (α ℓ)) :
    ∃ c : Fin (s + 2) → ℤ_[ℓ], ∃ R : PS ℓ, Env ℓ D.hℓ5 2 (α ℓ) R ∧
      F = ∑ i, c i • D.fLift i + (ℓ : ℤ_[ℓ]) • R := by
  obtain ⟨a, ha, he⟩ := envelope_reduction D.hℓ5 (α ℓ)
    (fun i hi => (envelopes_ge_two (by omega : 13 ≤ ℓ) i hi).1) F hF.2
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [he, coeff_map, hF.1, map_zero]
  set e : Fin (s + 2) → ZMod ℓ := fun i => ∑ k : Fin (s + 2), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  have hae : Ψ ℓ a = D.comb e := D.cusp_eq a ha ha0
  let c : Fin (s + 2) → ℤ_[ℓ] := fun i => ((e i).val : ℕ)
  have hc : (fun i => PadicInt.toZMod (c i)) = e := funext fun i => lift_val (e i)
  obtain ⟨R, hR⟩ := PS_dvd_of_map (F - ∑ i, c i • D.fLift i) (by
    rw [map_sub, D.map_sum_lift, hc, ← hae, he, sub_self])
  have hm : F - ∑ i, c i • D.fLift i ∈ envSub D.hℓ5 1 (α ℓ) := by
    refine (envSub _ _ _).sub_mem hF (Submodule.sum_mem _ fun i _ => ?_)
    exact (envSub _ _ _).smul_mem _ ⟨D.fLift_cusp i, D.fLift_env i⟩
  refine ⟨c, R, ?_, ?_⟩
  · simpa using env_div D.hℓ5 1 (α ℓ) hm.2 hR
  · rw [← hR]; abel

/-! ### The tail and the observation -/

/-- `obs_a ∘ U` vanishes on `a₁ = … = a_s = 0`. -/
lemma obs_U_low (a : Fin s) (e : Fin (s + 2) → ZMod ℓ)
    (h : ∀ t : Fin s, ∑ i, D.B (Fin.castAdd 2 t) i * e i = 0) :
    ∑ i, D.ω a i * mv D.Umat e i = 0 := by
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, D.ω a i * (D.Umat i j * e j) =
      ∑ t, D.lam a t * (D.B (Fin.castAdd 2 t) j * e j) := fun j => by
    have hk := D.hkill a j
    calc ∑ i, D.ω a i * (D.Umat i j * e j) = (∑ i, D.ω a i * D.Umat i j) * e j := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ t, D.lam a t * D.B (Fin.castAdd 2 t) j) * e j := by rw [← hk]; rfl
      _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [← Finset.mul_sum, h t, mul_zero]

include h29 h24 in
/-- `obs_a ∘ Y` kills the divided tail modulo `ℓ`. -/
theorem tail_killed (a : Fin s) (R : PS ℓ) (hR : Env ℓ D.hℓ5 2 (α ℓ) R) :
    PadicInt.toZMod (obs (D.w a) (Yop R)) = 0 := by
  have hD := D_env D.hℓ5 (by omega) (bounds h29).2 2 le_rfl R hR
  obtain ⟨A, hA, he⟩ := envelope_reduction D.hℓ5 (β ℓ)
    (fun i hi => (envelopes_ge_two (by omega : 13 ≤ ℓ) i hi).2) _ hD
  have ha0 : coeff 0 (Ψ ℓ A) = 0 := by
    rw [he, coeff_map, D_coeff_low D.hlow _ 0 (by omega), map_zero]
  set e : Fin (s + 2) → ZMod ℓ := fun i => ∑ k : Fin (s + 2), D.Binv i k * coeff (k.val + 1) (Ψ ℓ A)
  have hae : Ψ ℓ A = D.comb e := D.cusp_eq A hA ha0
  have hl0 : ∀ t : Fin s, ∑ i, D.B (Fin.castAdd 2 t) i * e i = 0 := fun t => by
    rw [← D.coeff_comb e, ← hae, he, coeff_map]
    simp only [Fin.val_castAdd]
    rw [D_coeff_low D.hlow _ _ (by omega), map_zero]
  rw [obs_reduce]
  change ∑ k : Fin (s + 2), _ * coeff _ (PowerSeries.map _ (U ℓ (Dlin ℓ R))) = 0
  rw [map_U, ← he, hae, D.U_comb, D.obsBar_comb]
  exact D.obs_U_low a e hl0

lemma exists_of_toZMod {x : ℤ_[ℓ]} (h : PadicInt.toZMod x = 0) : ∃ s, x = (ℓ : ℤ_[ℓ]) * s := by
  have hm : x ∈ RingHom.ker (PadicInt.toZMod (p := ℓ)) := h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  have := (PadicInt.mem_nonunits.mp hm)
  rw [PadicInt.norm_lt_one_iff_dvd] at this
  obtain ⟨s, hs⟩ := this
  exact ⟨s, hs⟩

include h29 h24 in
/-- `obs_a(Y F) = ℓ (Σ cᵢ z_{ai} + ℓ w)`. -/
theorem obs_Y (a : Fin s) (F R : PS ℓ) (c : Fin (s + 2) → ℤ_[ℓ]) (hR : Env ℓ D.hℓ5 2 (α ℓ) R)
    (h : F = ∑ i, c i • D.fLift i + (ℓ : ℤ_[ℓ]) • R) :
    ∃ w' : ℤ_[ℓ], obs (D.w a) (Yop F) =
      (ℓ : ℤ_[ℓ]) * (∑ i, c i * (D.z a i : ℤ_[ℓ]) + ℓ * w') := by
  obtain ⟨σ, hs⟩ := exists_of_toZMod (D.tail_killed h29 h24 a R hR)
  choose t ht using D.hz a
  refine ⟨∑ i, c i * t i + σ, ?_⟩
  rw [h, map_add, map_sum, map_add, map_sum, map_smul, map_smul, smul_eq_mul, hs]
  simp only [map_smul, smul_eq_mul]
  have : ∀ i, c i * obs (D.w a) (Yop (D.fLift i)) =
      c i * ((ℓ : ℤ_[ℓ]) * ((D.z a i : ℤ_[ℓ]) + ℓ * t i)) :=
    fun i => by rw [← ht i]; rfl
  have key : ∑ i, c i * ((ℓ : ℤ_[ℓ]) * ((D.z a i : ℤ_[ℓ]) + ℓ * t i)) =
      ℓ * ∑ i, c i * (D.z a i : ℤ_[ℓ]) + ℓ * (ℓ * ∑ i, c i * t i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i, key]
  ring

end Data2

end RamanujanTau.FiniteArithmetic.RankS
