/-
# Weil's bound for the symmetric Kloosterman sums `S(h,h;c)`, uniformly in `h`

`norm_kloosterman_hh_le`: for every `δ > 0` there is `A` with
`|S(h,h;c)| ≤ A · h · c^{1/2+δ}` for all `h, c ≥ 1`.

Proof: `g = gcd(h,c)`, `c = g c'`, `h = g h'`.  `ψ_c(g x) = ψ_{c'}(x mod c')`, so
`S_c(h,h) = Σ_{u ∈ (ℤ/c)ˣ} F(π u)` with `π : (ℤ/c)ˣ → (ℤ/c')ˣ` (surjective, all fibres of the same
size `≤ g`), `F(v) = ψ_{c'}(h'(v + v⁻¹))`.  Hence `S_c(h,h) = #ker π · S_{c'}(h',h')` and
`S_{c'}(h',h') = S_{c'}(1,h'²)` (`kl_unit_eq`, `h'` a unit mod `c'`), which is Weil
(`Discharge.Kloosterman.kloostermanBound_half_unconditional`).
-/
import RamanujanTau.Discharge.Kloosterman

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Complex Finset RamanujanTau.TauBound

/-- `ψ_{g c'}(g x) = ψ_{c'}(x mod c')`. -/
lemma stdAddChar_mul_dvd (g c' : ℕ) [NeZero (g * c')] [NeZero c'] (x : ZMod (g * c')) :
    ZMod.stdAddChar ((g : ZMod (g * c')) * x) =
      ZMod.stdAddChar ((ZMod.castHom (dvd_mul_left c' g) (ZMod c')) x) := by
  have hg : g ≠ 0 := by
    intro h; exact NeZero.ne (g * c') (by simp [h])
  have hc' : (c' : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c'
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have e1 : (g : ZMod (g * c')) * x = (((g * x.val : ℕ) : ℤ) : ZMod (g * c')) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have e2 : (ZMod.castHom (dvd_mul_left c' g) (ZMod c')) x = (((x.val : ℕ) : ℤ) : ZMod c') := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]; push_cast; rfl
  rw [e1, e2, stdAddChar_intCast_eq_ee, stdAddChar_intCast_eq_ee]
  congr 1
  push_cast
  field_simp

/-- Fibre size of the reduction map on units is at most `g`. -/
lemma card_fiber_unitsMap_le (g c' : ℕ) [NeZero (g * c')] [NeZero c'] :
    #{u : (ZMod (g * c'))ˣ | ZMod.unitsMap (dvd_mul_left c' g) u = 1} ≤ g := by
  classical
  set π := ZMod.castHom (dvd_mul_left c' g) (ZMod c')
  -- injective map into the additive fibre over `1`
  have h1 : #{u : (ZMod (g * c'))ˣ | ZMod.unitsMap (dvd_mul_left c' g) u = 1} ≤
      #{x : ZMod (g * c') | π x = 1} := by
    refine Finset.card_le_card_of_injOn (fun u => (u : ZMod (g * c'))) (fun u hu => ?_)
      (fun u _ v _ huv => Units.ext huv)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
    have := congrArg (fun w : (ZMod c')ˣ => (w : ZMod c')) hu
    simpa [ZMod.unitsMap_val, π] using this
  -- all additive fibres have the same size, and there are `c'` of them
  have hfib : ∀ v : ZMod c', #{x : ZMod (g * c') | π x = v} = #{x : ZMod (g * c') | π x = 1} := by
    intro v
    have hsurj : Function.Surjective π := ZMod.ringHom_surjective π
    exact AddMonoidHom.card_fiber_eq_of_mem_range π.toAddMonoidHom (hsurj v) (hsurj 1)
  have htot : (Finset.univ : Finset (ZMod (g * c'))).card =
      ∑ v : ZMod c', #{x : ZMod (g * c') | π x = v} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ) (fun _ _ => mem_univ _)]
  simp_rw [hfib] at htot
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ, ZMod.card, ZMod.card, smul_eq_mul]
    at htot
  have hc'0 : 0 < c' := Nat.pos_of_ne_zero (NeZero.ne c')
  have : #{x : ZMod (g * c') | π x = 1} = g := by
    have h2 : c' * #{x : ZMod (g * c') | π x = 1} = c' * g := by rw [← htot]; ring
    exact Nat.eq_of_mul_eq_mul_left hc'0 h2
  omega

/-- `S_{gc'}(g h', g h') = (#ker) · S_{c'}(h', h')`, as a norm bound. -/
lemma norm_kl_scale_le (g c' : ℕ) [NeZero (g * c')] [NeZero c'] (h' : ℕ) :
    ‖kl (g * c') (((g * h' : ℕ)) : ZMod (g * c')) (((g * h' : ℕ)) : ZMod (g * c'))‖ ≤
      g * ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ := by
  classical
  set π := ZMod.unitsMap (dvd_mul_left c' g)
  set F : (ZMod c')ˣ → ℂ := fun v =>
    ZMod.stdAddChar ((h' : ZMod c') * (v : ZMod c') + (h' : ZMod c') * ((v⁻¹ : (ZMod c')ˣ) : ZMod c'))
  have hterm : ∀ u : (ZMod (g * c'))ˣ,
      ZMod.stdAddChar ((((g * h' : ℕ)) : ZMod (g * c')) * (u : ZMod (g * c')) +
        (((g * h' : ℕ)) : ZMod (g * c')) * ((u⁻¹ : (ZMod (g * c'))ˣ) : ZMod (g * c'))) =
        F (π u) := by
    intro u
    have e : (((g * h' : ℕ)) : ZMod (g * c')) * (u : ZMod (g * c')) +
        (((g * h' : ℕ)) : ZMod (g * c')) * ((u⁻¹ : (ZMod (g * c'))ˣ) : ZMod (g * c')) =
        (g : ZMod (g * c')) * (((h' : ℕ) : ZMod (g * c')) * u + ((h' : ℕ) : ZMod (g * c')) *
          ((u⁻¹ : (ZMod (g * c'))ˣ) : ZMod (g * c'))) := by push_cast; ring
    rw [e, stdAddChar_mul_dvd]
    simp only [F, map_add, map_mul, map_natCast, π, ZMod.unitsMap_val]
    rfl
  have hsum : kl (g * c') (((g * h' : ℕ)) : ZMod (g * c')) (((g * h' : ℕ)) : ZMod (g * c')) =
      ∑ u : (ZMod (g * c'))ˣ, F (π u) := by
    unfold kl; exact Finset.sum_congr rfl fun u _ => hterm u
  have hfw : ∑ u : (ZMod (g * c'))ˣ, F (π u) =
      ∑ v : (ZMod c')ˣ, (#{u : (ZMod (g * c'))ˣ | π u = v} : ℂ) * F v := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := π) (f := fun u => F (π u))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F v) (fun u hu => by
      rw [(Finset.mem_filter.mp hu).2])]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsurj := ZMod.unitsMap_surjective (m := g * c') (dvd_mul_left c' g)
  have hconst : ∀ v : (ZMod c')ˣ, #{u : (ZMod (g * c'))ˣ | π u = v} =
      #{u : (ZMod (g * c'))ˣ | π u = 1} := fun v =>
    MonoidHom.card_fiber_eq_of_mem_range π (hsurj v) (hsurj 1)
  simp_rw [hconst] at hfw
  rw [hsum, hfw, ← Finset.mul_sum, norm_mul]
  have hklF : ∑ v : (ZMod c')ˣ, F v = kl c' h' h' := rfl
  rw [hklF, Complex.norm_natCast]
  gcongr
  exact_mod_cast card_fiber_unitsMap_le g c'

/-- **Weil for `S(h,h;c)`**: `|S(h,h;c)| ≤ A h c^{1/2+δ}` for `h, c ≥ 1`. -/
theorem norm_kloosterman_hh_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h c : ℕ, 1 ≤ h → 1 ≤ c →
      ‖kloosterman h h c‖ ≤ A * h * (c : ℝ) ^ (1 / 2 + δ) := by
  obtain ⟨A₀, hA₀⟩ := Discharge.Kloosterman.kloostermanBound_half_unconditional δ hδ
  refine ⟨max A₀ 1, by positivity, fun h c hh hc => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd h c := ⟨_, rfl⟩
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hh
  obtain ⟨c', hc'⟩ : g ∣ c := hg ▸ Nat.gcd_dvd_right h c
  obtain ⟨h', hh'⟩ : g ∣ h := hg ▸ Nat.gcd_dvd_left h c
  have hc'0 : 0 < c' := by
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · rw [h0, mul_zero] at hc'; omega
    · exact h0
  have hcop : Nat.Coprime h' c' := by
    have := Nat.coprime_div_gcd_div_gcd (m := h) (n := c) (hg ▸ hg0)
    rwa [← hg, hh', hc', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hgh : (g : ℝ) ≤ h := by
    have : g ≤ h := Nat.le_of_dvd (by omega) ⟨h', hh'⟩
    exact_mod_cast this
  have hc'c : (c' : ℝ) ≤ c := by
    have : c' ≤ c := Nat.le_of_dvd (by omega) ⟨g, by rw [hc']; ring⟩
    exact_mod_cast this
  subst hc' hh'
  haveI : NeZero c' := ⟨by omega⟩
  haveI : NeZero (g * c') := ⟨by positivity⟩
  -- step 1: scale reduction
  have hS : ‖kloosterman ((g * h' : ℕ) : ℤ) ((g * h' : ℕ) : ℤ) (g * c')‖ ≤
      g * ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ := by
    rw [kloosterman_eq_kl]
    simpa using norm_kl_scale_le g c' h'
  -- step 2: unit reduction and Weil
  have hW : ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ ≤ max A₀ 1 * (c' : ℝ) ^ (1 / 2 + δ) := by
    set t : (ZMod c')ˣ := ZMod.unitOfCoprime h' hcop
    have ht : ((h' : ℕ) : ZMod c') = (t : ZMod c') := by simp [t]
    rw [ht, kl_unit_eq]
    have e2 : ((t : ZMod c') * (t : ZMod c')) = (((h' * h' : ℕ) : ℤ) : ZMod c') := by
      rw [← ht]; push_cast; ring
    rw [e2]
    have := hA₀ ((h' * h' : ℕ) : ℤ) c' (by omega)
    rw [kloosterman_eq_kl] at this
    simp only [Int.cast_one] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  push_cast at hS ⊢
  calc ‖kloosterman ((g : ℤ) * h') ((g : ℤ) * h') (g * c')‖
      ≤ g * ‖kl c' (h' : ZMod c') (h' : ZMod c')‖ := hS
    _ ≤ ((g : ℝ) * h') * (max A₀ 1 * ((g : ℝ) * c') ^ (1 / 2 + δ)) := by
        gcongr
        · push_cast at hgh; exact hgh
        · refine hW.trans ?_
          gcongr
          push_cast at hc'c; exact hc'c
    _ = max A₀ 1 * ((g : ℝ) * h') * ((g : ℝ) * c') ^ (1 / 2 + δ) := by ring

end RamanujanTau.SCSProof
