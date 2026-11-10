/-- `LphA`: `B = (1 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {(-1)}`. -/
def BphA : ECS where
  b11 := 1
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - (-1)) % 1 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((0 * m + 0 * n - (-1)) % 1 + (-1))) - 0 * (n - 0 * ((0 * m + 0 * n - (-1)) % 1 + (-1)))) / 1), ((1 * (n - 0 * ((0 * m + 0 * n - (-1)) % 1 + (-1))) - 0 * (m - 1 * ((0 * m + 0 * n - (-1)) % 1 + (-1)))) / 1), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LphA : QS (qmono 1 0 1 0 0 0 0) = (θ hm2 1 (-1) * θ hm2 1 (-1)) := by
  have h := (QS_orth 1 0 1 0 0 0 0 BphA hm2 hm2 (by norm_num [BphA])
    (by norm_num [BphA]) (by norm_num [BphA])).2
  simp only [BphA] at h
  rw [sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm2 1 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-1) 1 (e := (-1)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LphB`: `B = (1 1; -1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1)}`. -/
def BphB : ECS where
  b11 := 1
  b12 := 1
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 2 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 1 * n - (-2)) % 2 + (-2))) - 1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), ((1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 2 + (-2))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 2 + (-2)))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LphB : QS (qmono 1 0 1 0 0 0 0) = (θ hm4 2 (-1) * θ hm4 2 (-1)) + (mono 1 1 * (θ hm4 0 (-1) * θ hm4 0 (-1))) := by
  have h := (QS_orth 1 0 1 0 0 0 0 BphB hm4 hm4 (by norm_num [BphB])
    (by norm_num [BphB]) (by norm_num [BphB])).2
  simp only [BphB] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_sh hm4 2 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
