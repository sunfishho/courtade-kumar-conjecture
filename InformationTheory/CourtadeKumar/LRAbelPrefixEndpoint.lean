import InformationTheory.CourtadeKumar.LRAbelPrefixIntegration

/-! Reduction of the Abel-prefix endpoint to the positive logarithmic tail. -/

namespace CourtadeKumar

noncomputable def lrAbelTailValue (N : ℕ) : ℝ :=
  Real.log 2 - lrAbelPhiPrefixAtOne N

lemma lrG_one : lrG 1 = 2 * Real.log 2 := by
  unfold lrG
  norm_num

lemma lrAbelPhiDivPrefix_one (N : ℕ) :
    lrAbelPhiDivPrefix N 1 = lrAbelPhiPrefixAtOne N := by
  unfold lrAbelPhiDivPrefix lrAbelPhiPrefixAtOne
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem lrAbelPrefixS_one
    {N : ℕ} (hN : 1 ≤ N) :
    lrAbelPrefixS N 1 =
      1 / (2 * (N : ℝ)) - 2 * lrAbelTailValue N := by
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  unfold lrAbelPrefixS lrAbelCStar lrAbelTailValue
  rw [lrG_one, lrAbelPhiDivPrefix_one]
  norm_num
  field_simp [hNReal.ne']
  ring

theorem lrAbelPrefixS_one_lower_of_tail
    {N : ℕ} (hN : 2 ≤ N)
    (htail : lrAbelTailValue N ≤
      (4 * (N : ℝ) + 1) /
        (8 * (N : ℝ) * (2 * (N : ℝ) + 1))) :
    1 / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) ≤
      lrAbelPrefixS N 1 := by
  have hNOne : 1 ≤ N := by omega
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNOne)
  have hodd : 0 < 2 * (N : ℝ) + 1 := by positivity
  rw [lrAbelPrefixS_one hNOne]
  apply le_trans ?_ (sub_le_sub_left (mul_le_mul_of_nonneg_left htail (by norm_num)) _)
  field_simp [hNReal.ne', hodd.ne']
  ring_nf
  norm_num

theorem lrAbelPrefixS_lower_of_tail
    {N : ℕ} (hN : 2 ≤ N)
    (htail : lrAbelTailValue N ≤
      (4 * (N : ℝ) + 1) /
        (8 * (N : ℝ) * (2 * (N : ℝ) + 1)))
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    v ^ (2 * N + 1) / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) ≤
      lrAbelPrefixS N v :=
  lrAbelPrefixS_lower_of_endpoint hN
    (lrAbelPrefixS_one_lower_of_tail hN htail) hv

end CourtadeKumar
