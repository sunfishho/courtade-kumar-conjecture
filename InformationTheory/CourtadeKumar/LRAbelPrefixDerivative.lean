import InformationTheory.CourtadeKumar.LRAbelElementaryBounds

/-! The actual Abel prefix `S_N` and its exact derivative. -/

open Set Finset
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrAbelCStar : ℝ := 4 * Real.log 2 - 2

noncomputable def lrAbelPhiPrefixAtOne (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    1 / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))

/-- The quotient `Φ_N(v) / v`, written without a removable division at zero. -/
noncomputable def lrAbelPhiDivPrefix (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    v ^ (2 * k + 1) /
      (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))

/-- The same logarithmic prefix as `lrAbelLogPrefix`, in a form convenient
for differentiation. -/
noncomputable def lrAbelLogPrefixPow (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    v ^ (2 * (k + 1)) / (2 * ((k : ℝ) + 1))

lemma lrAbelLogPrefixPow_eq (N : ℕ) (v : ℝ) :
    lrAbelLogPrefixPow N v = lrAbelLogPrefix N v := by
  unfold lrAbelLogPrefixPow lrAbelLogPrefix
  apply Finset.sum_congr rfl
  intro k _
  have hpow : v ^ (2 * (k + 1)) = v ^ 2 * (v ^ 2) ^ k := by
    rw [pow_mul, pow_succ']
  rw [hpow]

noncomputable def lrAbelPhiDivDerivPrefix (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, v ^ (2 * k) / (2 * ((k : ℝ) + 1))

noncomputable def lrAbelLogDerivPrefix (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, v ^ (2 * k + 1)

theorem hasDerivAt_lrAbelPhiDivPrefix (N : ℕ) (v : ℝ) :
    HasDerivAt (lrAbelPhiDivPrefix N)
      (lrAbelPhiDivDerivPrefix N v) v := by
  unfold lrAbelPhiDivPrefix lrAbelPhiDivDerivPrefix
  apply HasDerivAt.fun_sum
  intro k _
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hodd : 0 < 2 * (k : ℝ) + 1 := by positivity
  convert (hasDerivAt_pow (2 * k + 1) v).div_const
    (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1)) using 1
  · rw [show 2 * k + 1 - 1 = 2 * k by omega]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hk1.ne', hodd.ne']
    ring

theorem hasDerivAt_lrAbelLogPrefixPow (N : ℕ) (v : ℝ) :
    HasDerivAt (lrAbelLogPrefixPow N)
      (lrAbelLogDerivPrefix N v) v := by
  unfold lrAbelLogPrefixPow lrAbelLogDerivPrefix
  apply HasDerivAt.fun_sum
  intro k _
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  convert (hasDerivAt_pow (2 * (k + 1)) v).div_const
    (2 * ((k : ℝ) + 1)) using 1
  · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hk1.ne']
    ring

/-- Equation (lr-Abel-prefix) from the audited manuscript. -/
noncomputable def lrAbelPrefixS (N : ℕ) (v : ℝ) : ℝ :=
  lrG v - lrAbelCStar - (1 + v) + lrAbelPhiPrefixAtOne N +
    lrAbelPhiDivPrefix N v +
    (1 - v) * (lrAbelLogPrefixPow (N - 1) v - Real.log (1 + v)) +
    (3 - v) * v ^ (2 * N) / (4 * (N : ℝ))

noncomputable def lrAbelPrefixSDeriv (N : ℕ) (v : ℝ) : ℝ :=
  -Real.log (1 + v) / v ^ 2 - 1 +
    lrAbelPhiDivDerivPrefix N v -
    (lrAbelLogPrefixPow (N - 1) v - Real.log (1 + v)) +
    (1 - v) * (lrAbelLogDerivPrefix (N - 1) v - 1 / (1 + v)) -
    v ^ (2 * N) / (4 * (N : ℝ)) +
    (3 - v) * ((2 * N : ℕ) : ℝ) * v ^ (2 * N - 1) /
      (4 * (N : ℝ))

theorem hasDerivAt_lrAbelPrefixS
    {N : ℕ} (hN : 1 ≤ N) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (lrAbelPrefixS N) (lrAbelPrefixSDeriv N v) v := by
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hplus : 1 + v ≠ 0 := by linarith
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y)) (1 / (1 + v)) v := by
    simpa [one_div] using
      (((hasDerivAt_const v 1).add (hasDerivAt_id v)).log hplus)
  have hlinear : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) v := by
    simpa using (hasDerivAt_const v 1).sub (hasDerivAt_id v)
  have hthree : HasDerivAt (fun y : ℝ ↦ 3 - y) (-1) v := by
    simpa using (hasDerivAt_const v 3).sub (hasDerivAt_id v)
  have hlogPrefix := hasDerivAt_lrAbelLogPrefixPow (N - 1) v
  have hproduct := hlinear.mul (hlogPrefix.sub hlog)
  have htail := (hthree.mul (hasDerivAt_pow (2 * N) v)).div_const (4 * (N : ℝ))
  have hmain :=
    ((((((hasDerivAt_lrG hv).sub_const lrAbelCStar).sub
      ((hasDerivAt_const v 1).add (hasDerivAt_id v))).add_const
        (lrAbelPhiPrefixAtOne N)).add
          (hasDerivAt_lrAbelPhiDivPrefix N v)).add hproduct).add htail
  convert hmain using 1
  simp only [Pi.sub_apply]
  unfold lrAbelPrefixSDeriv
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hv.ne', hplus, hNReal.ne']
  ring

end CourtadeKumar
