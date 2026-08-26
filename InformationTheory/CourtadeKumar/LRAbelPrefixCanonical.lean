import InformationTheory.CourtadeKumar.LRAbelPrefixDerivative

/-! Closed finite-sum form of the derivative of the audited Abel prefix. -/

open Set Finset
open scoped BigOperators

namespace CourtadeKumar

lemma lrAbelPhiDivDeriv_mul_sq (N : ℕ) (v : ℝ) :
    v ^ 2 * lrAbelPhiDivDerivPrefix N v = lrAbelLogPrefixPow N v := by
  unfold lrAbelPhiDivDerivPrefix lrAbelLogPrefixPow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hpow : v ^ 2 * v ^ (2 * k) = v ^ (2 * (k + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  field_simp [hk1.ne']
  exact hpow

lemma lrAbelLogPrefixPow_succ
    {N : ℕ} (hN : 1 ≤ N) (v : ℝ) :
    lrAbelLogPrefixPow N v =
      lrAbelLogPrefixPow (N - 1) v +
        v ^ (2 * N) / (2 * (N : ℝ)) := by
  have hpred : N = (N - 1) + 1 := by omega
  unfold lrAbelLogPrefixPow
  conv_lhs => rw [hpred, Finset.sum_range_succ]
  rw [show 2 * (N - 1 + 1) = 2 * N by omega]
  rw [show (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) by
    rw [Nat.cast_sub hN]
    norm_num]

lemma lrAbelLogDerivPrefix_eq_geom (N : ℕ) (v : ℝ) :
    lrAbelLogDerivPrefix N v = v * lrGeomPrefix N (v ^ 2) := by
  unfold lrAbelLogDerivPrefix lrGeomPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show v ^ (2 * k + 1) = v * (v ^ 2) ^ k by
    rw [pow_succ', pow_mul]]

lemma lrAbelLogDerivPrefix_closed
    (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    lrAbelLogDerivPrefix N v =
      v * (1 - v ^ (2 * N)) / (1 - v ^ 2) := by
  have hvSqLt : v ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - v ^ 2 := sub_pos.mpr hvSqLt
  rw [lrAbelLogDerivPrefix_eq_geom]
  have hgeom := one_sub_mul_lrGeomPrefix N (v ^ 2)
  have hpow : (v ^ 2) ^ N = v ^ (2 * N) := by rw [← pow_mul]
  rw [hpow] at hgeom
  apply (eq_div_iff hden.ne').2
  nlinarith [hgeom]

noncomputable def lrAbelPrefixSCanonical (N : ℕ) (v : ℝ) : ℝ :=
  Real.log (1 + v) * (v ^ 2 - 1) / v ^ 2 - 1 +
    (1 - v ^ 2) / v ^ 2 * lrAbelLogPrefixPow (N - 1) v +
    v ^ (2 * N - 2) / (2 * (N : ℝ)) +
    (1 - v) * lrAbelLogDerivPrefix (N - 1) v -
    (1 - v) / (1 + v) -
    v ^ (2 * N) / (4 * (N : ℝ)) +
    (3 - v) * v ^ (2 * N - 1) / 2

theorem lrAbelPrefixSDeriv_eq_canonical
    {N : ℕ} (hN : 1 ≤ N) {v : ℝ} (hv : 0 < v) :
    lrAbelPrefixSDeriv N v = lrAbelPrefixSCanonical N v := by
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hplus : 1 + v ≠ 0 := by linarith
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv.ne'
  have hphi := lrAbelPhiDivDeriv_mul_sq N v
  have hphiDiv : lrAbelPhiDivDerivPrefix N v =
      lrAbelLogPrefixPow N v / v ^ 2 := by
    apply (eq_div_iff hv2).2
    nlinarith [hphi]
  have hlogSucc := lrAbelLogPrefixPow_succ hN v
  have hpowEven : v ^ 2 * v ^ (2 * N - 2) = v ^ (2 * N) := by
    rw [← pow_add]
    congr 1
    omega
  unfold lrAbelPrefixSDeriv lrAbelPrefixSCanonical
  rw [hphiDiv, hlogSucc]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNReal.ne', hv.ne', hplus]
  rw [hpowEven]
  ring

end CourtadeKumar
