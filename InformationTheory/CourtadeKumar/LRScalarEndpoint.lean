import InformationTheory.CourtadeKumar.LRBernsteinP

/-! Elementary endpoint polynomial signs in the audited scalar `K` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrScalarEndpointQ (z : ℝ) : ℝ :=
  3 * z ^ 6 + 11 * z ^ 5 + 96 * z ^ 4 + 266 * z ^ 3 +
    255 * z ^ 2 + 187 * z + 46

noncomputable def lrScalarEndpointP (z : ℝ) : ℝ :=
  z ^ 10 + 6 * z ^ 9 + 39 * z ^ 8 + 60 * z ^ 7 -
    113 * z ^ 6 - 202 * z ^ 5 - 87 * z ^ 4 - 344 * z ^ 3 -
    368 * z ^ 2 - 384 * z - 80

theorem lrScalarEndpointQ_pos {z : ℝ} (hz : 0 ≤ z) :
    0 < lrScalarEndpointQ z := by
  unfold lrScalarEndpointQ
  have hz2 : 0 ≤ z ^ 2 := pow_nonneg hz _
  have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz _
  have hz4 : 0 ≤ z ^ 4 := pow_nonneg hz _
  have hz5 : 0 ≤ z ^ 5 := pow_nonneg hz _
  have hz6 : 0 ≤ z ^ 6 := pow_nonneg hz _
  nlinarith

theorem lrScalarEndpointP_neg
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    lrScalarEndpointP z < 0 := by
  have hz10 : z ^ 10 ≤ z ^ 7 :=
    pow_le_pow_of_le_one hz.1 hz.2 (by omega)
  have hz9 : z ^ 9 ≤ z ^ 7 :=
    pow_le_pow_of_le_one hz.1 hz.2 (by omega)
  have hz8 : z ^ 8 ≤ z ^ 7 :=
    pow_le_pow_of_le_one hz.1 hz.2 (by omega)
  have hz7 : z ^ 7 ≤ z ^ 6 :=
    pow_le_pow_of_le_one hz.1 hz.2 (by omega)
  have hz2 : 0 ≤ z ^ 2 := pow_nonneg hz.1 _
  have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz.1 _
  have hz4 : 0 ≤ z ^ 4 := pow_nonneg hz.1 _
  have hz5 : 0 ≤ z ^ 5 := pow_nonneg hz.1 _
  have hz6 : 0 ≤ z ^ 6 := pow_nonneg hz.1 _
  have hhead :
      z ^ 10 + 6 * z ^ 9 + 39 * z ^ 8 + 60 * z ^ 7 ≤
        106 * z ^ 6 := by
    nlinarith
  unfold lrScalarEndpointP
  nlinarith

/-- Sign of the cleared `ℓ`-derivative at the lower logarithm bound. -/
theorem lrScalarEndpoint_deriv_nonneg
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ -z ^ 2 * lrScalarEndpointQ z /
      (6 * (z - 1) * (z + 1) ^ 5 * (z + 2)) := by
  have hQ : 0 < lrScalarEndpointQ z := lrScalarEndpointQ_pos hz.1.le
  have hnum : -z ^ 2 * lrScalarEndpointQ z ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg z)) hQ.le
  have hden : 6 * (z - 1) * (z + 1) ^ 5 * (z + 2) < 0 := by
    have hm : z - 1 < 0 := sub_neg.mpr hz.2
    have hp1 : 0 < z + 1 := by nlinarith [hz.1]
    have hp2 : 0 < z + 2 := by nlinarith [hz.1]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by norm_num) hm)
        (pow_pos hp1 5)) hp2
  exact (div_nonneg_iff).2 (Or.inr ⟨hnum, hden.le⟩)

/-- Sign of the endpoint value after exact denominator clearing. -/
theorem lrScalarEndpoint_value_nonneg
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ -z ^ 2 * lrScalarEndpointP z /
      (18 * (z + 1) ^ 8 * (z + 2) ^ 2) := by
  have hP : lrScalarEndpointP z < 0 :=
    lrScalarEndpointP_neg ⟨hz.1.le, hz.2.le⟩
  have hnum : 0 ≤ -z ^ 2 * lrScalarEndpointP z := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (sq_nonneg z)) hP.le
  have hp1 : 0 < z + 1 := by nlinarith [hz.1]
  have hp2 : 0 < z + 2 := by nlinarith [hz.1]
  have hden : 0 < 18 * (z + 1) ^ 8 * (z + 2) ^ 2 := by positivity
  exact div_nonneg hnum hden.le

end CourtadeKumar
