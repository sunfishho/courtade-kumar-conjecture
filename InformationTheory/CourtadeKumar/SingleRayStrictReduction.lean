import InformationTheory.CourtadeKumar.SingleRayGapDecomposition

/-! Reduction of LR to the genuinely strict contact regime `M < z`. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- In the strict regime, the scaling factor belongs to `(0,1)` and the
scaling reserve is nonnegative. -/
theorem singleRayNatScalingReserve_nonneg_of_mean_lt_contact
    {alpha : ℝ≥0} {M r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z) :
    0 ≤ singleRayNatScalingReserve (channelRho (alpha : ℝ))
      (M / z) r z := by
  have hrho : channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hc : M / z ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hM.1 hz.1, (div_lt_one hz.1).2 hMz⟩
  have hminus : (1 - r) * z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hr.2]) hz.1.le
    · calc
        (1 - r) * z ≤ 1 * z :=
          mul_le_mul_of_nonneg_right (by linarith [hr.1]) hz.1.le
        _ ≤ 1 := by linarith [hz.2]
  have hplus : (1 + r) * z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hr.1]) hz.1.le
    · apply le_of_lt
      calc
        (1 + r) * z < 2 * z :=
          mul_lt_mul_of_pos_right (by linarith [hr.2]) hz.1
        _ < 1 := by linarith [hz.2]
  exact singleRayNatScalingReserve_nonneg hrho hc hminus hplus

/-- The only unresolved reserve assertion after the equality case and the
ordering `M ≤ z` have been discharged. -/
def SingleRayStrictReserveTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M r z : ℝ),
    M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    r ∈ Ioo (0 : ℝ) 1 →
    z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    M < z →
    M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
    0 ≤ singleRayNatLocalGap (channelRho (alpha : ℝ)) M r +
      singleRayNatScalingReserve (channelRho (alpha : ℝ)) (M / z) r z

/-- The strict reserve theorem implies the complete scalar contact theorem;
the boundary `M = z` follows from the radial one-ray bound. -/
theorem singleRayScalarContact_of_strictReserve
    (alpha : ℝ≥0) (hstrict : SingleRayStrictReserveTheorem alpha) :
    SingleRayScalarContactTheorem alpha := by
  intro halpha M r z hM hr hz hcontact
  have hMz := singleRay_mean_le_contact halpha hM hr hz hcontact
  rcases hMz.eq_or_lt with hEq | hLt
  · subst z
    simpa [div_self hM.1.ne'] using
      (bellmanEnvelope_le_radialChannelEntropy halpha
        ⟨hr.1.le, hr.2.le⟩ ⟨hM.1.le, hM.2.le⟩)
  · have hreserve := hstrict M r z hM hr hz hLt hcontact
    have hdiv : 0 ≤
        (singleRayNatLocalGap (channelRho (alpha : ℝ)) M r +
          singleRayNatScalingReserve (channelRho (alpha : ℝ)) (M / z) r z) /
            Real.log 2 :=
      div_nonneg hreserve (Real.log_pos (by norm_num)).le
    rw [← singleRayBitGap_eq_natDecomposition hM.1 hz.1 hcontact] at hdiv
    exact sub_nonneg.mp hdiv

end CourtadeKumar
