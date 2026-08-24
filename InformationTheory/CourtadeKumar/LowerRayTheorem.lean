import InformationTheory.CourtadeKumar.LowerRayCurvature
import InformationTheory.CourtadeKumar.ScalarUnitConversion

/-! The bit-valued one-ray inequality obtained from lower-ray concavity. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Channel entropy in bits is the natural radial entropy divided by `log 2`. -/
theorem radialTriangleChannelEntropy_eq_nat
    (alpha : ℝ≥0) (r z : ℝ) :
    radialTriangleChannelEntropy alpha r z =
      radialNatEntropy (channelRho (alpha : ℝ)) r z / Real.log 2 := by
  unfold radialTriangleChannelEntropy radialNatEntropy binaryEntropyBits
  ring

/-- The natural lower-ray envelope is exactly the Bellman envelope after
conversion from nats to bits. -/
theorem lowerRayNatEnvelope_eq_bellman
    (alpha : ℝ) (m : ℝ) :
    lowerRayNatEnvelope (channelRho alpha) m =
      Real.log 2 * bellmanEnvelope alpha m := by
  unfold lowerRayNatEnvelope bellmanEnvelope
  rw [topS_channelRho, topEll_channelRho]
  unfold binaryEntropyBits
  field_simp [log_two_ne_zero]

/-- On the lower half interval, the Bellman envelope is bounded by channel
entropy on the extremal ray. -/
theorem bellmanEnvelope_le_oneRayChannelEntropy
    {alpha : ℝ≥0} {m : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hm : m ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    bellmanEnvelope (alpha : ℝ) m ≤
      radialTriangleChannelEntropy alpha 1 m := by
  have hrho : channelRho (alpha : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hgap := lowerRayGap_nonneg hrho hm
  have hnat : radialNatEntropy (channelRho (alpha : ℝ)) 1 m =
      Real.log 2 * radialTriangleChannelEntropy alpha 1 m := by
    rw [radialTriangleChannelEntropy_eq_nat]
    field_simp [log_two_ne_zero]
  rw [lowerRayGap, lowerRayNatEnvelope_eq_bellman, hnat] at hgap
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : 0 ≤ Real.log 2 *
      (radialTriangleChannelEntropy alpha 1 m -
        bellmanEnvelope (alpha : ℝ) m) := by
    linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlog).mp hscaled)

end CourtadeKumar
