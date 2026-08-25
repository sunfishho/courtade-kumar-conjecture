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

/-- For an interior channel and positive lower-half mass, the extremal-ray
channel entropy is strictly below the input entropy. -/
theorem radialTriangleChannelEntropy_lt_binaryEntropy
    {alpha : ℝ≥0} {m : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hm : m ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    radialTriangleChannelEntropy alpha 1 m < binaryEntropyBits m := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hminus : (1 - rho) * m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hrho.2]) hm.1.le
    · calc
        (1 - rho) * m ≤ 1 * m :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.1]) hm.1.le
        _ ≤ 1 := by
          simpa using hm.2.trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hplus : (1 + rho) * m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hrho.1]) hm.1.le
    · calc
        (1 + rho) * m ≤ 2 * m :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.2]) hm.1.le
        _ ≤ 1 := by linarith [hm.2]
  have hne : (1 - rho) * m ≠ (1 + rho) * m := by
    nlinarith [mul_pos hrho.1 hm.1]
  have hstrict := Real.strictConcave_binEntropy.2
    hminus hplus hne
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hstrict
  have hmean : (1 / 2 : ℝ) * ((1 - rho) * m) +
      (1 / 2 : ℝ) * ((1 + rho) * m) = m := by ring
  rw [hmean] at hstrict
  dsimp [rho] at hstrict
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold radialTriangleChannelEntropy binaryEntropyBits
  simp only [mul_one]
  calc
    (Real.binEntropy ((1 - channelRho (alpha : ℝ)) * m) / Real.log 2 +
        Real.binEntropy ((1 + channelRho (alpha : ℝ)) * m) / Real.log 2) / 2 =
        ((Real.binEntropy ((1 - channelRho (alpha : ℝ)) * m) +
          Real.binEntropy ((1 + channelRho (alpha : ℝ)) * m)) / 2) /
            Real.log 2 := by ring
    _ < Real.binEntropy m / Real.log 2 :=
      (div_lt_div_iff_of_pos_right hlog).2 (by nlinarith [hstrict])

/-- The Bellman envelope is strictly below entropy away from the hard
endpoints for an interior BSC. -/
theorem bellmanEnvelope_lt_binaryEntropy
    {alpha : ℝ≥0} {m : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hm : m ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    bellmanEnvelope (alpha : ℝ) m < binaryEntropyBits m :=
  (bellmanEnvelope_le_oneRayChannelEntropy halpha
      ⟨hm.1.le, hm.2⟩).trans_lt
    (radialTriangleChannelEntropy_lt_binaryEntropy halpha hm)

end CourtadeKumar
