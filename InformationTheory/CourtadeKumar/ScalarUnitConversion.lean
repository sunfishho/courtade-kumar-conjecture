import InformationTheory.CourtadeKumar.FixedWeightReduction

/-! Exact conversion between natural-unit TOP scalars and bit-valued Bellman scalars. -/

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma log_two_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num))

/-- Natural binary entropy in bias coordinates equals `log 2` times binary
entropy in bits. -/
theorem topJ_unitConversion (p : ℝ) :
    topJ (1 - 2 * p) = Real.log 2 * binaryEntropyBits p := by
  unfold topJ topPhi binaryEntropyBits
  rw [show (1 - (1 - 2 * p)) / 2 = p by ring]
  field_simp [log_two_ne_zero]
  ring

lemma topS_channelRho (alpha : ℝ) :
    topS (channelRho alpha) = channelS alpha := by
  rfl

/-- The natural-unit and bit-unit equal-multiplier coefficients agree after
multiplication by `log 2`. -/
theorem topEll_channelRho (alpha : ℝ) :
    topEll (channelRho alpha) = Real.log 2 * bellmanLambda alpha := by
  unfold topEll topR topPhi bellmanLambda binaryEntropyBits
  unfold channelS channelRho
  rw [show (1 - (1 - 2 * alpha)) / 2 = alpha by ring]
  field_simp [log_two_ne_zero]
  ring

/-- Exact unit conversion between the natural TOP envelope and the bit-valued
Bellman envelope. -/
theorem topEnvelope_unitConversion (alpha p : ℝ) :
    topEnvelope (channelRho alpha) (1 - 2 * p) =
      Real.log 2 * bellmanEnvelope alpha p := by
  unfold topEnvelope bellmanEnvelope
  rw [topS_channelRho, topJ_unitConversion, topEll_channelRho]
  ring

end CourtadeKumar
