import InformationTheory.CourtadeKumar.TopTheorem

/-! Bit-valued Bellman-coordinate form of the corrected interior TOP theorem. -/

open Set

namespace CourtadeKumar

/-- Exact conversion of an interior natural-unit TOP theorem to the
bit-valued Bellman normalization. -/
theorem correctedTopTarget_interior_bits
    {alpha c r X : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) (1 - c))
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) (1 - c),
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual (channelRho alpha) c r X = 0) :
    bellmanEnvelope alpha ((1 - X) / 2) ≤
      c * binaryEntropyBits ((1 - channelRho alpha * r) / 2) := by
  have hrho : channelRho alpha ∈ Ioo (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have htop := correctedTopTarget_interior hrho hr hc hX hdomain hcontact
  have hEnv : topEnvelope (channelRho alpha) X =
      Real.log 2 * bellmanEnvelope alpha ((1 - X) / 2) := by
    convert topEnvelope_unitConversion alpha ((1 - X) / 2) using 1 <;> ring
  have hJ : topJ (channelRho alpha * r) =
      Real.log 2 * binaryEntropyBits ((1 - channelRho alpha * r) / 2) := by
    convert topJ_unitConversion ((1 - channelRho alpha * r) / 2) using 1 <;> ring
  rw [hEnv, hJ] at htop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The same result with the contact hypothesis already expressed in
bit-valued probability coordinates. -/
theorem correctedTopTarget_interior_bits_of_contact
    {alpha c r X : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) (1 - c))
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) (1 - c),
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact :
      c * binaryEntropyBits ((1 - r) / 2) =
        (bellmanEnvelope alpha ((1 - X - c * r) / 2) +
          bellmanEnvelope alpha ((1 - X + c * r) / 2)) / 2) :
    bellmanEnvelope alpha ((1 - X) / 2) ≤
      c * binaryEntropyBits ((1 - channelRho alpha * r) / 2) := by
  have hJ : topJ r = Real.log 2 * binaryEntropyBits ((1 - r) / 2) := by
    convert topJ_unitConversion ((1 - r) / 2) using 1 <;> ring
  have hplus : topEnvelope (channelRho alpha) (X + c * r) =
      Real.log 2 * bellmanEnvelope alpha ((1 - X - c * r) / 2) := by
    convert topEnvelope_unitConversion alpha ((1 - X - c * r) / 2) using 1 <;> ring
  have hminus : topEnvelope (channelRho alpha) (X - c * r) =
      Real.log 2 * bellmanEnvelope alpha ((1 - X + c * r) / 2) := by
    convert topEnvelope_unitConversion alpha ((1 - X + c * r) / 2) using 1 <;> ring
  have hcontactNat : topContactResidual (channelRho alpha) c r X = 0 := by
    unfold topContactResidual
    rw [hJ, hplus, hminus]
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  exact correctedTopTarget_interior_bits halpha hr hc hX hdomain hcontactNat

end CourtadeKumar
