import InformationTheory.CourtadeKumar.EnergyPositivity

/-! Positivity facts for the explicit Bellman envelope. -/

open Set
open scoped NNReal

namespace CourtadeKumar

lemma binaryEntropyBits_pos_of_mem_Ioo
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < binaryEntropyBits p := by
  unfold binaryEntropyBits
  exact div_pos (Real.binEntropy_pos hp.1 hp.2)
    (Real.log_pos (by norm_num))

lemma channelS_pos_of_alpha_interior
    {alpha : ℝ} (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    0 < channelS alpha := by
  have hrho : channelRho alpha ∈ Ioo (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  unfold channelS
  nlinarith [mul_pos (sub_pos.2 hrho.2) (by linarith [hrho.1] : 0 < 1 + channelRho alpha)]

theorem bellmanEnvelope_nonneg_of_mem_Icc
    {alpha p : ℝ}
    (halpha : alpha ∈ Icc (0 : ℝ) (1 / 2 : ℝ))
    (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ bellmanEnvelope alpha p := by
  have hrho : channelRho alpha ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hS : 0 ≤ channelS alpha := by
    unfold channelS
    nlinarith [mul_nonneg (sub_nonneg.2 hrho.2)
      (by linarith [hrho.1] : 0 ≤ 1 + channelRho alpha)]
  have hentropy : 0 ≤ binaryEntropyBits p :=
    div_nonneg (Real.binEntropy_nonneg hp.1 hp.2)
      (Real.log_pos (by norm_num)).le
  have hlambda : 0 ≤ bellmanLambda alpha :=
    bellmanLambda_nonneg halpha
  unfold bellmanEnvelope
  exact add_nonneg (mul_nonneg hS hentropy)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlambda) hp.1)
      (sub_nonneg.2 hp.2))

theorem bellmanEnvelope_pos_of_mem_Ioo
    {alpha p : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < bellmanEnvelope alpha p := by
  have hS : 0 < channelS alpha :=
    channelS_pos_of_alpha_interior halpha
  have hentropy : 0 < binaryEntropyBits p :=
    binaryEntropyBits_pos_of_mem_Ioo hp
  have hlambda : 0 ≤ bellmanLambda alpha :=
    bellmanLambda_nonneg ⟨halpha.1.le, halpha.2.le⟩
  unfold bellmanEnvelope
  exact add_pos_of_pos_of_nonneg (mul_pos hS hentropy)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlambda) hp.1.le)
      (sub_nonneg.2 hp.2.le))

/-- The average of two endpoint envelopes is positive as soon as the upper
endpoint is interior and the lower endpoint is admissible. -/
theorem centeredBellmanThreshold_pos
    {alpha M d : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hminus : M - d ∈ Icc (0 : ℝ) 1)
    (hplus : M + d ∈ Ioo (0 : ℝ) 1) :
    0 < (bellmanEnvelope alpha (M - d) +
      bellmanEnvelope alpha (M + d)) / 2 := by
  exact div_pos
    (add_pos_of_nonneg_of_pos
      (bellmanEnvelope_nonneg_of_mem_Icc
        ⟨halpha.1.le, halpha.2.le⟩ hminus)
      (bellmanEnvelope_pos_of_mem_Ioo halpha hplus))
    (by norm_num)

end CourtadeKumar
