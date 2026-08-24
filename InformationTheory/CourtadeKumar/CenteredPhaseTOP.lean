import InformationTheory.CourtadeKumar.PerspectivePhases
import InformationTheory.CourtadeKumar.TopBitTheorem

/-! Application of corrected TOP to the centered-endpoint perspective phase. -/

open Set
open scoped NNReal

namespace CourtadeKumar

@[simp] lemma radialTriangleEntropy_centered (r : ℝ) :
    radialTriangleEntropy r (1 / 2) = binaryEntropyBits ((1 - r) / 2) := by
  unfold radialTriangleEntropy
  rw [show (1 - r) * (1 / 2) = (1 - r) / 2 by ring,
    show (1 + r) * (1 / 2) = 1 - (1 - r) / 2 by ring,
    binaryEntropyBits_one_sub]
  ring

@[simp] lemma radialTriangleChannelEntropy_centered
    (alpha : ℝ≥0) (r : ℝ) :
    radialTriangleChannelEntropy alpha r (1 / 2) =
      binaryEntropyBits ((1 - channelRho (alpha : ℝ) * r) / 2) := by
  unfold radialTriangleChannelEntropy
  rw [show (1 - channelRho (alpha : ℝ) * r) * (1 / 2) =
      (1 - channelRho (alpha : ℝ) * r) / 2 by ring,
    show (1 + channelRho (alpha : ℝ) * r) * (1 / 2) =
      1 - (1 - channelRho (alpha : ℝ) * r) / 2 by ring,
    binaryEntropyBits_one_sub]
  ring

/-- The manuscript's centered-endpoint scalar `(TOP)` is exactly the
already-proved corrected TOP theorem after setting `c = 2d/r` and converting
the probability midpoint to bias `X = 1-2M`. -/
theorem centeredEndpoint_top_bound_of_correctedTop
    {alpha M d r : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hc : 2 * d / r ∈ Ioo (0 : ℝ) 1)
    (hcap : 2 * d / r ≤ 2 * M)
    (hcontact :
      2 * d / r * binaryEntropyBits ((1 - r) / 2) =
        (bellmanEnvelope alpha (M - d) +
          bellmanEnvelope alpha (M + d)) / 2) :
    bellmanEnvelope alpha M ≤
      2 * d / r * radialTriangleChannelEntropy
        (⟨alpha, halpha.1.le⟩ : ℝ≥0) r (1 / 2) := by
  let alphaNN : ℝ≥0 := ⟨alpha, halpha.1.le⟩
  let c : ℝ := 2 * d / r
  let X : ℝ := 1 - 2 * M
  have hX : X ∈ Icc (0 : ℝ) (1 - c) := by
    dsimp [X, c]
    constructor
    · linarith [hM.2]
    · linarith [hcap]
  have hdomain : ∀ Y ∈ Icc (0 : ℝ) (1 - c),
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1 := by
    intro Y hY
    have hc0 : 0 < c := by simpa [c] using hc.1
    have hc1 : c < 1 := by simpa [c] using hc.2
    have hcr0 : 0 < c * r := mul_pos hc0 hr.1
    have hcr1 : c * r < c := mul_lt_of_lt_one_right hc0 hr.2
    constructor
    · constructor <;> linarith [hY.1, hY.2, hc.1]
    constructor
    · constructor <;> linarith [hY.1, hY.2, hcr1]
    · constructor <;> linarith [hY.1, hY.2, hcr0, hcr1, hc1]
  have hcontact' :
      c * binaryEntropyBits ((1 - r) / 2) =
        (bellmanEnvelope (alphaNN : ℝ) ((1 - X - c * r) / 2) +
          bellmanEnvelope (alphaNN : ℝ) ((1 - X + c * r) / 2)) / 2 := by
    dsimp [c, X, alphaNN]
    rw [show (1 - (1 - 2 * M) - 2 * d / r * r) / 2 = M - d by
      field_simp [hr.1.ne']; ring,
      show (1 - (1 - 2 * M) + 2 * d / r * r) / 2 = M + d by
        field_simp [hr.1.ne']; ring]
    exact hcontact
  have htop := correctedTopTarget_interior_bits_of_contact
    (alpha := alpha) (c := c) (r := r) (X := X)
    halpha hr hc hX hdomain hcontact'
  dsimp [X, c, alphaNN] at htop ⊢
  rw [show (1 - (1 - 2 * M)) / 2 = M by ring] at htop
  rw [radialTriangleChannelEntropy_centered]
  simpa using htop

end CourtadeKumar
