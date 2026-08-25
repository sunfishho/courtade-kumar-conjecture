import InformationTheory.CourtadeKumar.PerspectivePhases
import InformationTheory.CourtadeKumar.LowerRayTheorem
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
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
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

/-- Perspective feasibility `d/M ≤ r` automatically supplies the TOP
weight cap `c = 2d/r ≤ 2M < 1`. -/
theorem centeredEndpoint_top_bound_of_phaseContact
    {alpha M d r : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d) (hshape : d / M ≤ r)
    (hcontact :
      2 * d / r * binaryEntropyBits ((1 - r) / 2) =
        (bellmanEnvelope alpha (M - d) +
          bellmanEnvelope alpha (M + d)) / 2) :
    bellmanEnvelope alpha M ≤
      2 * d / r * radialTriangleChannelEntropy
        (⟨alpha, halpha.1.le⟩ : ℝ≥0) r (1 / 2) := by
  have hdMr : d ≤ M * r := by
    have := (div_le_iff₀ hM.1).mp hshape
    nlinarith
  have hcap : 2 * d / r ≤ 2 * M := by
    rw [div_le_iff₀ hr.1]
    nlinarith
  have hc : 2 * d / r ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos (by norm_num) hd) hr.1
    · have hcle : 2 * d / r ≤ 1 := hcap.trans (by linarith [hM.2])
      apply lt_of_le_of_ne hcle
      intro hceq
      let p : ℝ := (1 - r) / 2
      have hdEq : d = r / 2 := by
        rw [div_eq_iff hr.1.ne'] at hceq
        linarith
      have hMlower : 1 / 2 ≤ M := by
        have hdMr : d ≤ M * r := by
          simpa [mul_comm] using (div_le_iff₀ hM.1).mp hshape
        rw [hdEq] at hdMr
        nlinarith [hr.1]
      have hMhalf : M = 1 / 2 := le_antisymm hM.2 hMlower
      have hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := by
        dsimp [p]
        constructor <;> linarith [hr.1, hr.2]
      have hstrict := bellmanEnvelope_lt_binaryEntropy
        (alpha := (⟨alpha, halpha.1.le⟩ : ℝ≥0)) halpha hp
      have hminus : M - d = p := by
        dsimp [p]
        rw [hMhalf, hdEq]
        ring
      have hplus : M + d = 1 - p := by
        dsimp [p]
        rw [hMhalf, hdEq]
        ring
      have heq : binaryEntropyBits p = bellmanEnvelope alpha p := by
        rw [hceq, hminus, hplus, bellmanEnvelope_one_sub] at hcontact
        simpa using hcontact
      exact hstrict.ne heq.symm
  exact centeredEndpoint_top_bound_of_correctedTop
    halpha hr hM hc hcap hcontact

/-- The centered-phase geometry before its scalar objective bound is
inserted.  All fields here belong to the perspective/contact classification;
the corrected TOP theorem supplies the missing `top_bound`. -/
structure CenteredEndpointGeometryData
    (alpha : ℝ≥0) (M d E0 : ℝ) where
  theta : ℝ
  c : ℝ → ℝ
  rstar : ℝ
  alpha_interior : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)
  mean_lowerHalf : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)
  displacement_pos : 0 < d
  rstar_interior : rstar ∈ Ioo (0 : ℝ) 1
  phase_shape : d / M ≤ rstar
  theta_nonneg : 0 ≤ theta
  contactProfile : RadialContactProfile alpha theta c
  chordSupport : RadialChordSupport c rstar
  centered_contact : c rstar =
    2 * radialTriangleDifference alpha theta rstar (1 / 2)
  entropy_contact : E0 =
    2 * d / rstar * radialTriangleEntropy rstar (1 / 2)
  threshold_eq : E0 =
    (bellmanEnvelope (alpha : ℝ) (M - d) +
      bellmanEnvelope (alpha : ℝ) (M + d)) / 2

/-- The corrected TOP theorem upgrades centered phase geometry to the full
phase data required by weak duality. -/
noncomputable def CenteredEndpointGeometryData.toPhaseData
    {alpha : ℝ≥0} {M d E0 : ℝ}
    (h : CenteredEndpointGeometryData alpha M d E0) :
    CenteredEndpointPhaseData alpha M d E0 where
  theta := h.theta
  c := h.c
  rstar := h.rstar
  theta_nonneg := h.theta_nonneg
  contactProfile := h.contactProfile
  chordSupport := h.chordSupport
  centered_contact := h.centered_contact
  entropy_contact := h.entropy_contact
  top_bound := by
    have hcontact :
        2 * d / h.rstar * binaryEntropyBits ((1 - h.rstar) / 2) =
          (bellmanEnvelope (alpha : ℝ) (M - d) +
            bellmanEnvelope (alpha : ℝ) (M + d)) / 2 := by
      calc
        2 * d / h.rstar * binaryEntropyBits ((1 - h.rstar) / 2) =
            2 * d / h.rstar * radialTriangleEntropy h.rstar (1 / 2) := by
              rw [radialTriangleEntropy_centered]
        _ = E0 := h.entropy_contact.symm
        _ = (bellmanEnvelope (alpha : ℝ) (M - d) +
            bellmanEnvelope (alpha : ℝ) (M + d)) / 2 := h.threshold_eq
    exact centeredEndpoint_top_bound_of_phaseContact
      h.alpha_interior h.rstar_interior h.mean_lowerHalf
      h.displacement_pos h.phase_shape hcontact

end CourtadeKumar
