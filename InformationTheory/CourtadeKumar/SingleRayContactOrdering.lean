import InformationTheory.CourtadeKumar.SingleRayScalarReduction
import InformationTheory.CourtadeKumar.EnvelopeFormula
import InformationTheory.CourtadeKumar.RadialEntropyRatio

/-! Elementary ordering consequences of a single-ray entropy contact. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Averaging the two channel outputs cannot exceed entropy at their mean. -/
theorem radialTriangleChannelEntropy_le_binaryEntropy
    {alpha : ℝ≥0} {m : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hm : m ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    radialTriangleChannelEntropy alpha 1 m ≤ binaryEntropyBits m := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hminus : (1 - rho) * m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hrho.2]) hm.1
    · calc
        (1 - rho) * m ≤ 1 * m :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.1]) hm.1
        _ ≤ 1 := by linarith [hm.2]
  have hplus : (1 + rho) * m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hrho.1]) hm.1
    · calc
        (1 + rho) * m ≤ 2 * m :=
          mul_le_mul_of_nonneg_right (by linarith [hrho.2]) hm.1
        _ ≤ 1 := by linarith [hm.2]
  have hconcave := binaryEntropyBits_concaveOn.2 hminus hplus
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconcave
  have hmean : (1 / 2 : ℝ) * ((1 - rho) * m) +
      (1 / 2 : ℝ) * ((1 + rho) * m) = m := by ring
  rw [hmean] at hconcave
  unfold radialTriangleChannelEntropy
  simp only [mul_one]
  dsimp [rho] at hconcave
  nlinarith [hconcave]

/-- On the physical lower half, the Bellman envelope stays below input
entropy.  This follows by sandwiching it through the extremal channel ray. -/
theorem bellmanEnvelope_le_binaryEntropy
    {alpha : ℝ≥0} {m : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hm : m ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    bellmanEnvelope (alpha : ℝ) m ≤ binaryEntropyBits m :=
  (bellmanEnvelope_le_oneRayChannelEntropy halpha hm).trans
    (radialTriangleChannelEntropy_le_binaryEntropy halpha hm)

lemma singleRay_endpoint_mem_Icc
    {M r : ℝ} (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    M * (1 - r) ∈ Icc (0 : ℝ) (1 / 2 : ℝ) ∧
      M * (1 + r) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · constructor
    · exact mul_nonneg hM.1.le (by linarith [hr.2])
    · calc
        M * (1 - r) ≤ M * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hr.1]) hM.1.le
        _ ≤ 1 / 2 := by linarith [hM.2]
  · constructor
    · exact mul_nonneg hM.1.le (by linarith [hr.1])
    · apply le_of_lt
      calc
        M * (1 + r) ≤ (1 / 2) * (1 + r) :=
          mul_le_mul_of_nonneg_right hM.2 (by linarith [hr.1])
        _ < (1 / 2) * 2 :=
          mul_lt_mul_of_pos_left (by linarith [hr.2]) (by norm_num)
        _ = 1 := by ring

/-- A canonical entropy contact never lies below the aggregate mass. -/
theorem singleRay_mean_le_contact
    {alpha : ℝ≥0} {M r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hcontact : M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2) :
    M ≤ z := by
  obtain ⟨hminus, hplus⟩ := singleRay_endpoint_mem_Icc hM hr
  have hBminus := bellmanEnvelope_le_binaryEntropy halpha hminus
  have hBplus : bellmanEnvelope (alpha : ℝ) (M * (1 + r)) ≤
      binaryEntropyBits (M * (1 + r)) := by
    by_cases hp : M * (1 + r) ≤ 1 / 2
    · exact bellmanEnvelope_le_binaryEntropy halpha ⟨hplus.1, hp⟩
    · have hsym : 1 - M * (1 + r) ∈ Icc (0 : ℝ) (1 / 2 : ℝ) := by
        constructor
        · linarith [hplus.2]
        · linarith
      rw [← binaryEntropyBits_one_sub (M * (1 + r))]
      have henvsym : bellmanEnvelope (alpha : ℝ) (M * (1 + r)) =
          bellmanEnvelope (alpha : ℝ) (1 - M * (1 + r)) := by
        unfold bellmanEnvelope
        rw [binaryEntropyBits_one_sub]
        ring
      rw [henvsym]
      exact bellmanEnvelope_le_binaryEntropy halpha hsym
  have havg :
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 ≤
      radialTriangleEntropy r M := by
    unfold radialTriangleEntropy
    simpa [mul_comm] using
      (div_le_div_of_nonneg_right (add_le_add hBminus hBplus) (by norm_num))
  have hratio : radialEntropyRatio r z ≤ radialEntropyRatio r M := by
    rw [radialEntropyRatio, radialEntropyRatio]
    rw [← hcontact] at havg
    have hMz : 0 < M / z := div_pos hM.1 hz.1
    have hMne : M ≠ 0 := hM.1.ne'
    have hzNe : z ≠ 0 := hz.1.ne'
    calc
      radialTriangleEntropy r z / z =
          (M / z * radialTriangleEntropy r z) / M := by
            field_simp [hMne, hzNe]
      _ ≤ radialTriangleEntropy r M / M :=
        div_le_div_of_nonneg_right havg hM.1.le
  by_contra hnot
  have hzM : z < M := lt_of_not_ge hnot
  have hstrict := strictAntiOn_radialEntropyRatio hr
    ⟨hz.1, hz.2.trans (by
      rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
      calc
        (1 / 2) * (1 + r) < (1 / 2) * 2 :=
          mul_lt_mul_of_pos_left (by linarith [hr.2]) (by norm_num)
        _ = 1 := by ring)⟩
    ⟨hM.1, by
      rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
      calc
        M * (1 + r) ≤ (1 / 2) * (1 + r) :=
          mul_le_mul_of_nonneg_right hM.2 (by linarith [hr.1])
        _ < (1 / 2) * 2 :=
          mul_lt_mul_of_pos_left (by linarith [hr.2]) (by norm_num)
        _ = 1 := by ring⟩ hzM
  linarith

end CourtadeKumar
