import InformationTheory.CourtadeKumar.ArtanhDerivative

/-! Monotonicity of the entropy drop and the corrected TOP reserve transition. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

/-- Derivative of the symmetric entropy drop with respect to its center. -/
noncomputable def topEntropyDropCenterSlope (Y b : ℝ) : ℝ :=
  (Real.artanh (Y + b) + Real.artanh (Y - b)) / 2 - Real.artanh Y

noncomputable def topEntropyDropWidthDerivative (Y b : ℝ) : ℝ :=
  (1 / (1 - (Y + b) ^ 2) - 1 / (1 - (Y - b) ^ 2)) / 2

lemma hasDerivAt_topEntropyDropCenterSlope_width
    {Y b : ℝ}
    (hplus : Y + b ∈ Ioo (-1 : ℝ) 1)
    (hminus : Y - b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (topEntropyDropCenterSlope Y)
      (topEntropyDropWidthDerivative Y b) b := by
  have hargPlus : HasDerivAt (fun t : ℝ ↦ Y + t) 1 b :=
    (hasDerivAt_id b).const_add Y
  have hargMinus : HasDerivAt (fun t : ℝ ↦ Y - t) (-1) b :=
    (hasDerivAt_id b).const_sub Y
  have hp := (hasDerivAt_artanh hplus).comp b hargPlus
  have hm := (hasDerivAt_artanh hminus).comp b hargMinus
  have havg := (hp.add hm).div_const 2
  have h := havg.sub_const (Real.artanh Y)
  change HasDerivAt
    (fun t : ℝ ↦ (Real.artanh (Y + t) + Real.artanh (Y - t)) / 2 -
      Real.artanh Y) (topEntropyDropWidthDerivative Y b) b
  convert h using 1
  unfold topEntropyDropWidthDerivative
  ring

lemma topEntropyDropWidthDerivative_nonneg
    {Y b : ℝ} (hY : 0 ≤ Y) (hb : 0 ≤ b)
    (hplus : Y + b ∈ Ioo (-1 : ℝ) 1)
    (hminus : Y - b ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ topEntropyDropWidthDerivative Y b := by
  have hA : 0 < 1 - (Y + b) ^ 2 := by
    have hsquare := sq_lt_sq' hplus.1 hplus.2
    nlinarith
  have hB : 0 < 1 - (Y - b) ^ 2 := by
    have hsquare := sq_lt_sq' hminus.1 hminus.2
    nlinarith
  have hAB : 1 - (Y + b) ^ 2 ≤ 1 - (Y - b) ^ 2 := by
    nlinarith [mul_nonneg hY hb]
  have hinv := one_div_le_one_div_of_le hA hAB
  unfold topEntropyDropWidthDerivative
  linarith

/-- The center slope is nonnegative for nonnegative center and half-width. -/
theorem topEntropyDropCenterSlope_nonneg
    {Y b : ℝ} (hY : 0 ≤ Y) (hb : 0 ≤ b)
    (hplus : Y + b ∈ Ioo (-1 : ℝ) 1)
    (hminus : Y - b ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ topEntropyDropCenterSlope Y b := by
  have hdomain : ∀ t ∈ Icc (0 : ℝ) b,
      Y + t ∈ Ioo (-1 : ℝ) 1 ∧ Y - t ∈ Ioo (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨ht0, htb⟩
    constructor
    · constructor <;> linarith [hplus.1, hplus.2]
    · constructor
      · linarith [hminus.1]
      · linarith [hplus.2]
  have hmono : MonotoneOn (topEntropyDropCenterSlope Y) (Icc (0 : ℝ) b) := by
    let derivW : ℝ → ℝ := topEntropyDropWidthDerivative Y
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b)
    · intro t ht
      exact (hasDerivAt_topEntropyDropCenterSlope_width (hdomain t ht).1
        (hdomain t ht).2).continuousAt.continuousWithinAt
    · intro t ht
      have htin : t ∈ Icc (0 : ℝ) b := interior_subset ht
      exact (hasDerivAt_topEntropyDropCenterSlope_width (hdomain t htin).1
        (hdomain t htin).2).hasDerivWithinAt
    · intro t ht
      have htin : t ∈ Icc (0 : ℝ) b := interior_subset ht
      exact topEntropyDropWidthDerivative_nonneg hY htin.1
        (hdomain t htin).1 (hdomain t htin).2
  have h0b := hmono (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb⟩)
    (show b ∈ Icc (0 : ℝ) b from ⟨hb, le_rfl⟩) hb
  simpa [topEntropyDropCenterSlope] using h0b

lemma hasDerivAt_topEntropyDrop_center
    {Y b : ℝ}
    (hcenter : Y ∈ Ioo (-1 : ℝ) 1)
    (hplus : Y + b ∈ Ioo (-1 : ℝ) 1)
    (hminus : Y - b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun Z ↦ topEntropyDrop Z b)
      (topEntropyDropCenterSlope Y b) Y := by
  have hargPlus : HasDerivAt (fun Z : ℝ ↦ Z + b) 1 Y :=
    (hasDerivAt_id Y).add_const b
  have hargMinus : HasDerivAt (fun Z : ℝ ↦ Z - b) 1 Y :=
    (hasDerivAt_id Y).sub_const b
  have hc := hasDerivAt_topJ hcenter
  have hp := (hasDerivAt_topJ hplus).comp Y hargPlus
  have hm := (hasDerivAt_topJ hminus).comp Y hargMinus
  have h := hc.sub ((hp.add hm).div_const 2)
  change HasDerivAt
    (fun Z : ℝ ↦ topJ Z - (topJ (Z + b) + topJ (Z - b)) / 2)
      (topEntropyDropCenterSlope Y b) Y
  convert h using 1
  unfold topEntropyDropCenterSlope
  ring

/-- For fixed half-width, the symmetric entropy drop increases with its
nonnegative center. -/
theorem topEntropyDrop_monotoneOn_nonneg
    {b U : ℝ} (hb : 0 ≤ b)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + b ∈ Ioo (-1 : ℝ) 1 ∧ Y - b ∈ Ioo (-1 : ℝ) 1) :
    MonotoneOn (fun Y ↦ topEntropyDrop Y b) (Icc (0 : ℝ) U) := by
  let slope : ℝ → ℝ := fun Y ↦ topEntropyDropCenterSlope Y b
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 U)
  · intro Y hY
    exact (hasDerivAt_topEntropyDrop_center (hdomain Y hY).1
      (hdomain Y hY).2.1 (hdomain Y hY).2.2).continuousAt.continuousWithinAt
  · intro Y hY
    have hYin : Y ∈ Icc (0 : ℝ) U := interior_subset hY
    exact (hasDerivAt_topEntropyDrop_center (hdomain Y hYin).1
      (hdomain Y hYin).2.1 (hdomain Y hYin).2.2).hasDerivWithinAt
  · intro Y hY
    have hYin : Y ∈ Icc (0 : ℝ) U := interior_subset hY
    exact topEntropyDropCenterSlope_nonneg hYin.1 hb
      (hdomain Y hYin).2.1 (hdomain Y hYin).2.2

/-- Moving an actual contact outward to the admissible endpoint can only
decrease the auxiliary reserve. -/
theorem topAuxiliaryReserve_ge_endpoint
    {rho c r X U : ℝ}
    (hs : 0 ≤ topS rho) (hcr : 0 ≤ c * r)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1) :
    topAuxiliaryReserve rho c r X ≥ topAuxiliaryReserve rho c r U := by
  have hmono := topEntropyDrop_monotoneOn_nonneg hcr hdomain
  have hU : 0 ≤ U := hX.1.trans hX.2
  have hdrop := hmono hX (show U ∈ Icc (0 : ℝ) U from ⟨hU, le_rfl⟩) hX.2
  unfold topAuxiliaryReserve
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hdrop)]

/-- The corrected TOP target gap at a contact is bounded below by the
endpoint auxiliary reserve. -/
theorem topGap_ge_endpointAuxiliaryReserve_of_contact
    {rho c r X U : ℝ}
    (hs : 0 ≤ topS rho) (hcr : 0 ≤ c * r)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    c * topJ (rho * r) - topEnvelope rho X ≥
      topAuxiliaryReserve rho c r U := by
  rw [topGap_eq_auxiliaryReserve_of_contact rho c r X hcontact]
  exact topAuxiliaryReserve_ge_endpoint hs hcr hX hdomain

end CourtadeKumar
