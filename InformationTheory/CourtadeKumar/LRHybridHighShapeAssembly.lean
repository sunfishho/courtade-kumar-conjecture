import InformationTheory.CourtadeKumar.LRCompactVReplayLedgerSoundAdapter
import InformationTheory.CourtadeKumar.LRSmallVComplete
import InformationTheory.CourtadeKumar.LRFullFlowClosure

/-!
# Hybrid high-shape assembly

The compact `V` ledger is strongest away from the endpoint, while the
cancellation-coordinate midpoint and tangent evaluators are designed for
`R` close to one.  This module partitions at `R = 9/10`: the existing direct
`V` argument handles the compact side, leaving midpoint and tangent
certificates only on the near-endpoint side.
-/

open Set

namespace CourtadeKumar

def LRHighShapeNearEndpointHalfMidpointTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    9 / 10 < R →
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t

def LRHighShapeNearEndpointTangentTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    9 / 10 < R →
    0 ≤ lrFlowTReserve R v t

/-- The compact direct-`V` ledger and the two near-endpoint certificates
exhaust the high-shape positive-flow chart. -/
theorem lrFlowNumeratorP_nonneg_target_of_compactV_and_nearEndpoint
    (ledger : LRCompactVSoundLedger)
    (hmidpoint : LRHighShapeNearEndpointHalfMidpointTheorem)
    (htangent : LRHighShapeNearEndpointTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  by_cases htLow : t ^ 2 ≤ 17 / 20
  · exact lrFlowNumeratorP_nonneg_target_lowShape
      hR hp hv ht htLow htarget
  have htHigh : 17 / 20 ≤ t ^ 2 := by linarith
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target
      hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
      hR hv ht hJzero
  · by_cases hvSmall : v ≤ 1 / 3
    · exact lrHighShapeSmallVNumeratorTheorem
        R p v t hR hp hv ht htHigh hvSmall hJpos htarget
    have hvHigh : 1 / 3 ≤ v := by linarith
    by_cases hcompact : R ≤ 9 / 10
    · have hV := ledger.v_nonnegative R v t hR hcompact hv hvHigh ht
        htHigh hJpos
      exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
        hR hp hv ht htarget hJpos hV
    · have hnear : 9 / 10 < R := lt_of_not_ge hcompact
      exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
        hR hp hv ht htarget hJpos
        (hmidpoint R v t hR hv ht htHigh hvHigh hJpos hnear)
        (htangent R v t hR hv ht htHigh hvHigh hJpos hnear)

/-- Differential form of the hybrid high-shape assembly, ready for
integration along a regular target-root trajectory. -/
theorem hasDerivAt_lrReserve_exactFlow_of_compactV_and_nearEndpoint
    (ledger : LRCompactVSoundLedger)
    (hmidpoint : LRHighShapeNearEndpointHalfMidpointTheorem)
    (htangent : LRHighShapeNearEndpointTangentTheorem)
    {R p v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvval : vfun R = v) (hvfun : HasDerivAt vfun v' R)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hcurve :
      (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
        (fun y : ℝ ↦ lrSquareObjective y (lrProbabilityToOdds p))) :
    HasDerivAt
        (fun y : ℝ ↦
          lrSquareReserve y (lrProbabilityToOdds p) (vfun y) t)
        (lrFlowNumerator R (lrProbabilityToOdds p) v t /
          (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R ∧
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) := by
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
    calc
      lrGShape (Real.sqrt R * t) v = lrSquareTarget R v t := rfl
      _ = lrPrefixEll R p := htarget.symm
      _ = lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hR hp
  have hderiv := hasDerivAt_lrReserve_exactFlow hR hu.1 hv.1 ht hvt
    hvval hvfun hroot hcurve
  have hpOdds : lrFlowP (lrProbabilityToOdds p) = p := by
    simpa [lrFlowP, lrOddsToProbability] using
      lrOddsToProbability_probabilityToOdds
        (show p < 1 from hp.2.trans (by norm_num))
  have hnumP := lrFlowNumeratorP_nonneg_target_of_compactV_and_nearEndpoint
    ledger hmidpoint htangent hR
    (show p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) from ⟨hp.1, hp.2.le⟩)
    hv ht htarget
  have hnum : 0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t := by
    rw [lrFlowNumerator_eq_p, hpOdds]
    exact hnumP
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hden : 0 < lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 :=
    mul_pos (mul_pos hB (sq_pos_of_pos (sub_pos.mpr hR.2)))
      (sq_pos_of_pos ht.1)
  exact ⟨hderiv, div_nonneg hnum hden.le⟩

end CourtadeKumar
