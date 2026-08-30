import InformationTheory.CourtadeKumar.TopPhi
import InformationTheory.CourtadeKumar.FixedWeightReduction
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Differential identities for the corrected TOP fixed-weight reduction. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma hasDerivAt_biasToProbability (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 - y) / 2) (-1 / 2) x := by
  convert ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).div_const 2 using 1
  all_goals ring

/-- In bias coordinates, the derivative of natural binary entropy is
`-artanh x`. -/
theorem hasDerivAt_topJ {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt topJ (-Real.artanh x) x := by
  let p : ℝ := (1 - x) / 2
  have hp0 : p ≠ 0 := by
    dsimp [p]
    linarith [hx.2]
  have hp1 : p ≠ 1 := by
    dsimp [p]
    linarith [hx.1]
  have hraw := (Real.hasDerivAt_binEntropy hp0 hp1).comp x
    (hasDerivAt_biasToProbability x)
  rw [show topJ = fun y : ℝ ↦ Real.binEntropy ((1 - y) / 2) from
    funext topJ_eq_binEntropy]
  convert hraw using 1
  dsimp [p]
  have hpos : 0 < (1 - x) / 2 := by linarith [hx.2]
  have hpos' : 0 < (1 + x) / 2 := by linarith [hx.1]
  rw [show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]
  rw [← Real.log_div hpos'.ne' hpos.ne']
  rw [show ((1 + x) / 2) / ((1 - x) / 2) = (1 + x) / (1 - x) by
    field_simp]
  rw [Real.artanh_eq_half_log (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2.le⟩)]
  ring

theorem hasDerivAt_topPhi {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt topPhi (Real.artanh x) x := by
  have h := (hasDerivAt_const x (Real.log 2)).sub (hasDerivAt_topJ hx)
  have heq : (fun _ : ℝ ↦ Real.log 2) - topJ = topPhi := by
    funext y
    change Real.log 2 - topJ y = topPhi y
    unfold topJ
    ring
  rw [heq] at h
  simpa using h

/-- The increasing odd function used to write `-topEnvelope'`. -/
noncomputable def topP (rho x : ℝ) : ℝ :=
  topS rho * Real.artanh x + 2 * topEll rho * x

theorem hasDerivAt_topEnvelope {rho x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (topEnvelope rho) (-topP rho x) x := by
  have hj := (hasDerivAt_topJ hx).const_mul (topS rho)
  have hquad : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2) using 1
    simp [id_eq, mul_comm]
  have hq := hquad.const_mul (topEll rho)
  have h := hj.add hq
  change HasDerivAt
    (fun y : ℝ ↦ topS rho * topJ y + topEll rho * (1 - y ^ 2))
    (-topP rho x) x
  convert h using 1
  unfold topP
  ring

/-- Derivative identity for the fixed-weight contact residual. -/
theorem hasDerivAt_topContactResidual
    {rho c r X : ℝ}
    (hplus : X + c * r ∈ Ioo (-1 : ℝ) 1)
    (hminus : X - c * r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (topContactResidual rho c r)
      ((topP rho (X + c * r) + topP rho (X - c * r)) / 2) X := by
  have hargPlus : HasDerivAt (fun Y : ℝ ↦ Y + c * r) 1 X :=
    (hasDerivAt_id X).add_const (c * r)
  have hargMinus : HasDerivAt (fun Y : ℝ ↦ Y - c * r) 1 X :=
    (hasDerivAt_id X).sub_const (c * r)
  have henvPlus := (hasDerivAt_topEnvelope (rho := rho) hplus).comp X hargPlus
  have henvMinus := (hasDerivAt_topEnvelope (rho := rho) hminus).comp X hargMinus
  have havg := (henvPlus.add henvMinus).div_const 2
  have h := (hasDerivAt_const X (c * topJ r)).sub havg
  change HasDerivAt
    (fun Y : ℝ ↦ c * topJ r -
      (topEnvelope rho (Y + c * r) + topEnvelope rho (Y - c * r)) / 2)
    ((topP rho (X + c * r) + topP rho (X - c * r)) / 2) X
  convert h using 1
  all_goals ring

end CourtadeKumar
