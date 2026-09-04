import AgentConcreteRootRatioCalculus
import AgentRootRatioBaseFacePilotData

/-!
# A concrete base-face numerical pilot using the existing first-bracket checker

Depth zero is precisely the prescribed `base-face-030` box:
`s = 1/16`, `2 <= k <= 4`, `1/4 <= chi <= 1/2`.
Larger depths select smaller boxes around `(k,chi) = (3,3/8)`; they do not
claim to cover the original box.

Despite this file's historical "GroupedPilot" name, it intentionally uses
the current, proved `firstBracketDominanceCheck`.  The separate grouped
evaluator draft references component fields absent from the current D9 API.

All analytic enclosure semantics are supplied by the existing D9 evaluator.
The only remaining input to the final theorem is a closed Boolean check.
No successful numerical result is asserted in this source file.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioBaseFaceGroupedPilot

theorem pilotCheck_of_parts {depth : ℕ}
    (hpayload : pilotPayloadCheck depth = true)
    (hdominance : pilotDominanceCheck depth = true) :
    pilotCheck depth = true := by
  simpa only [pilotCheck, Bool.and_eq_true] using And.intro hpayload hdominance

theorem pilotBox_kLo_pos (depth : ℕ) : (0 : ℚ) < (pilotBox depth).kLo := by
  have hpower : (1 : ℚ) ≤ (2 : ℚ) ^ depth :=
    one_le_pow₀ (by norm_num)
  have hpowerPos : (0 : ℚ) < (2 : ℚ) ^ depth := by positivity
  have hfraction : (1 : ℚ) / (2 : ℚ) ^ depth ≤ 1 :=
    (div_le_one hpowerPos).2 hpower
  change (0 : ℚ) < 3 - 1 / (2 : ℚ) ^ depth
  linarith

/-- Convert an already certified production first bracket into the
normalized scalar target used by the compact base-face proof. -/
theorem scriptBaseGap_nonnegative_of_firstBracketAt
    {k chi : ℝ} (hk : 0 < k)
    (hfirst : LRDeterminantFirstBracketAt
      (lrFixed16RootRatioPoint (1 / 16) k chi)) :
    0 ≤ lrFixed16RootRatioScriptBaseGap k chi := by
  have hgap : 0 ≤ lrFixed16RootRatioBaseGap k chi := by
    unfold lrFixed16RootRatioBaseGap
    rw [lrFixed16RootRatioGap_eq_firstBracket]
    exact hfirst
  rw [lrFixed16RootRatioBaseGap_eq_scaled_script hk.ne'] at hgap
  exact (mul_nonneg_iff_of_pos_left
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 16) hk)).mp hgap

/-- Local adapter using the already compiled component-soundness theorem.
Keeping this derivation here avoids rebuilding the larger D9 module merely
to import a newer convenience lemma with the same conclusion. -/
theorem firstBracketAt_of_payload_and_dominanceCheck
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9ZeroFaceCertificate}
    (hpoint : box.Contains point)
    (hpayload : certificate.payloadCheck box = true)
    (hdominance : certificate.firstBracketDominanceCheck terms box = true) :
    LRDeterminantFirstBracketAt point := by
  have hsound := certificate.evaluate_and_components_sound terms hpoint hpayload
  let evaluation := certificate.evaluateAll terms box
  have hspec :
      (0 : ℚ) ≤ evaluation.b.lower ∧
      evaluation.cBase.upper ≤ (0 : ℚ) ∧
      (0 : ℚ) ≤ evaluation.d1.lower ∧
      (0 : ℚ) ≤ evaluation.psi.lower ∧
      -(evaluation.b.upper * evaluation.cBase.lower) ≤
        evaluation.d1.lower * evaluation.psi.lower := by
    simpa only [LRFiniteDeterminantD9ZeroFaceCertificate.firstBracketDominanceCheck,
      evaluation, decide_eq_true_eq] using hdominance
  have hB : (0 : ℝ) ≤ lrCertificateBFlow point :=
    le_trans (by exact_mod_cast hspec.1) hsound.2.b.1
  have hC : LRFiniteDeterminantD9ZeroFaceCertificate.firstBracketBaseValue point ≤ 0 :=
    le_trans hsound.2.cBase.2 (by exact_mod_cast hspec.2.1)
  have hClower : (evaluation.cBase.lower : ℝ) ≤ 0 :=
    hsound.2.cBase.1.trans hC
  have hD : (0 : ℝ) ≤ lrDeterminantD1 point :=
    le_trans (by exact_mod_cast hspec.2.2.1) hsound.2.d1.1
  have hPlower : (0 : ℝ) ≤ (evaluation.psi.lower : ℝ) := by
    exact_mod_cast hspec.2.2.2.1
  have hleft : ((evaluation.b.upper * evaluation.cBase.lower : ℚ) : ℝ) ≤
      lrCertificateBFlow point *
        LRFiniteDeterminantD9ZeroFaceCertificate.firstBracketBaseValue point := by
    calc
      ((evaluation.b.upper * evaluation.cBase.lower : ℚ) : ℝ) =
          (evaluation.b.upper : ℝ) * (evaluation.cBase.lower : ℝ) := by norm_num
      _ ≤ lrCertificateBFlow point * (evaluation.cBase.lower : ℝ) :=
        mul_le_mul_of_nonpos_right hsound.2.b.2 hClower
      _ ≤ _ := mul_le_mul_of_nonneg_left hsound.2.cBase.1 hB
  have hright : ((evaluation.d1.lower * evaluation.psi.lower : ℚ) : ℝ) ≤
      lrDeterminantD1 point * lrDeterminantPsi point := by
    calc
      ((evaluation.d1.lower * evaluation.psi.lower : ℚ) : ℝ) =
          (evaluation.d1.lower : ℝ) * (evaluation.psi.lower : ℝ) := by norm_num
      _ ≤ _ := mul_le_mul hsound.2.d1.1 hsound.2.psi.1 hPlower hD
  have hdominanceReal :
      -((evaluation.b.upper * evaluation.cBase.lower : ℚ) : ℝ) ≤
        ((evaluation.d1.lower * evaluation.psi.lower : ℚ) : ℝ) := by
    exact_mod_cast hspec.2.2.2.2
  unfold LRDeterminantFirstBracketAt
  rw [hsound.2.firstBracketDecomposition]
  linarith

/-- A successful exact numerical check proves a nontrivial base-face box.
The depth remains explicit so a smaller accepted pilot cannot be confused
with a certificate covering the whole prescribed depth-zero leaf. -/
theorem scriptBaseGap_nonnegative_on_pilot
    {depth : ℕ} (hcheck : pilotCheck depth = true)
    {k chi : ℝ}
    (hpoint : (pilotBox depth).Contains
      (lrFixed16RootRatioPoint (1 / 16) k chi)) :
    0 ≤ lrFixed16RootRatioScriptBaseGap k chi := by
  have hparts : pilotPayloadCheck depth = true ∧
      pilotDominanceCheck depth = true := by
    simpa only [pilotCheck, Bool.and_eq_true] using hcheck
  have hkLower : ((pilotBox depth).kLo : ℝ) ≤ k := hpoint.2.2.1
  have hkLoPos : (0 : ℝ) < ((pilotBox depth).kLo : ℝ) := by
    exact_mod_cast pilotBox_kLo_pos depth
  apply scriptBaseGap_nonnegative_of_firstBracketAt (hkLoPos.trans_le hkLower)
  exact firstBracketAt_of_payload_and_dominanceCheck
    pilotTerms hpoint hparts.1 hparts.2

end RootRatioBaseFaceGroupedPilot
end CourtadeKumar
