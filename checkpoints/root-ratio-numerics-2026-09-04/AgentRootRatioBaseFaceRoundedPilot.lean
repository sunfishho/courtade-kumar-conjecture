import AgentRootRatioBaseFaceGroupedPilot
import AgentRootRatioBaseFaceRoundedData
import InformationTheory.CourtadeKumar.LRDeterminantUpperKEnclosureCovers

/-!
# Short rational outer bounds for the actual base-face pilot

Each of the four expensive evaluator intervals is authenticated independently
against a supplied rational outer bound.  The final dominance comparison uses
only those four short outer bounds.  In particular it does not normalize the
large exact cross-products inside the original first-bracket checker.

The bound producer may use dyadic outward rounding, but no rounding algorithm
is trusted here: the four explicit endpoint-containment checks authenticate
the actual bounds.  Separate kernel receipts can be supplied for every check.
No successful numerical receipt is asserted in this generic source file.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioBaseFaceRoundedPilot

open RootRatioBaseFaceGroupedPilot
open LRUpperKMidpointCoarsening

theorem coversCheck_spec {outer inner : RationalEnclosure}
    (hcheck : coversCheck outer inner = true) : Covers outer inner := by
  simpa only [coversCheck, Covers, decide_eq_true_eq] using hcheck

/-- The short rational check is sound for any four real numbers enclosed
by the supplied intervals.  Only the required product signs are assumed.
-/
theorem FourBounds.nonnegative_of_contains
    {bounds : FourBounds} {B C D P : ℝ}
    (hB : bounds.b.Contains B) (hC : bounds.cBase.Contains C)
    (hD : bounds.d1.Contains D) (hP : bounds.psi.Contains P)
    (hcheck : bounds.dominanceCheck = true) :
    0 ≤ B * C + D * P := by
  have hspec :
      (0 : ℚ) ≤ bounds.b.lower ∧
      bounds.cBase.upper ≤ (0 : ℚ) ∧
      (0 : ℚ) ≤ bounds.d1.lower ∧
      (0 : ℚ) ≤ bounds.psi.lower ∧
      -(bounds.b.upper * bounds.cBase.lower) ≤
        bounds.d1.lower * bounds.psi.lower := by
    simpa only [FourBounds.dominanceCheck, decide_eq_true_eq] using hcheck
  have hBnonnegative : (0 : ℝ) ≤ B :=
    le_trans (by exact_mod_cast hspec.1) hB.1
  have hCnonpositive : C ≤ (0 : ℝ) :=
    le_trans hC.2 (by exact_mod_cast hspec.2.1)
  have hClowerNonpositive : (bounds.cBase.lower : ℝ) ≤ 0 :=
    hC.1.trans hCnonpositive
  have hDnonnegative : (0 : ℝ) ≤ D :=
    le_trans (by exact_mod_cast hspec.2.2.1) hD.1
  have hPlowerNonnegative : (0 : ℝ) ≤ (bounds.psi.lower : ℝ) := by
    exact_mod_cast hspec.2.2.2.1
  have hleft : ((bounds.b.upper * bounds.cBase.lower : ℚ) : ℝ) ≤ B * C := by
    calc
      ((bounds.b.upper * bounds.cBase.lower : ℚ) : ℝ) =
          (bounds.b.upper : ℝ) * (bounds.cBase.lower : ℝ) := by norm_num
      _ ≤ B * (bounds.cBase.lower : ℝ) :=
        mul_le_mul_of_nonpos_right hB.2 hClowerNonpositive
      _ ≤ B * C := mul_le_mul_of_nonneg_left hC.1 hBnonnegative
  have hright : ((bounds.d1.lower * bounds.psi.lower : ℚ) : ℝ) ≤ D * P := by
    calc
      ((bounds.d1.lower * bounds.psi.lower : ℚ) : ℝ) =
          (bounds.d1.lower : ℝ) * (bounds.psi.lower : ℝ) := by norm_num
      _ ≤ D * P := mul_le_mul hD.1 hP.1 hPlowerNonnegative hDnonnegative
  have hdominance :
      -((bounds.b.upper * bounds.cBase.lower : ℚ) : ℝ) ≤
        ((bounds.d1.lower * bounds.psi.lower : ℚ) : ℝ) := by
    exact_mod_cast hspec.2.2.2.2
  linarith

/-- Reusable semantic adapter for any current D9 value payload.  The four
coverage facts may be checked or proved separately and reused opaquely.
-/
theorem firstBracketAt_of_payload_and_rounded_bounds
    {terms : ℕ} {box : CertificateBox}
    {certificate : LRFiniteDeterminantD9ZeroFaceCertificate}
    {bounds : FourBounds} {point : CertificatePoint}
    (hpoint : box.Contains point)
    (hpayload : certificate.payloadCheck box = true)
    (hb : Covers bounds.b (certificate.evaluateAll terms box).b)
    (hc : Covers bounds.cBase (certificate.evaluateAll terms box).cBase)
    (hd : Covers bounds.d1 (certificate.evaluateAll terms box).d1)
    (hp : Covers bounds.psi (certificate.evaluateAll terms box).psi)
    (hcheck : bounds.dominanceCheck = true) :
    LRDeterminantFirstBracketAt point := by
  have hsound := certificate.evaluate_and_components_sound terms hpoint hpayload
  unfold LRDeterminantFirstBracketAt
  rw [hsound.2.firstBracketDecomposition]
  exact FourBounds.nonnegative_of_contains
    (contains_of_covers hb hsound.2.b)
    (contains_of_covers hc hsound.2.cBase)
    (contains_of_covers hd hsound.2.d1)
    (contains_of_covers hp hsound.2.psi) hcheck

theorem scriptBaseGap_nonnegative_on_pilot_of_rounded_receipts
    (bounds : FourBounds) {depth : ℕ}
    (hpayload : pilotPayloadCheck depth = true)
    (hb : bounds.bCoverCheck depth = true)
    (hc : bounds.cBaseCoverCheck depth = true)
    (hd : bounds.d1CoverCheck depth = true)
    (hp : bounds.psiCoverCheck depth = true)
    (hdominance : bounds.dominanceCheck = true)
    {k chi : ℝ}
    (hpoint : (pilotBox depth).Contains
      (lrFixed16RootRatioPoint (1 / 16) k chi)) :
    0 ≤ lrFixed16RootRatioScriptBaseGap k chi := by
  have hkLower : ((pilotBox depth).kLo : ℝ) ≤ k := hpoint.2.2.1
  have hkLoPos : (0 : ℝ) < ((pilotBox depth).kLo : ℝ) := by
    exact_mod_cast pilotBox_kLo_pos depth
  apply scriptBaseGap_nonnegative_of_firstBracketAt (hkLoPos.trans_le hkLower)
  exact firstBracketAt_of_payload_and_rounded_bounds hpoint hpayload
    (coversCheck_spec hb) (coversCheck_spec hc)
    (coversCheck_spec hd) (coversCheck_spec hp) hdominance

/-- The prechecked depth-eight candidate is a genuine part of the compact
base face.  To instantiate this theorem, the caller must supply the five
separate rounded receipts and the independently authenticated payload.
-/
theorem scriptBaseGap_nonnegative_on_pilot8
    (bounds : FourBounds)
    (hpayload : pilotPayloadCheck 8 = true)
    (hb : bounds.bCoverCheck 8 = true)
    (hc : bounds.cBaseCoverCheck 8 = true)
    (hd : bounds.d1CoverCheck 8 = true)
    (hp : bounds.psiCoverCheck 8 = true)
    (hdominance : bounds.dominanceCheck = true)
    {k chi : ℝ}
    (hpoint : (pilotBox 8).Contains
      (lrFixed16RootRatioPoint (1 / 16) k chi)) :
    0 ≤ lrFixed16RootRatioScriptBaseGap k chi :=
  scriptBaseGap_nonnegative_on_pilot_of_rounded_receipts bounds
    hpayload hb hc hd hp hdominance hpoint

/-- Final entry point for the concrete pilot.  The five remaining finite
receipts are the payload check and four outward-containment checks; there
is no analytic or derivative-model premise. -/
theorem scriptBaseGap_nonnegative_on_pilot8_of_receipts
    (hpayload : pilotPayloadCheck 8 = true)
    (hb : pilot8Bounds.bCoverCheck 8 = true)
    (hc : pilot8Bounds.cBaseCoverCheck 8 = true)
    (hd : pilot8Bounds.d1CoverCheck 8 = true)
    (hp : pilot8Bounds.psiCoverCheck 8 = true)
    {k chi : ℝ}
    (hpoint : (pilotBox 8).Contains
      (lrFixed16RootRatioPoint (1 / 16) k chi)) :
    0 ≤ lrFixed16RootRatioScriptBaseGap k chi :=
  scriptBaseGap_nonnegative_on_pilot8 pilot8Bounds
    hpayload hb hc hd hp pilot8Bounds_dominance hpoint

end RootRatioBaseFaceRoundedPilot
end CourtadeKumar
