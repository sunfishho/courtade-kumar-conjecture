import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACScalarSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKACMonotonicity

/-!
# Soundness of the historical monotone-corner `A/C` value nodes

The executable corner nodes evaluate the scalar primitive only at the two
extremal corners selected by the analytic monotonicity rules.  This file
combines the checked scalar enclosures with those unconditional corner rules.

The hypotheses deliberately expose every domain fact used by the argument:
the three `s` values lie in `(0,1)`, the three `y` values lie in `[0,1)`, and
the queried real point lies between the rational endpoints.  Thus neither the
Boolean scalar checks nor the corner selection silently assert a physical
domain condition.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalACValues

open Set
open LRUpperKReplayCertificate

private theorem aAutoI_sound (terms sqrtFuel logFuel : ℕ) (s y : ℚ)
    (hcheck : scalarAutoCheck sqrtFuel logFuel s y = true) :
    (aAutoI terms sqrtFuel logFuel s y).Contains
      (aPrimitive (s : ℝ) (y : ℝ)) := by
  have hscalar :
      scalarCheck s y (ScalarPayload.auto sqrtFuel logFuel s y) = true := by
    simpa [scalarAutoCheck] using hcheck
  simpa [aAutoI] using
    (aScalarI_sound terms (s := s) (y := y)
      (payload := ScalarPayload.auto sqrtFuel logFuel s y) hscalar)

private theorem cAutoI_sound (terms sqrtFuel logFuel : ℕ) (s y : ℚ)
    (hcheck : scalarAutoCheck sqrtFuel logFuel s y = true) :
    (cAutoI terms sqrtFuel logFuel s y).Contains
      (cPrimitive (s : ℝ) (y : ℝ)) := by
  have hscalar :
      scalarCheck s y (ScalarPayload.auto sqrtFuel logFuel s y) = true := by
    simpa [scalarAutoCheck] using hcheck
  simpa [cAutoI] using
    (cScalarI_sound terms (s := s) (y := y)
      (payload := ScalarPayload.auto sqrtFuel logFuel s y) hscalar)

/-- The historical `A` corner hull contains `A_s(y)` throughout the supplied
rational rectangle.  The lower corner is `(sHi,yLo)` and the upper corner is
`(sLo,yHi)` because `A` is antitone in `s` and monotone in `y`. -/
theorem aCornerI_sound (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {yI : RationalEnclosure} {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (yI.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (yI.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : yI.Contains y)
    (hcheck : aCornerCheck sqrtFuel logFuel box yI = true) :
    (aCornerI terms sqrtFuel logFuel box yI).Contains (aPrimitive s y) := by
  have hchecks :
      scalarAutoCheck sqrtFuel logFuel box.sHi yI.lower = true ∧
        scalarAutoCheck sqrtFuel logFuel box.sLo yI.upper = true := by
    simpa [aCornerCheck] using hcheck
  have hLower := aAutoI_sound terms sqrtFuel logFuel
    box.sHi yI.lower hchecks.1
  have hUpper := aAutoI_sound terms sqrtFuel logFuel
    box.sLo yI.upper hchecks.2
  have hCorners := LRUpperKReplayCertificate.aPrimitive_corner_bounds
    hsLo hs hsHi hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  change
    ((aAutoI terms sqrtFuel logFuel box.sHi yI.lower).lower : ℝ) ≤
        aPrimitive s y ∧
      aPrimitive s y ≤
        ((aAutoI terms sqrtFuel logFuel box.sLo yI.upper).upper : ℝ)
  exact ⟨hLower.1.trans hCorners.1, hCorners.2.trans hUpper.2⟩

/-- The historical `C` corner hull contains `C_s(y)` throughout the supplied
rational rectangle.  Both coordinate directions are antitone, so the lower
corner is `(sHi,yHi)` and the upper corner is `(sLo,yLo)`. -/
theorem cCornerI_sound (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {yI : RationalEnclosure} {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (yI.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (yI.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : yI.Contains y)
    (hcheck : cCornerCheck sqrtFuel logFuel box yI = true) :
    (cCornerI terms sqrtFuel logFuel box yI).Contains (cPrimitive s y) := by
  have hchecks :
      scalarAutoCheck sqrtFuel logFuel box.sHi yI.upper = true ∧
        scalarAutoCheck sqrtFuel logFuel box.sLo yI.lower = true := by
    simpa [cCornerCheck] using hcheck
  have hLower := cAutoI_sound terms sqrtFuel logFuel
    box.sHi yI.upper hchecks.1
  have hUpper := cAutoI_sound terms sqrtFuel logFuel
    box.sLo yI.lower hchecks.2
  have hCorners := LRUpperKReplayCertificate.cPrimitive_corner_bounds
    hsLo hs hsHi hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  change
    ((cAutoI terms sqrtFuel logFuel box.sHi yI.upper).lower : ℝ) ≤
        cPrimitive s y ∧
      cPrimitive s y ≤
        ((cAutoI terms sqrtFuel logFuel box.sLo yI.lower).upper : ℝ)
  exact ⟨hLower.1.trans hCorners.1, hCorners.2.trans hUpper.2⟩

end LRUpperKHistoricalACValues
end CourtadeKumar
