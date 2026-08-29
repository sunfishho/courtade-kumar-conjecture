import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalDomainAdapters
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACCornerSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACPartialsSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalEvaluatorAssembly

/-!
# Fully sound historical sharp `A/C` nodes

This module closes the semantic interface of the four historical `A/C`
nodes.  The only executable assumptions are

* the existing open-chart box check;
* the existing sharp payload check; and
* the four monotone-corner checks used by the archived evaluator.

Box containment supplies the queried real chart point.  The domain adapter
turns these Boolean checks into the physical-domain facts required by the
partial ledger and the monotone-corner theorems.  Each conclusion is one
`Encloses` statement for the value and all three primitive partials.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalSharpNodeSoundness

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD
open LRUpperKHistoricalACValues
open LRUpperKHistoricalDomainAdapters
open LRUpperKHistoricalACPartialsSoundness
open LRUpperKHistoricalEvaluatorAssembly

abbrev Payload := LRUpperKHistoricalACAD.Payload

/-! ## Exact node jets -/

noncomputable def aY0Jet (coordinate : CertificatePoint) : Jet3 :=
  let raw := lrDeterminantKChartDecode coordinate
  let partials := aY0PrimitivePartials coordinate
  { value := aPrimitive coordinate.s (lrCertificateY0 raw)
    derivS := partials.derivS
    derivK := partials.derivK
    derivH := partials.derivH }

noncomputable def cY0Jet (coordinate : CertificatePoint) : Jet3 :=
  let raw := lrDeterminantKChartDecode coordinate
  let partials := cY0PrimitivePartials coordinate
  { value := cPrimitive coordinate.s (lrCertificateY0 raw)
    derivS := partials.derivS
    derivK := partials.derivK
    derivH := partials.derivH }

noncomputable def aEJet (coordinate : CertificatePoint) : Jet3 :=
  let raw := lrDeterminantKChartDecode coordinate
  let partials := aEPrimitivePartials coordinate
  { value := aPrimitive coordinate.s (lrCertificateE raw)
    derivS := partials.derivS
    derivK := partials.derivK
    derivH := partials.derivH }

noncomputable def cEJet (coordinate : CertificatePoint) : Jet3 :=
  let raw := lrDeterminantKChartDecode coordinate
  let partials := cEPrimitivePartials coordinate
  { value := cPrimitive coordinate.s (lrCertificateE raw)
    derivS := partials.derivS
    derivK := partials.derivK
    derivH := partials.derivH }

/-! ## From the executable checks to the partial-ledger interface -/

theorem partialsValid_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate) :
    PartialsValid terms box payload coordinate := by
  have hfacts := facts_of_checked hdomain hsharp hcoordinate
  exact
    { sharp := hfacts.checks.valid
      coordinateMem := hcoordinate
      sPhysical := hfacts.point.sPhysical
      y0Physical := hfacts.point.y0Physical
      ePhysical := hfacts.point.ePhysical
      oneMinusSLower :=
        hfacts.endpoints.oneMinusSLowerNonnegative
      oneMinusY0Lower :=
        hfacts.endpoints.oneMinusY0LowerNonnegative
      oneMinusELower :=
        hfacts.endpoints.oneMinusELowerNonnegative }

/-! ## Corner-value soundness -/

theorem aY0CornerValue_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      aCornerCheck 40 48 box (y0AD box).value = true) :
    (aCornerI terms 40 48 box (y0AD box).value).Contains
      (aPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  have hfacts := facts_of_checked hdomain hsharp hcoordinate
  exact aCornerI_sound terms 40 48
    hfacts.endpoints.sLoPhysical
    hfacts.point.sPhysical
    hfacts.endpoints.sHiPhysical
    hfacts.endpoints.y0LowerPhysical
    hfacts.point.y0Physical
    hfacts.endpoints.y0UpperPhysical
    hfacts.point.sRange
    hfacts.point.y0Value
    hcorner

theorem cY0CornerValue_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      cCornerCheck 40 48 box (y0AD box).value = true) :
    (cCornerI terms 40 48 box (y0AD box).value).Contains
      (cPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  have hfacts := facts_of_checked hdomain hsharp hcoordinate
  exact cCornerI_sound terms 40 48
    hfacts.endpoints.sLoPhysical
    hfacts.point.sPhysical
    hfacts.endpoints.sHiPhysical
    hfacts.endpoints.y0LowerPhysical
    hfacts.point.y0Physical
    hfacts.endpoints.y0UpperPhysical
    hfacts.point.sRange
    hfacts.point.y0Value
    hcorner

theorem aECornerValue_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      aCornerCheck 40 48 box (eAD box).value = true) :
    (aCornerI terms 40 48 box (eAD box).value).Contains
      (aPrimitive coordinate.s
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
  have hfacts := facts_of_checked hdomain hsharp hcoordinate
  exact aCornerI_sound terms 40 48
    hfacts.endpoints.sLoPhysical
    hfacts.point.sPhysical
    hfacts.endpoints.sHiPhysical
    hfacts.endpoints.eLowerPhysical
    hfacts.point.ePhysical
    hfacts.endpoints.eUpperPhysical
    hfacts.point.sRange
    hfacts.point.eValue
    hcorner

theorem cECornerValue_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      cCornerCheck 40 48 box (eAD box).value = true) :
    (cCornerI terms 40 48 box (eAD box).value).Contains
      (cPrimitive coordinate.s
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
  have hfacts := facts_of_checked hdomain hsharp hcoordinate
  exact cCornerI_sound terms 40 48
    hfacts.endpoints.sLoPhysical
    hfacts.point.sPhysical
    hfacts.endpoints.sHiPhysical
    hfacts.endpoints.eLowerPhysical
    hfacts.point.ePhysical
    hfacts.endpoints.eUpperPhysical
    hfacts.point.sRange
    hfacts.point.eValue
    hcorner

/-! ## Full value-and-partial soundness for the four executable nodes -/

theorem aY0HistoricalAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      aCornerCheck 40 48 box (y0AD box).value = true) :
    Encloses (aY0HistoricalAD terms box payload) (aY0Jet coordinate) := by
  have hvalid := partialsValid_of_checked hdomain hsharp hcoordinate
  have hvalue := aY0CornerValue_sound terms
    hdomain hsharp hcoordinate hcorner
  have hpartials := aY0Partials_primitive_sound terms hvalid
  simpa [Encloses, aY0HistoricalAD, aY0Jet, ContainsPartials] using
    And.intro hvalue hpartials

theorem cY0HistoricalAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      cCornerCheck 40 48 box (y0AD box).value = true) :
    Encloses (cY0HistoricalAD terms box payload) (cY0Jet coordinate) := by
  have hvalid := partialsValid_of_checked hdomain hsharp hcoordinate
  have hvalue := cY0CornerValue_sound terms
    hdomain hsharp hcoordinate hcorner
  have hpartials := cY0Partials_primitive_sound terms hvalid
  simpa [Encloses, cY0HistoricalAD, cY0Jet, ContainsPartials] using
    And.intro hvalue hpartials

theorem aEHistoricalAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      aCornerCheck 40 48 box (eAD box).value = true) :
    Encloses (aEHistoricalAD terms box payload) (aEJet coordinate) := by
  have hvalid := partialsValid_of_checked hdomain hsharp hcoordinate
  have hvalue := aECornerValue_sound terms
    hdomain hsharp hcoordinate hcorner
  have hpartials := aEPartials_primitive_sound terms hvalid
  simpa [Encloses, aEHistoricalAD, aEJet, ContainsPartials] using
    And.intro hvalue hpartials

theorem cEHistoricalAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hcorner :
      cCornerCheck 40 48 box (eAD box).value = true) :
    Encloses (cEHistoricalAD terms box payload) (cEJet coordinate) := by
  have hvalid := partialsValid_of_checked hdomain hsharp hcoordinate
  have hvalue := cECornerValue_sound terms
    hdomain hsharp hcoordinate hcorner
  have hpartials := cEPartials_primitive_sound terms hvalid
  simpa [Encloses, cEHistoricalAD, cEJet, ContainsPartials] using
    And.intro hvalue hpartials

/-! ## One bundled theorem for downstream evaluator assembly -/

structure SharpNodeEnclosures (terms : ℕ) (box : CertificateBox)
    (payload : Payload) (coordinate : CertificatePoint) : Prop where
  aY0 : Encloses (aY0HistoricalAD terms box payload) (aY0Jet coordinate)
  cY0 : Encloses (cY0HistoricalAD terms box payload) (cY0Jet coordinate)
  aE : Encloses (aEHistoricalAD terms box payload) (aEJet coordinate)
  cE : Encloses (cEHistoricalAD terms box payload) (cEJet coordinate)

theorem sharpNodeEnclosures_of_checked (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (haY0Corner :
      aCornerCheck 40 48 box (y0AD box).value = true)
    (hcY0Corner :
      cCornerCheck 40 48 box (y0AD box).value = true)
    (haECorner :
      aCornerCheck 40 48 box (eAD box).value = true)
    (hcECorner :
      cCornerCheck 40 48 box (eAD box).value = true) :
    SharpNodeEnclosures terms box payload coordinate :=
  { aY0 := aY0HistoricalAD_sound terms
      hdomain hsharp hcoordinate haY0Corner
    cY0 := cY0HistoricalAD_sound terms
      hdomain hsharp hcoordinate hcY0Corner
    aE := aEHistoricalAD_sound terms
      hdomain hsharp hcoordinate haECorner
    cE := cEHistoricalAD_sound terms
      hdomain hsharp hcoordinate hcECorner }

end LRUpperKHistoricalSharpNodeSoundness
end CourtadeKumar
