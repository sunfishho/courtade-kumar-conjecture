import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalQPartialSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalFixedMovingSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACChainRules

/-!
# Soundness of the historical sharp `A/C` partial ledgers

This module assembles the already checked scalar pieces of the historical
three-coordinate upper-`K` evaluator.  It keeps the value enclosure separate
from the derivative ledger: the main theorems below establish containment of
the three partials, and the final four adapters attach any independently
proved sound value enclosure.

The exact partials are first written in the same `fixed + moving` form as the
historical checker.  Parallel `PrimitivePartials` definitions and algebraic
bridge theorems identify them with `aPrimitiveDeriv` and
`cPrimitiveDeriv`.  Thus this file does not merely prove containment of a
surrogate interval expression.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalACPartialsSoundness

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD
open LRUpperKHistoricalFixedMovingSoundness
open LRUpperKHistoricalACChainRules

/-! Local aliases make the sharp payload, validity record, and executable
partial record unambiguous despite the simultaneously opened production
namespace. -/

abbrev Payload := LRUpperKHistoricalACAD.Payload
abbrev Valid := LRUpperKHistoricalACAD.Valid
abbrev Partials := LRUpperKHistoricalACAD.Partials

/-! ## Semantic partial triples -/

/-- A real-valued analogue of the executable rational `Partials` record. -/
@[ext] structure ExactPartials where
  derivS : ℝ
  derivK : ℝ
  derivH : ℝ

/-- Componentwise semantic containment of a real partial triple. -/
def ContainsPartials (interval : Partials) (exact : ExactPartials) : Prop :=
  interval.derivS.Contains exact.derivS ∧
    interval.derivK.Contains exact.derivK ∧
    interval.derivH.Contains exact.derivH

/-! ## Exact historical formulas -/

noncomputable def aY0ExactPartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let y := lrCertificateY0 raw
  let cs := fixedYPartialS coordinate.s y
  let m := movingYCoefficient coordinate.s y
  { derivS := cs + m * (2 * y / coordinate.s)
    derivK := m * (y / coordinate.k)
    derivH := m * (2 * coordinate.chi * lrCertificateE raw) }

noncomputable def cY0ExactPartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let y := lrCertificateY0 raw
  let a := aY0ExactPartials coordinate
  { derivS := a.derivS -
      2 * (y * lrCertificateQPrime y) / coordinate.s
    derivK := a.derivK -
      (y * lrCertificateQPrime y) / coordinate.k
    derivH := a.derivH -
      2 * coordinate.chi * lrCertificateE raw * lrCertificateQPrime y }

noncomputable def aEExactPartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let e := lrCertificateE raw
  let cs := fixedYPartialS coordinate.s e
  let m := movingYCoefficient coordinate.s e
  { derivS := cs + m * (2 * e / coordinate.s)
    derivK := m * (e / coordinate.k)
    derivH := 0 }

noncomputable def cEExactPartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let e := lrCertificateE raw
  let a := aEExactPartials coordinate
  { derivS := a.derivS -
      lrCertificateQPrime e * (2 * e / coordinate.s)
    derivK := a.derivK -
      lrCertificateQPrime e * (e / coordinate.k)
    derivH := 0 }

/-! ## The same formulas expressed through the primitive derivative API -/

noncomputable def aY0PrimitivePartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let y := lrCertificateY0 raw
  { derivS := aPrimitiveDeriv coordinate.s y 1
      (2 * y / coordinate.s)
    derivK := aPrimitiveDeriv coordinate.s y 0
      (y / coordinate.k)
    derivH := aPrimitiveDeriv coordinate.s y 0
      (2 * coordinate.chi * lrCertificateE raw) }

noncomputable def cY0PrimitivePartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let y := lrCertificateY0 raw
  { derivS := cPrimitiveDeriv coordinate.s y 1
      (2 * y / coordinate.s)
    derivK := cPrimitiveDeriv coordinate.s y 0
      (y / coordinate.k)
    derivH := cPrimitiveDeriv coordinate.s y 0
      (2 * coordinate.chi * lrCertificateE raw) }

noncomputable def aEPrimitivePartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let e := lrCertificateE raw
  { derivS := aPrimitiveDeriv coordinate.s e 1
      (2 * e / coordinate.s)
    derivK := aPrimitiveDeriv coordinate.s e 0
      (e / coordinate.k)
    derivH := aPrimitiveDeriv coordinate.s e 0 0 }

noncomputable def cEPrimitivePartials
    (coordinate : CertificatePoint) : ExactPartials :=
  let raw := lrDeterminantKChartDecode coordinate
  let e := lrCertificateE raw
  { derivS := cPrimitiveDeriv coordinate.s e 1
      (2 * e / coordinate.s)
    derivK := cPrimitiveDeriv coordinate.s e 0
      (e / coordinate.k)
    derivH := cPrimitiveDeriv coordinate.s e 0 0 }

theorem aY0ExactPartials_eq_primitive (coordinate : CertificatePoint) :
    aY0ExactPartials coordinate = aY0PrimitivePartials coordinate := by
  ext <;>
    simp [aY0ExactPartials, aY0PrimitivePartials,
      aPrimitiveDeriv_eq_fixed_add_moving]

theorem cY0ExactPartials_eq_primitive (coordinate : CertificatePoint) :
    cY0ExactPartials coordinate = cY0PrimitivePartials coordinate := by
  ext <;>
    simp [cY0ExactPartials, cY0PrimitivePartials,
      aY0ExactPartials, cPrimitiveDeriv_eq_fixed_add_moving_sub_q] <;>
    ring

theorem aEExactPartials_eq_primitive (coordinate : CertificatePoint) :
    aEExactPartials coordinate = aEPrimitivePartials coordinate := by
  ext <;>
    simp [aEExactPartials, aEPrimitivePartials,
      aPrimitiveDeriv_eq_fixed_add_moving]

theorem cEExactPartials_eq_primitive (coordinate : CertificatePoint) :
    cEExactPartials coordinate = cEPrimitivePartials coordinate := by
  ext <;>
    simp [cEExactPartials, cEPrimitivePartials,
      aEExactPartials, cPrimitiveDeriv_eq_fixed_add_moving_sub_q] <;>
    ring

/-! ## Explicit validity data consumed by the sharp scalar nodes -/

/-- The generated checker proves `sharp`; the remaining fields are ordinary
physical-domain and nonnegative-factor facts for the queried chart point.
They are kept explicit so no interval refinement silently assumes them. -/
structure PartialsValid (terms : ℕ) (box : CertificateBox)
    (payload : Payload) (coordinate : CertificatePoint) : Prop where
  sharp : Valid terms box payload
  coordinateMem : box.Contains coordinate
  sPhysical : coordinate.s ∈ Ioo (0 : ℝ) 1
  y0Physical :
    lrCertificateY0 (lrDeterminantKChartDecode coordinate) ∈
      Ico (0 : ℝ) 1
  ePhysical :
    lrCertificateE (lrDeterminantKChartDecode coordinate) ∈
      Ico (0 : ℝ) 1
  oneMinusSLower : (0 : ℚ) ≤ (oneMinusSI box).lower
  oneMinusY0Lower : (0 : ℚ) ≤ (oneMinusYI box).lower
  oneMinusELower : (0 : ℚ) ≤ (oneMinusEI box).lower

/-! ## Reusable value and check extraction -/

private theorem sValue_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sAD box).value.Contains coordinate.s := by
  exact (IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)).1

private theorem sAD_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sAD box).Contains coordinate.s 1 0 0 := by
  exact IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)

private theorem ratioValue_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (ratioAD box).value.Contains coordinate.k := by
  exact (IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)).1

private theorem y0BValue_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (y0BAd box).value.Contains
      (lrCertificateB coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  have hy := LRUpperKReplayCertificate.y0AD_sound
    hvalid.base hcoordinate
  dsimp only at hy
  have hb := lrCertificateBAD_sound (sAD_sound hcoordinate) hy
  simpa [y0BAd, lrDeterminantKChartDecode] using hb.1

private theorem eBValue_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (eBAd box).value.Contains
      (lrCertificateB coordinate.s
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
  have he := LRUpperKHistoricalACAD.eAD_sound
    hvalid hcoordinate
  dsimp only at he
  have hb := lrCertificateBAD_sound (sAD_sound hcoordinate) he
  simpa [eBAd, lrDeterminantKChartDecode] using hb.1

private theorem omegaECheck_parts {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload) :
    (payload.base.omegaE.qAtB.check (eBAd box).value = true ∧
      payload.base.omegaE.qAtY.check (eAD box).value = true) ∧
      payload.base.omegaE.qPrimeAtB.check (eBAd box).value = true := by
  simpa [LROmegaADCertificate.check, eBAd] using
    hvalid.base.omegaECheck

private theorem omegaEQPrimeAtBValueCheck {terms : ℕ}
    {box : CertificateBox} {payload : Payload}
    (hvalid : Valid terms box payload) :
    payload.base.omegaE.qPrimeAtB.value.check
      (eBAd box).value = true := by
  have hcheck := (omegaECheck_parts hvalid).2
  have hparts :
      payload.base.omegaE.qPrimeAtB.value.check
          (eBAd box).value = true ∧
        lrQSecondCoarseCheck (eBAd box).value = true := by
    simpa [LRQPrimeADCertificate.check] using hcheck
  exact hparts.1

/-! ## The `e`-branch `Q'` node and coordinate velocities -/

/-- The `qPrimeEI` slope field really encloses `Q'(e)`.  In particular, the
fact is extracted from the checked `omegaE.qAtY` payload rather than assumed
from the generated interval. -/
theorem qPrimeEI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (qPrimeEI terms payload).Contains
      (lrCertificateQPrime
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
  have hqAtYCheck := (omegaECheck_parts hvalid).1.2
  have hqAtYParts :
      payload.base.omegaE.qAtY.value.check (eAD box).value = true ∧
        payload.base.omegaE.qAtY.slope.check (eAD box).value = true := by
    simpa [LRQADCertificate.check] using hqAtYCheck
  have he := LRUpperKHistoricalACAD.eValue_sound
    hvalid hcoordinate
  simpa [qPrimeEI] using
    payload.base.omegaE.qAtY.slope.sound terms hqAtYParts.2 he

private theorem ePartialSI_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (ePartialSI box).Contains
      (2 * lrCertificateE (lrDeterminantKChartDecode coordinate) /
        coordinate.s) := by
  have hscaled := RationalEnclosure.contains_scale (2 : ℚ)
    (LRUpperKHistoricalACAD.eValue_sound hvalid hcoordinate)
  have hdiv := RationalEnclosure.contains_div hvalid.base.sPositive
    hscaled (sValue_sound hcoordinate)
  simpa [ePartialSI] using hdiv

private theorem ePartialKI_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (ePartialKI box).Contains
      (lrCertificateE (lrDeterminantKChartDecode coordinate) /
        coordinate.k) := by
  have hdiv := RationalEnclosure.contains_div hvalid.base.ratioPositive
    (LRUpperKHistoricalACAD.eValue_sound hvalid hcoordinate)
    (ratioValue_sound hcoordinate)
  simpa [ePartialKI] using hdiv

private theorem pointZero_sound :
    (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
  simpa using RationalEnclosure.contains_point (0 : ℚ)

/-! ## Sound `y0` partial ledgers -/

theorem aY0Partials_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (aY0Partials terms box payload)
      (aY0ExactPartials coordinate) := by
  have hfixedRaw := fixedYPartialSI_sound terms
    hvalid.sharp.auxiliary.qPrimeAtSCheck
    hvalid.sharp.auxiliary.qPrimeAtBCheck
    (sValue_sound hvalid.coordinateMem)
    (LRUpperKHistoricalACAD.y0Value_sound
      hvalid.sharp hvalid.coordinateMem)
    (y0BValue_sound hvalid.sharp hvalid.coordinateMem)
    hvalid.oneMinusY0Lower hvalid.sPhysical hvalid.y0Physical
  have hfixed :
      (fixedYPartialSI terms box payload).Contains
        (fixedYPartialS coordinate.s
          (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
    simpa [fixedYPartialS] using hfixedRaw
  have hmovingRaw := movingYCoefficientI_sound terms
    hvalid.sharp.auxiliary.qPrimeAtBCheck
    (sValue_sound hvalid.coordinateMem)
    (LRUpperKHistoricalACAD.y0Value_sound
      hvalid.sharp hvalid.coordinateMem)
    (y0BValue_sound hvalid.sharp hvalid.coordinateMem)
    hvalid.sharp.base.sPositive.le hvalid.oneMinusSLower
    hvalid.oneMinusY0Lower
  have hmoving :
      (movingYCoefficientI terms box payload).Contains
        (movingYCoefficient coordinate.s
          (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
    simpa [movingYCoefficient] using hmovingRaw
  have hyS := LRUpperKHistoricalACAD.yPartialSI_sound
    hvalid.sharp hvalid.coordinateMem
  have hyK := LRUpperKHistoricalACAD.yPartialKI_sound
    hvalid.sharp hvalid.coordinateMem
  have hyH := LRUpperKHistoricalACAD.yPartialHI_sound
    hvalid.sharp hvalid.coordinateMem
  have hS := RationalEnclosure.contains_add hfixed
    (RationalEnclosure.contains_mul hmoving hyS)
  have hK := RationalEnclosure.contains_mul hmoving hyK
  have hH := RationalEnclosure.contains_mul hmoving hyH
  simpa [ContainsPartials, aY0Partials, aY0ExactPartials] using
    (show
      (aY0Partials terms box payload).derivS.Contains
          (aY0ExactPartials coordinate).derivS ∧
        (aY0Partials terms box payload).derivK.Contains
          (aY0ExactPartials coordinate).derivK ∧
        (aY0Partials terms box payload).derivH.Contains
          (aY0ExactPartials coordinate).derivH from
      ⟨hS, hK, hH⟩)

theorem cY0Partials_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (cY0Partials terms box payload)
      (cY0ExactPartials coordinate) := by
  have ha := aY0Partials_sound terms hvalid
  change
    (aY0Partials terms box payload).derivS.Contains
        (aY0ExactPartials coordinate).derivS ∧
      (aY0Partials terms box payload).derivK.Contains
        (aY0ExactPartials coordinate).derivK ∧
      (aY0Partials terms box payload).derivH.Contains
        (aY0ExactPartials coordinate).derivH at ha
  have hqS := LRUpperKHistoricalACAD.qPartialSI_sound terms
    hvalid.sharp hvalid.coordinateMem
  have hqK := LRUpperKHistoricalACAD.qPartialKI_sound terms
    hvalid.sharp hvalid.coordinateMem
  have hqH := LRUpperKHistoricalACAD.qPartialHI_sound_exact terms
    hvalid.sharp hvalid.coordinateMem
  have hS := RationalEnclosure.contains_sub ha.1 hqS
  have hK := RationalEnclosure.contains_sub ha.2.1 hqK
  have hH := RationalEnclosure.contains_sub ha.2.2 hqH
  simpa [ContainsPartials, cY0Partials, cY0ExactPartials] using
    (show
      (cY0Partials terms box payload).derivS.Contains
          (cY0ExactPartials coordinate).derivS ∧
        (cY0Partials terms box payload).derivK.Contains
          (cY0ExactPartials coordinate).derivK ∧
        (cY0Partials terms box payload).derivH.Contains
          (cY0ExactPartials coordinate).derivH from
      ⟨hS, hK, hH⟩)

/-! ## Sound `e` partial ledgers -/

theorem aEPartials_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (aEPartials terms box payload)
      (aEExactPartials coordinate) := by
  have hfixedRaw := fixedEPartialSI_sound terms
    hvalid.sharp.auxiliary.qPrimeAtSCheck
    (omegaEQPrimeAtBValueCheck hvalid.sharp)
    (sValue_sound hvalid.coordinateMem)
    (LRUpperKHistoricalACAD.eValue_sound
      hvalid.sharp hvalid.coordinateMem)
    (eBValue_sound hvalid.sharp hvalid.coordinateMem)
    hvalid.oneMinusELower hvalid.sPhysical hvalid.ePhysical
  have hfixed :
      (fixedEPartialSI terms box payload).Contains
        (fixedYPartialS coordinate.s
          (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
    simpa [fixedYPartialS] using hfixedRaw
  have hmovingRaw := movingECoefficientI_sound terms
    (omegaEQPrimeAtBValueCheck hvalid.sharp)
    (sValue_sound hvalid.coordinateMem)
    (LRUpperKHistoricalACAD.eValue_sound
      hvalid.sharp hvalid.coordinateMem)
    (eBValue_sound hvalid.sharp hvalid.coordinateMem)
    hvalid.sharp.base.sPositive.le hvalid.oneMinusSLower
    hvalid.oneMinusELower
  have hmoving :
      (movingECoefficientI terms box payload).Contains
        (movingYCoefficient coordinate.s
          (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
    simpa [movingYCoefficient] using hmovingRaw
  have heS := ePartialSI_sound hvalid.sharp hvalid.coordinateMem
  have heK := ePartialKI_sound hvalid.sharp hvalid.coordinateMem
  have hS := RationalEnclosure.contains_add hfixed
    (RationalEnclosure.contains_mul hmoving heS)
  have hK := RationalEnclosure.contains_mul hmoving heK
  simpa [ContainsPartials, aEPartials, aEExactPartials] using
    (show
      (aEPartials terms box payload).derivS.Contains
          (aEExactPartials coordinate).derivS ∧
        (aEPartials terms box payload).derivK.Contains
          (aEExactPartials coordinate).derivK ∧
        (aEPartials terms box payload).derivH.Contains
          (aEExactPartials coordinate).derivH from
      ⟨hS, hK, pointZero_sound⟩)

theorem cEPartials_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (cEPartials terms box payload)
      (cEExactPartials coordinate) := by
  have ha := aEPartials_sound terms hvalid
  change
    (aEPartials terms box payload).derivS.Contains
        (aEExactPartials coordinate).derivS ∧
      (aEPartials terms box payload).derivK.Contains
        (aEExactPartials coordinate).derivK ∧
      (aEPartials terms box payload).derivH.Contains
        (aEExactPartials coordinate).derivH at ha
  have hqPrime := qPrimeEI_sound terms
    hvalid.sharp hvalid.coordinateMem
  have heS := ePartialSI_sound hvalid.sharp hvalid.coordinateMem
  have heK := ePartialKI_sound hvalid.sharp hvalid.coordinateMem
  have hS := RationalEnclosure.contains_sub ha.1
    (RationalEnclosure.contains_mul hqPrime heS)
  have hK := RationalEnclosure.contains_sub ha.2.1
    (RationalEnclosure.contains_mul hqPrime heK)
  simpa [ContainsPartials, cEPartials, cEExactPartials] using
    (show
      (cEPartials terms box payload).derivS.Contains
          (cEExactPartials coordinate).derivS ∧
        (cEPartials terms box payload).derivK.Contains
          (cEExactPartials coordinate).derivK ∧
        (cEPartials terms box payload).derivH.Contains
          (cEExactPartials coordinate).derivH from
      ⟨hS, hK, pointZero_sound⟩)

/-! ## Primitive-derivative corollaries -/

theorem aY0Partials_primitive_sound (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (aY0Partials terms box payload)
      (aY0PrimitivePartials coordinate) := by
  rw [← aY0ExactPartials_eq_primitive]
  exact aY0Partials_sound terms hvalid

theorem cY0Partials_primitive_sound (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (cY0Partials terms box payload)
      (cY0PrimitivePartials coordinate) := by
  rw [← cY0ExactPartials_eq_primitive]
  exact cY0Partials_sound terms hvalid

theorem aEPartials_primitive_sound (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (aEPartials terms box payload)
      (aEPrimitivePartials coordinate) := by
  rw [← aEExactPartials_eq_primitive]
  exact aEPartials_sound terms hvalid

theorem cEPartials_primitive_sound (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate) :
    ContainsPartials (cEPartials terms box payload)
      (cEPrimitivePartials coordinate) := by
  rw [← cEExactPartials_eq_primitive]
  exact cEPartials_sound terms hvalid

/-! ## Attaching separately proved value enclosures -/

theorem aY0ProjectedAD_sound_of_value (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate)
    (hvalue : (aY0ValueI terms box payload).Contains
      (aPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))) :
    (aY0ProjectedAD terms box payload).Contains
      (aPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))
      (aY0PrimitivePartials coordinate).derivS
      (aY0PrimitivePartials coordinate).derivK
      (aY0PrimitivePartials coordinate).derivH := by
  have hp := aY0Partials_primitive_sound terms hvalid
  simpa [aY0ProjectedAD, ContainsPartials, IntervalAD.Contains] using
    And.intro hvalue hp

theorem cY0ProjectedAD_sound_of_value (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate)
    (hvalue : (cY0ValueI terms box payload).Contains
      (cPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))) :
    (cY0ProjectedAD terms box payload).Contains
      (cPrimitive coordinate.s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))
      (cY0PrimitivePartials coordinate).derivS
      (cY0PrimitivePartials coordinate).derivK
      (cY0PrimitivePartials coordinate).derivH := by
  have hp := cY0Partials_primitive_sound terms hvalid
  simpa [cY0ProjectedAD, ContainsPartials, IntervalAD.Contains] using
    And.intro hvalue hp

theorem aEProjectedAD_sound_of_value (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate)
    (hvalue :
      (LRUpperKReplayCertificate.aESKAD terms box payload.base).value.Contains
        (aPrimitive coordinate.s
          (lrCertificateE (lrDeterminantKChartDecode coordinate)))) :
    (aEProjectedAD terms box payload).Contains
      (aPrimitive coordinate.s
        (lrCertificateE (lrDeterminantKChartDecode coordinate)))
      (aEPrimitivePartials coordinate).derivS
      (aEPrimitivePartials coordinate).derivK
      (aEPrimitivePartials coordinate).derivH := by
  have hp := aEPartials_primitive_sound terms hvalid
  simpa [aEProjectedAD, ContainsPartials, IntervalAD.Contains] using
    And.intro hvalue hp

theorem cEProjectedAD_sound_of_value (terms : ℕ)
    {box : CertificateBox} {payload : Payload}
    {coordinate : CertificatePoint}
    (hvalid : PartialsValid terms box payload coordinate)
    (hvalue :
      (LRUpperKReplayCertificate.cESKAD terms box payload.base).value.Contains
        (cPrimitive coordinate.s
          (lrCertificateE (lrDeterminantKChartDecode coordinate)))) :
    (cEProjectedAD terms box payload).Contains
      (cPrimitive coordinate.s
        (lrCertificateE (lrDeterminantKChartDecode coordinate)))
      (cEPrimitivePartials coordinate).derivS
      (cEPrimitivePartials coordinate).derivK
      (cEPrimitivePartials coordinate).derivH := by
  have hp := cEPartials_primitive_sound terms hvalid
  simpa [cEProjectedAD, ContainsPartials, IntervalAD.Contains] using
    And.intro hvalue hp

end LRUpperKHistoricalACPartialsSoundness
end CourtadeKumar
