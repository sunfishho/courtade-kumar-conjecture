import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACCornerSoundness

/-!
# Explicit scalar-corner payloads for upper-`K` replay

The historical evaluator reconstructs each scalar `A/C` endpoint payload.
Large definitional reductions through that reconstruction overflow the process
stack.  These definitions instead accept the same exact certificate data as a
literal and expose a balanced checker whose soundness is proved by the
existing scalar and monotonicity theorems.
-/

namespace CourtadeKumar
namespace LRUpperKExplicitCornerPayload

open Set
open LRUpperKReplayCertificate
open LRUpperKHistoricalACValues

abbrev ScalarPayload := LRUpperKHistoricalACValues.ScalarPayload

structure Pair where
  lower : ScalarPayload
  upper : ScalarPayload

/-- Explicit historical `A` hull.  Its lower endpoint is evaluated at
`(sHi,yLo)` and its upper endpoint at `(sLo,yHi)`. -/
def aCornerI (terms : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) (payload : Pair) : RationalEnclosure :=
  let lower := aScalarI terms box.sHi yI.lower payload.lower
  let upper := aScalarI terms box.sLo yI.upper payload.upper
  ⟨lower.lower, upper.upper⟩

def aCornerCheck (box : CertificateBox)
    (yI : RationalEnclosure) (payload : Pair) : Bool :=
  scalarCheck box.sHi yI.lower payload.lower &&
    scalarCheck box.sLo yI.upper payload.upper

/-- Explicit historical `C` hull.  Its lower endpoint is evaluated at
`(sHi,yHi)` and its upper endpoint at `(sLo,yLo)`. -/
def cCornerI (terms : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) (payload : Pair) : RationalEnclosure :=
  let lower := cScalarI terms box.sHi yI.upper payload.lower
  let upper := cScalarI terms box.sLo yI.lower payload.upper
  ⟨lower.lower, upper.upper⟩

def cCornerCheck (box : CertificateBox)
    (yI : RationalEnclosure) (payload : Pair) : Bool :=
  scalarCheck box.sHi yI.upper payload.lower &&
    scalarCheck box.sLo yI.lower payload.upper

/-- Four explicit corner pairs: `A(y0)`, `C(y0)`, `A(e)`, and `C(e)`. -/
structure Payload where
  aY0 : Pair
  cY0 : Pair
  aE : Pair
  cE : Pair

def all4 (a b c d : Bool) : Bool := (a && b) && (c && d)

/-- Balanced checker for all eight scalar endpoint payloads. -/
def check (box : CertificateBox) (payload : Payload) : Bool :=
  all4
    (aCornerCheck box (y0AD box).value payload.aY0)
    (cCornerCheck box (y0AD box).value payload.cY0)
    (aCornerCheck box (eAD box).value payload.aE)
    (cCornerCheck box (eAD box).value payload.cE)

structure Checked (box : CertificateBox) (payload : Payload) : Prop where
  aY0 : aCornerCheck box (y0AD box).value payload.aY0 = true
  cY0 : cCornerCheck box (y0AD box).value payload.cY0 = true
  aE : aCornerCheck box (eAD box).value payload.aE = true
  cE : cCornerCheck box (eAD box).value payload.cE = true

theorem checked_of_check {box : CertificateBox} {payload : Payload}
    (hcheck : check box payload = true) : Checked box payload := by
  have hparts :
      (aCornerCheck box (y0AD box).value payload.aY0 = true ∧
        cCornerCheck box (y0AD box).value payload.cY0 = true) ∧
      (aCornerCheck box (eAD box).value payload.aE = true ∧
        cCornerCheck box (eAD box).value payload.cE = true) := by
    simpa [check, all4] using hcheck
  exact ⟨hparts.1.1, hparts.1.2, hparts.2.1, hparts.2.2⟩

/-! ## Sound explicit corner hulls -/

theorem aCornerI_sound (terms : ℕ)
    {box : CertificateBox} {yI : RationalEnclosure} {payload : Pair}
    {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (yI.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (yI.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : yI.Contains y)
    (hcheck : aCornerCheck box yI payload = true) :
    (aCornerI terms box yI payload).Contains
      (LRUpperKReplayCertificate.aPrimitive s y) := by
  have hchecks :
      scalarCheck box.sHi yI.lower payload.lower = true ∧
        scalarCheck box.sLo yI.upper payload.upper = true := by
    simpa [aCornerCheck] using hcheck
  have hLower := LRUpperKHistoricalACValues.aScalarI_sound terms hchecks.1
  have hUpper := LRUpperKHistoricalACValues.aScalarI_sound terms hchecks.2
  have hCorners := LRUpperKReplayCertificate.aPrimitive_corner_bounds
    hsLo hs hsHi hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  change
    ((aScalarI terms box.sHi yI.lower payload.lower).lower : ℝ) ≤
        LRUpperKReplayCertificate.aPrimitive s y ∧
      LRUpperKReplayCertificate.aPrimitive s y ≤
        ((aScalarI terms box.sLo yI.upper payload.upper).upper : ℝ)
  exact ⟨hLower.1.trans hCorners.1, hCorners.2.trans hUpper.2⟩

theorem cCornerI_sound (terms : ℕ)
    {box : CertificateBox} {yI : RationalEnclosure} {payload : Pair}
    {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (yI.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (yI.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : yI.Contains y)
    (hcheck : cCornerCheck box yI payload = true) :
    (cCornerI terms box yI payload).Contains
      (LRUpperKReplayCertificate.cPrimitive s y) := by
  have hchecks :
      scalarCheck box.sHi yI.upper payload.lower = true ∧
        scalarCheck box.sLo yI.lower payload.upper = true := by
    simpa [cCornerCheck] using hcheck
  have hLower := LRUpperKHistoricalACValues.cScalarI_sound terms hchecks.1
  have hUpper := LRUpperKHistoricalACValues.cScalarI_sound terms hchecks.2
  have hCorners := LRUpperKReplayCertificate.cPrimitive_corner_bounds
    hsLo hs hsHi hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  change
    ((cScalarI terms box.sHi yI.upper payload.lower).lower : ℝ) ≤
        LRUpperKReplayCertificate.cPrimitive s y ∧
      LRUpperKReplayCertificate.cPrimitive s y ≤
        ((cScalarI terms box.sLo yI.lower payload.upper).upper : ℝ)
  exact ⟨hLower.1.trans hCorners.1, hCorners.2.trans hUpper.2⟩

end LRUpperKExplicitCornerPayload
end CourtadeKumar
