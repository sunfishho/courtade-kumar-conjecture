import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACAD

/-!
# Historical monotone-corner value nodes for the upper-K A/C primitives

This module isolates sharp checked scalar values at rational `(s,y)` points,
then assembles the exact corner order used by the historical replay.  Scalar
soundness is ordinary interval arithmetic; soundness of corner selection uses
the separate `A/C` monotonicity theorem.
-/

namespace CourtadeKumar.LRUpperKHistoricalACValues

open LRUpperKReplayCertificate

def constAD (q : ℚ) : IntervalAD := IntervalAD.const q

structure ScalarPayload where
  omegaY : LROmegaADCertificate
  omegaZero : LROmegaZeroADCertificate

namespace ScalarPayload

def auto (sqrtFuel logFuel : ℕ) (s y : ℚ) : ScalarPayload :=
  let sAD := constAD s
  let yAD := constAD y
  { omegaY := LROmegaADCertificate.auto
      sqrtFuel logFuel sAD yAD
    omegaZero := LROmegaZeroADCertificate.auto sqrtFuel logFuel sAD }

end ScalarPayload

def scalarCheck (s y : ℚ) (payload : ScalarPayload) : Bool :=
  if y = 0 then true
  else payload.omegaY.check (constAD s) (constAD y) &&
    payload.omegaZero.check (constAD s)

def capLowerZero (a : RationalEnclosure) : RationalEnclosure :=
  ⟨max 0 a.lower, a.upper⟩

def capUpperZero (a : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower, min 0 a.upper⟩

/-- Cancellation-free point enclosure of
`A_s(y)=Q(b)-s(1-y)Q'(b)-omega_s(0)`. -/
def aScalarI (terms : ℕ) (s y : ℚ)
    (payload : ScalarPayload) : RationalEnclosure :=
  if y = 0 then RationalEnclosure.point 0
  else
    let qB := payload.omegaY.qAtB.value.enclosure terms
    let qPrimeB := payload.omegaY.qPrimeAtB.value.enclosure terms
    let correction := RationalEnclosure.mul
      (RationalEnclosure.point (s * (1 - y))) qPrimeB
    let w := (payload.omegaZero.evaluate terms (constAD s)).value
    RationalEnclosure.sub (RationalEnclosure.sub qB correction) w

/-- Point enclosure of `C_s(y)=omega_s(y)-omega_s(0)`. -/
def cScalarI (terms : ℕ) (s y : ℚ)
    (payload : ScalarPayload) : RationalEnclosure :=
  if y = 0 then RationalEnclosure.point 0
  else
    let omegaY :=
      (payload.omegaY.evaluate terms (constAD s) (constAD y)).value
    let w := (payload.omegaZero.evaluate terms (constAD s)).value
    RationalEnclosure.sub omegaY w

def aAutoI (terms sqrtFuel logFuel : ℕ) (s y : ℚ) : RationalEnclosure :=
  aScalarI terms s y (ScalarPayload.auto sqrtFuel logFuel s y)

def cAutoI (terms sqrtFuel logFuel : ℕ) (s y : ℚ) : RationalEnclosure :=
  cScalarI terms s y (ScalarPayload.auto sqrtFuel logFuel s y)

def scalarAutoCheck (sqrtFuel logFuel : ℕ) (s y : ℚ) : Bool :=
  scalarCheck s y (ScalarPayload.auto sqrtFuel logFuel s y)

/-- Historical corner order for a composite whose `y` range is already
enclosed by `yI`: A decreases in `s` and increases in `y`. -/
def aCornerI (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) : RationalEnclosure :=
  let lower := aAutoI terms sqrtFuel logFuel box.sHi yI.lower
  let upper := aAutoI terms sqrtFuel logFuel box.sLo yI.upper
  ⟨lower.lower, upper.upper⟩

/-- Historical corner order for C, decreasing in both `s` and `y`. -/
def cCornerI (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) : RationalEnclosure :=
  let lower := cAutoI terms sqrtFuel logFuel box.sHi yI.upper
  let upper := cAutoI terms sqrtFuel logFuel box.sLo yI.lower
  ⟨lower.lower, upper.upper⟩

def aCornerCheck (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) : Bool :=
  scalarAutoCheck sqrtFuel logFuel box.sHi yI.lower &&
    scalarAutoCheck sqrtFuel logFuel box.sLo yI.upper

def cCornerCheck (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (yI : RationalEnclosure) : Bool :=
  scalarAutoCheck sqrtFuel logFuel box.sHi yI.upper &&
    scalarAutoCheck sqrtFuel logFuel box.sLo yI.lower

end CourtadeKumar.LRUpperKHistoricalACValues
