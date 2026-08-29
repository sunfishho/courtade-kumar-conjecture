import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalEvaluatorAssembly
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalThreeCoordinateBase

/-!
# Exact target-jet bridge for the historical upper-`K` evaluator

This file supplies the real-algebra side of the historical evaluator
interface.  Each ordinary component and each sharp `A/C` component is given
its exact value and its three `(s,K,h)` derivatives at a chart point.  The
main theorem identifies their `evaluateJet` assembly with the genuine CK
target jet.

There is no interval arithmetic, executable decision procedure, or analytic
approximation in this module.  The only hypotheses are the three nonvanishing
facts needed by the exact cancellation identities and quotient algebra.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalTargetJetBridge

open LRUpperKReplayCertificate
open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKHistoricalEvaluatorAssembly

/-! ## Decoded chart point and its exact coordinate velocities -/

def rawPoint (coordinate : CertificatePoint) : CertificatePoint :=
  lrDeterminantKChartDecode coordinate

def chartES (coordinate : CertificatePoint) : ℝ :=
  (rawPoint coordinate).k + (rawPoint coordinate).s * coordinate.k

def chartEK (coordinate : CertificatePoint) : ℝ :=
  (rawPoint coordinate).s * coordinate.s

def chartY0S (coordinate : CertificatePoint) : ℝ :=
  (rawPoint coordinate).chi * chartES coordinate

def chartY0K (coordinate : CertificatePoint) : ℝ :=
  (rawPoint coordinate).chi * chartEK coordinate

def chartY0H (coordinate : CertificatePoint) : ℝ :=
  2 * coordinate.chi * lrCertificateE (rawPoint coordinate)

def chartXS (coordinate : CertificatePoint) : ℝ :=
  -((rawPoint coordinate).chi * chartES coordinate)

def chartXK (coordinate : CertificatePoint) : ℝ :=
  -((rawPoint coordinate).chi * chartEK coordinate)

def chartXH (coordinate : CertificatePoint) : ℝ :=
  -(2 * coordinate.chi * lrCertificateE (rawPoint coordinate))

noncomputable def chartVS (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawPoint coordinate)
    (chartES coordinate) (chartXS coordinate)

noncomputable def chartVK (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawPoint coordinate)
    (chartEK coordinate) (chartXK coordinate)

noncomputable def chartVH (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawPoint coordinate) 0 (chartXH coordinate)

/-! ## Exact component jets -/

noncomputable def eJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateE (rawPoint coordinate)
  derivS := chartES coordinate
  derivK := chartEK coordinate
  derivH := 0

noncomputable def vJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateV (rawPoint coordinate)
  derivS := chartVS coordinate
  derivK := chartVK coordinate
  derivH := chartVH coordinate

noncomputable def bJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateBFlow (rawPoint coordinate)
  derivS := lrCertificateBFlowDeriv (rawPoint coordinate)
    1 (chartES coordinate) (chartVS coordinate)
  derivK := lrCertificateBFlowDeriv (rawPoint coordinate)
    0 (chartEK coordinate) (chartVK coordinate)
  derivH := lrCertificateBFlowDeriv (rawPoint coordinate)
    0 0 (chartVH coordinate)

noncomputable def d1Jet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantD1 (rawPoint coordinate)
  derivS := d1Deriv (rawPoint coordinate) 1 (chartES coordinate)
  derivK := d1Deriv (rawPoint coordinate) 0 (chartEK coordinate)
  derivH := d1Deriv (rawPoint coordinate) 0 0

noncomputable def g0Jet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateG0 (lrCertificateV (rawPoint coordinate))
  derivS := lrCertificateG0Prime (lrCertificateV (rawPoint coordinate)) *
    chartVS coordinate
  derivK := lrCertificateG0Prime (lrCertificateV (rawPoint coordinate)) *
    chartVK coordinate
  derivH := lrCertificateG0Prime (lrCertificateV (rawPoint coordinate)) *
    chartVH coordinate

noncomputable def aY0Jet (coordinate : CertificatePoint) : Jet3 where
  value := aPrimitive (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate))
  derivS := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 1 (chartY0S coordinate)
  derivK := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 0 (chartY0K coordinate)
  derivH := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 0 (chartY0H coordinate)

noncomputable def aEJet (coordinate : CertificatePoint) : Jet3 where
  value := aPrimitive (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate))
  derivS := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 1 (chartES coordinate)
  derivK := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 0 (chartEK coordinate)
  derivH := aPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 0 0

noncomputable def cY0Jet (coordinate : CertificatePoint) : Jet3 where
  value := cPrimitive (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate))
  derivS := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 1 (chartY0S coordinate)
  derivK := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 0 (chartY0K coordinate)
  derivH := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateY0 (rawPoint coordinate)) 0 (chartY0H coordinate)

noncomputable def cEJet (coordinate : CertificatePoint) : Jet3 where
  value := cPrimitive (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate))
  derivS := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 1 (chartES coordinate)
  derivK := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 0 (chartEK coordinate)
  derivH := cPrimitiveDeriv (rawPoint coordinate).s
    (lrCertificateE (rawPoint coordinate)) 0 0

noncomputable def kappaJet (coordinate : CertificatePoint) : Jet3 where
  value := kappaV (lrCertificateV (rawPoint coordinate))
  derivS := kappaDeriv (lrCertificateV (rawPoint coordinate))
    (chartVS coordinate)
  derivK := kappaDeriv (lrCertificateV (rawPoint coordinate))
    (chartVK coordinate)
  derivH := kappaDeriv (lrCertificateV (rawPoint coordinate))
    (chartVH coordinate)

noncomputable def deltaJet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantDelta (rawPoint coordinate)
  derivS := deltaDeriv (rawPoint coordinate)
    (chartXS coordinate) (chartVS coordinate)
  derivK := deltaDeriv (rawPoint coordinate)
    (chartXK coordinate) (chartVK coordinate)
  derivH := deltaDeriv (rawPoint coordinate)
    (chartXH coordinate) (chartVH coordinate)

noncomputable def wJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateW (rawPoint coordinate)
  derivS := lrCertificateOmegaDeriv (rawPoint coordinate).s 0 1 0
  derivK := lrCertificateOmegaDeriv (rawPoint coordinate).s 0 0 0
  derivH := lrCertificateOmegaDeriv (rawPoint coordinate).s 0 0 0

/-! ## Exact target jets for the two cancellation-aware inner expressions -/

noncomputable def baseDirectionalDeriv
    (point : CertificatePoint) (s' y0' e' x' v' : ℝ) : ℝ :=
  psiDeriv point s' y0' e' v' -
      lrCertificateGShapeDeriv point y0' e' v' +
    4 * (deltaDeriv point x' v' * lrCertificateW point +
      lrDeterminantDelta point *
        lrCertificateOmegaDeriv point.s 0 s' 0)

noncomputable def psiTargetJet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantPsi (rawPoint coordinate)
  derivS := psiDeriv (rawPoint coordinate) 1
    (chartY0S coordinate) (chartES coordinate) (chartVS coordinate)
  derivK := psiDeriv (rawPoint coordinate) 0
    (chartY0K coordinate) (chartEK coordinate) (chartVK coordinate)
  derivH := psiDeriv (rawPoint coordinate) 0
    (chartY0H coordinate) 0 (chartVH coordinate)

noncomputable def baseTargetJet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantPsi (rawPoint coordinate) -
      lrCertificateGShape (rawPoint coordinate) +
    4 * lrDeterminantDelta (rawPoint coordinate) *
      lrCertificateW (rawPoint coordinate)
  derivS := baseDirectionalDeriv (rawPoint coordinate) 1
    (chartY0S coordinate) (chartES coordinate)
    (chartXS coordinate) (chartVS coordinate)
  derivK := baseDirectionalDeriv (rawPoint coordinate) 0
    (chartY0K coordinate) (chartEK coordinate)
    (chartXK coordinate) (chartVK coordinate)
  derivH := baseDirectionalDeriv (rawPoint coordinate) 0
    (chartY0H coordinate) 0
    (chartXH coordinate) (chartVH coordinate)

/-! ## Two reusable cancellation identities for derivatives -/

theorem psiDeriv_eq_aPrimitives
    (point : CertificatePoint) (s' y0' e' v' : ℝ)
    (hv : lrCertificateV point ≠ 0)
    (honePlus : 1 + lrCertificateV point ≠ 0) :
    psiDeriv point s' y0' e' v' =
      lrCertificateG0Prime (lrCertificateV point) * v' +
        aPrimitiveDeriv point.s (lrCertificateY0 point) s' y0' +
        ((aPrimitiveDeriv point.s (lrCertificateE point) s' e' *
              lrCertificateV point -
            aPrimitive point.s (lrCertificateE point) * v') /
          lrCertificateV point ^ 2 +
          (kappaDeriv (lrCertificateV point) v' *
              lrCertificateW point +
            kappaV (lrCertificateV point) *
              lrCertificateOmegaDeriv point.s 0 s' 0)) := by
  simp [psiDeriv, aPrimitiveDeriv_identity, aPrimitive,
    kappaV, kappaDeriv, lrCertificateGShapeDeriv,
    lrCertificateGShapeValueDeriv, lrCertificatePWDeriv,
    lrCertificatePWValueDeriv, lrCertificateW]
  field_simp [hv, honePlus]
  ring

theorem baseDirectionalDeriv_eq_cPrimitives
    (point : CertificatePoint) (s' y0' e' x' v' : ℝ)
    (hv : lrCertificateV point ≠ 0)
    (honePlus : 1 + lrCertificateV point ≠ 0) :
    baseDirectionalDeriv point s' y0' e' x' v' =
      cPrimitiveDeriv point.s (lrCertificateY0 point) s' y0' +
        ((cPrimitiveDeriv point.s (lrCertificateE point) s' e' *
              lrCertificateV point -
            cPrimitive point.s (lrCertificateE point) * v') /
          lrCertificateV point ^ 2) +
        ((kappaDeriv (lrCertificateV point) v' +
              4 * deltaDeriv point x' v') * lrCertificateW point +
          (kappaV (lrCertificateV point) +
              4 * lrDeterminantDelta point) *
            lrCertificateOmegaDeriv point.s 0 s' 0) := by
  simp [baseDirectionalDeriv, psiDeriv, aPrimitiveDeriv_identity,
    cPrimitive, cPrimitiveDeriv, kappaV, kappaDeriv,
    lrCertificateGShapeDeriv, lrCertificateGShapeValueDeriv,
    lrCertificatePWDeriv, lrCertificatePWValueDeriv, lrCertificateW]
  field_simp [hv, honePlus]
  ring

/-! ## The sharp inner jets equal the production target jets -/

theorem psiJet_eq_target (coordinate : CertificatePoint)
    (hv : lrCertificateV (rawPoint coordinate) ≠ 0)
    (honePlus : 1 + lrCertificateV (rawPoint coordinate) ≠ 0) :
    psiJet (g0Jet coordinate) (aY0Jet coordinate) (aEJet coordinate)
        (vJet coordinate) (kappaJet coordinate) (wJet coordinate) =
      psiTargetJet coordinate := by
  apply Jet3.ext
  · have hid := psi_eq_aPrimitives
      (point := rawPoint coordinate) hv honePlus
    simp [psiJet, Jet3.add, Jet3.mul, Jet3.div,
      g0Jet, aY0Jet, aEJet, vJet, kappaJet, wJet,
      psiTargetJet]
    rw [hid]
    ring
  · simp [psiJet, Jet3.add, Jet3.mul, Jet3.div,
      g0Jet, aY0Jet, aEJet, vJet, kappaJet, wJet,
      psiTargetJet]
    rw [psiDeriv_eq_aPrimitives (rawPoint coordinate) 1
      (chartY0S coordinate) (chartES coordinate) (chartVS coordinate)
      hv honePlus]
  · simp [psiJet, Jet3.add, Jet3.mul, Jet3.div,
      g0Jet, aY0Jet, aEJet, vJet, kappaJet, wJet,
      psiTargetJet]
    rw [psiDeriv_eq_aPrimitives (rawPoint coordinate) 0
      (chartY0K coordinate) (chartEK coordinate) (chartVK coordinate)
      hv honePlus]
  · simp [psiJet, Jet3.add, Jet3.mul, Jet3.div,
      g0Jet, aY0Jet, aEJet, vJet, kappaJet, wJet,
      psiTargetJet]
    rw [psiDeriv_eq_aPrimitives (rawPoint coordinate) 0
      (chartY0H coordinate) 0 (chartVH coordinate) hv honePlus]

theorem baseJet_eq_target (coordinate : CertificatePoint)
    (hv : lrCertificateV (rawPoint coordinate) ≠ 0)
    (honePlus : 1 + lrCertificateV (rawPoint coordinate) ≠ 0) :
    baseJet (cY0Jet coordinate) (cEJet coordinate) (vJet coordinate)
        (kappaJet coordinate) (deltaJet coordinate) (wJet coordinate) =
      baseTargetJet coordinate := by
  apply Jet3.ext
  · have hid := psi_sub_gShape_eq_cPrimitives
      (point := rawPoint coordinate) hv honePlus
    simp [baseJet, Jet3.add, Jet3.mul, Jet3.div,
      cY0Jet, cEJet, vJet, kappaJet, deltaJet, wJet,
      baseTargetJet]
    rw [hid]
    ring
  · simp [baseJet, Jet3.add, Jet3.mul, Jet3.div,
      cY0Jet, cEJet, vJet, kappaJet, deltaJet, wJet,
      baseTargetJet]
    rw [baseDirectionalDeriv_eq_cPrimitives (rawPoint coordinate) 1
      (chartY0S coordinate) (chartES coordinate)
      (chartXS coordinate) (chartVS coordinate) hv honePlus]
  · simp [baseJet, Jet3.add, Jet3.mul, Jet3.div,
      cY0Jet, cEJet, vJet, kappaJet, deltaJet, wJet,
      baseTargetJet]
    rw [baseDirectionalDeriv_eq_cPrimitives (rawPoint coordinate) 0
      (chartY0K coordinate) (chartEK coordinate)
      (chartXK coordinate) (chartVK coordinate) hv honePlus]
  · simp [baseJet, Jet3.add, Jet3.mul, Jet3.div,
      cY0Jet, cEJet, vJet, kappaJet, deltaJet, wJet,
      baseTargetJet]
    rw [baseDirectionalDeriv_eq_cPrimitives (rawPoint coordinate) 0
      (chartY0H coordinate) 0
      (chartXH coordinate) (chartVH coordinate) hv honePlus]

/-! ## Final exact target bridge -/

theorem evaluateJet_eq_associationTarget (coordinate : CertificatePoint)
    (hv : lrCertificateV (rawPoint coordinate) ≠ 0)
    (honePlus : 1 + lrCertificateV (rawPoint coordinate) ≠ 0) :
    evaluateJet
        (bJet coordinate) (d1Jet coordinate) (g0Jet coordinate)
        (aY0Jet coordinate) (aEJet coordinate)
        (cY0Jet coordinate) (cEJet coordinate)
        (vJet coordinate) (kappaJet coordinate) (deltaJet coordinate)
        (wJet coordinate) (eJet coordinate) =
      upperKAssociationTargetJet coordinate := by
  unfold evaluateJet
  rw [psiJet_eq_target coordinate hv honePlus,
    baseJet_eq_target coordinate hv honePlus]
  apply Jet3.ext
  · simpa [historicalAssociationJet, Jet3.add, Jet3.mul, Jet3.div,
      bJet, baseTargetJet, d1Jet, psiTargetJet, eJet,
      upperKAssociationTargetJet] using
      historicalAssociation_value_eq_upperKTarget (rawPoint coordinate)
  · simp [historicalAssociationJet, Jet3.add, Jet3.mul, Jet3.div,
      historicalAssociationDerivative, upperKAssociationTargetJet,
      upperKAssociationRawDerivative, bJet, baseTargetJet, d1Jet,
      psiTargetJet, eJet, baseDirectionalDeriv,
      chartES, chartY0S, chartXS, chartVS, rawPoint]
  · simp [historicalAssociationJet, Jet3.add, Jet3.mul, Jet3.div,
      historicalAssociationDerivative, upperKAssociationTargetJet,
      upperKAssociationRawDerivative, bJet, baseTargetJet, d1Jet,
      psiTargetJet, eJet, baseDirectionalDeriv,
      chartEK, chartY0K, chartXK, chartVK, rawPoint]
  · simp [historicalAssociationJet, Jet3.add, Jet3.mul, Jet3.div,
      historicalAssociationDerivative, upperKAssociationTargetJet,
      upperKAssociationRawDerivative, bJet, baseTargetJet, d1Jet,
      psiTargetJet, eJet, baseDirectionalDeriv,
      chartY0H, chartXH, chartVH, rawPoint]

/-- The exact component jets assembled by `evaluateJet` are the genuine CK
value and genuine derivatives in all three `(s,K,h)` chart coordinates. -/
theorem evaluateJet_eq_upperKTarget (coordinate : CertificatePoint)
    (hv : lrCertificateV (rawPoint coordinate) ≠ 0)
    (honePlus : 1 + lrCertificateV (rawPoint coordinate) ≠ 0)
    (he : lrCertificateE (rawPoint coordinate) ≠ 0) :
    evaluateJet
        (bJet coordinate) (d1Jet coordinate) (g0Jet coordinate)
        (aY0Jet coordinate) (aEJet coordinate)
        (cY0Jet coordinate) (cEJet coordinate)
        (vJet coordinate) (kappaJet coordinate) (deltaJet coordinate)
        (wJet coordinate) (eJet coordinate) =
      upperKTargetJet coordinate := by
  calc
    _ = upperKAssociationTargetJet coordinate :=
      evaluateJet_eq_associationTarget coordinate hv honePlus
    _ = upperKTargetJet coordinate :=
      upperKAssociationTargetJet_eq_upperKTargetJet coordinate he

end LRUpperKHistoricalTargetJetBridge
end CourtadeKumar
