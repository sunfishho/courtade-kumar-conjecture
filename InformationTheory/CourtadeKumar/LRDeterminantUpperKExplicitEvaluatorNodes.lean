import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitCornerEvaluator

/-!
# Factored explicit nodes for the upper-`K` evaluator

The final historical expression uses twelve interval nodes.  Serializing and
checking them independently prevents kernel reduction from traversing the
entire certificate graph in one recursive call.  This module contains only
the generic node record and propositional reassembly.
-/

namespace CourtadeKumar
namespace LRUpperKExplicitEvaluatorNodes

open LRUpperKReplayCertificate
open LRUpperKHistoricalEvaluatorAssembly

abbrev SharpPayload := LRUpperKHistoricalACAD.Payload
abbrev CornerPayload := LRUpperKExplicitCornerPayload.Payload

structure Payload where
  bFlow : IntervalAD
  d1 : IntervalAD
  g0 : IntervalAD
  aY0 : IntervalAD
  aE : IntervalAD
  cY0 : IntervalAD
  cE : IntervalAD
  v : IntervalAD
  kappa : IntervalAD
  delta : IntervalAD
  w : IntervalAD
  e : IntervalAD

def materialize (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : Payload :=
  { bFlow := bFlowAD terms box sharp.base
    d1 := d1AD terms box sharp.base
    g0 := sharp.base.g0.evaluate terms (vAD box sharp.base)
    aY0 := LRUpperKExplicitCornerEvaluator.aY0AD terms box sharp corners
    aE := LRUpperKExplicitCornerEvaluator.aEAD terms box sharp corners
    cY0 := LRUpperKExplicitCornerEvaluator.cY0AD terms box sharp corners
    cE := LRUpperKExplicitCornerEvaluator.cEAD terms box sharp corners
    v := vAD box sharp.base
    kappa := kappaAD box sharp.base
    delta := deltaAD box sharp.base
    w := wAD terms box sharp.base
    e := eAD box }

def psiAD (nodes : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add nodes.g0 nodes.aY0)
    (IntervalAD.add
      (IntervalAD.divPositive nodes.aE nodes.v)
      (IntervalAD.mul nodes.kappa nodes.w))

def baseAD (nodes : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add nodes.cY0
      (IntervalAD.divPositive nodes.cE nodes.v))
    (IntervalAD.mul
      (IntervalAD.add nodes.kappa
        (IntervalAD.mul (IntervalAD.const 4) nodes.delta))
      nodes.w)

def evaluateAD (nodes : Payload) : IntervalAD :=
  historicalAssociationAD nodes.bFlow (baseAD nodes) nodes.d1
    (psiAD nodes) nodes.e

theorem materialize_bFlow (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) :
    (materialize terms box sharp corners).bFlow =
      bFlowAD terms box sharp.base := rfl

/-- Once the twelve separately checked nodes are identified, the factored
evaluator is definitionally the explicit-corner evaluator. -/
theorem evaluateAD_eq_of_nodes (terms : ℕ) {box : CertificateBox}
    {sharp : SharpPayload} {corners : CornerPayload} {nodes : Payload}
    (hbFlow : nodes.bFlow = bFlowAD terms box sharp.base)
    (hd1 : nodes.d1 = d1AD terms box sharp.base)
    (hg0 : nodes.g0 = sharp.base.g0.evaluate terms (vAD box sharp.base))
    (haY0 : nodes.aY0 =
      LRUpperKExplicitCornerEvaluator.aY0AD terms box sharp corners)
    (haE : nodes.aE =
      LRUpperKExplicitCornerEvaluator.aEAD terms box sharp corners)
    (hcY0 : nodes.cY0 =
      LRUpperKExplicitCornerEvaluator.cY0AD terms box sharp corners)
    (hcE : nodes.cE =
      LRUpperKExplicitCornerEvaluator.cEAD terms box sharp corners)
    (hv : nodes.v = vAD box sharp.base)
    (hkappa : nodes.kappa = kappaAD box sharp.base)
    (hdelta : nodes.delta = deltaAD box sharp.base)
    (hw : nodes.w = wAD terms box sharp.base)
    (he : nodes.e = eAD box) :
    evaluateAD nodes =
      LRUpperKExplicitCornerEvaluator.evaluateAD terms box sharp corners := by
  unfold evaluateAD psiAD baseAD
  rw [hbFlow, hd1, hg0, haY0, haE, hcY0, hcE, hv, hkappa, hdelta, hw, he]
  rfl

end LRUpperKExplicitEvaluatorNodes
end CourtadeKumar
