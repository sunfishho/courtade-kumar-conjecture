import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitCornerEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantUpperKEnclosureCovers

/-!
# Coarse midpoint certificates for the explicit upper-K evaluator

The evaluator can produce enormous normalized rationals.  A final midpoint
certificate does not need to repeat them: it may use small rational outer
bounds, provided ordinary kernel arithmetic proves that they cover the exact
evaluator intervals.  This module supplies that semantic adapter.
-/

namespace CourtadeKumar
namespace LRUpperKMidpointCoarsening

open LRUpperKHistoricalOpenMidpointLeaf

/-- Componentwise outer containment for interval-AD nodes. -/
def ADCovers (outer inner : IntervalAD) : Prop :=
  Covers outer.value inner.value ∧
    Covers outer.derivS inner.derivS ∧
    Covers outer.derivK inner.derivK ∧
    Covers outer.derivChi inner.derivChi

theorem intervalAD_contains_of_covers {outer inner : IntervalAD}
    {value derivS derivK derivChi : ℝ}
    (hcovers : ADCovers outer inner)
    (hinner : inner.Contains value derivS derivK derivChi) :
    outer.Contains value derivS derivK derivChi := by
  exact
    ⟨contains_of_covers hcovers.1 hinner.1,
      contains_of_covers hcovers.2.1 hinner.2.1,
      contains_of_covers hcovers.2.2.1 hinner.2.2.1,
      contains_of_covers hcovers.2.2.2 hinner.2.2.2⟩

theorem encloses_of_covers {outer inner : IntervalAD}
    {jet : LRUpperKHistoricalEvaluatorAssembly.Jet3}
    (hcovers : ADCovers outer inner)
    (hinner : LRUpperKHistoricalEvaluatorAssembly.Encloses inner jet) :
    LRUpperKHistoricalEvaluatorAssembly.Encloses outer jet := by
  exact intervalAD_contains_of_covers hcovers hinner

/-- Replace an exact evaluator certificate by any componentwise rational
outer enclosure. -/
theorem soundness_of_covers {box : CertificateBox}
    {inner outer : MidpointCertificate}
    (hsound : CenteredEvaluatorSoundness box inner)
    (hvalue : Covers outer.value inner.value)
    (hderivS : Covers outer.derivS inner.derivS)
    (hderivK : Covers outer.derivK inner.derivK)
    (hderivChi : Covers outer.derivChi inner.derivChi) :
    CenteredEvaluatorSoundness box outer := by
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    exact contains_of_covers hvalue
      (hsound.centerValue coordinate hcoordinate)
  · intro coordinate hcoordinate
    exact contains_of_covers hderivS (hsound.derivS coordinate hcoordinate)
  · intro coordinate hcoordinate
    exact contains_of_covers hderivK (hsound.derivK coordinate hcoordinate)
  · intro coordinate hcoordinate
    exact contains_of_covers hderivChi
      (hsound.derivH coordinate hcoordinate)

end LRUpperKMidpointCoarsening
end CourtadeKumar
