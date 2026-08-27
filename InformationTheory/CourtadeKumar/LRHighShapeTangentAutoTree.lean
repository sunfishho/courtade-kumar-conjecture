import InformationTheory.CourtadeKumar.LRHighShapeMidpointAutoTree

/-!
# Deterministic trees for the high-shape tangent certificate

The tangent evaluator needs four payloads beyond the half-midpoint base.
They are generated here and then checked by the already proved evaluator.
As with the midpoint tree builder, generation is untrusted: only a returned
tree together with `buildTree_check_of_eq` yields a theorem.
-/

namespace CourtadeKumar

namespace LRHighShapeTangentCertificate

/-- Generate every square-root and logarithm proposal used by one tangent
leaf. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeTangentCertificate :=
  let base := LRHighShapeVCertificate.auto sqrtFuel logFuel box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let v := base.kernel.coordinate.vAD box
  { base := base
    qBY0 := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s y0).value
    qBE := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s e).value
    qS := LRQADCertificate.auto sqrtFuel logFuel s.value
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 2) v).value }

end LRHighShapeTangentCertificate

namespace LRHighShapeTangentAutoTree

abbrev Tree := SubdivisionCertificate LRHighShapeTangentCertificate
  LRHighShapeVDiscardData

def splitScoreS (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  (payload.evaluate terms box).derivS.maxAbs *
    RationalEnclosure.radius box.sInterval

def splitScoreK (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  (payload.evaluate terms box).derivK.maxAbs *
    RationalEnclosure.radius box.kInterval

def splitScoreChi (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  (payload.evaluate terms box).derivChi.maxAbs *
    RationalEnclosure.radius box.chiInterval

def chooseAxis (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : CertificateAxis :=
  let ss := splitScoreS terms box payload
  let sk := splitScoreK terms box payload
  let sc := splitScoreChi terms box payload
  if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
  else if sk ≥ sc ∧ box.kLo < box.kHi then .k
  else .chi

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → CertificateBox → Option Tree
  | 0, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      if LRHighShapeTangentCertificate.accepts terms box payload then
        some (.accept payload)
      else
        match LRHighShapeMidpointAutoTree.autoDiscard terms box payload.base with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      if LRHighShapeTangentCertificate.accepts terms box payload then
        some (.accept payload)
      else
        match LRHighShapeMidpointAutoTree.autoDiscard terms box payload.base with
        | some data => some (.discard data)
        | none =>
            let axis := chooseAxis terms box payload
            let cut := axisCut box axis
            match buildTree terms sqrtFuel logFuel fuel (box.lower axis cut),
                buildTree terms sqrtFuel logFuel fuel (box.upper axis cut) with
            | some lower, some upper => some (.split axis cut lower upper)
            | _, _ => none

def treeNodes : Tree → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ _ lower upper => 1 + treeNodes lower + treeNodes upper

theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check (LRHighShapeTangentCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true := by
  induction fuel generalizing box tree with
  | zero =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      by_cases haccept :
          LRHighShapeTangentCertificate.accepts terms box payload = true
      · simp [buildTree, payload, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse :
            LRHighShapeTangentCertificate.accepts terms box payload = false :=
          Bool.eq_false_of_not_eq_true haccept
        generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
          terms box payload.base = discardOption
        cases discardOption with
        | none => simp [buildTree, payload, hfalse, hdiscard] at hbuild
        | some data =>
            simp [buildTree, payload, hfalse, hdiscard] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check] using
              LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                terms box payload.base data hdiscard
  | succ fuel ih =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      by_cases haccept :
          LRHighShapeTangentCertificate.accepts terms box payload = true
      · simp [buildTree, payload, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse :
            LRHighShapeTangentCertificate.accepts terms box payload = false :=
          Bool.eq_false_of_not_eq_true haccept
        generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
          terms box payload.base = discardOption
        cases discardOption with
        | some data =>
            simp [buildTree, payload, hfalse, hdiscard] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check] using
              LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                terms box payload.base data hdiscard
        | none =>
            let axis := chooseAxis terms box payload
            let cut := axisCut box axis
            generalize hlower : buildTree terms sqrtFuel logFuel fuel
              (box.lower axis cut) = lowerOption
            generalize hupper : buildTree terms sqrtFuel logFuel fuel
              (box.upper axis cut) = upperOption
            cases lowerOption with
            | none =>
                simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                  hlower] at hbuild
            | some lower =>
                cases upperOption with
                | none =>
                    simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                      hlower, hupper] at hbuild
                | some upper =>
                    simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                      hlower, hupper] at hbuild
                    subst tree
                    simp only [SubdivisionCertificate.check,
                      Bool.and_eq_true]
                    exact ⟨ih _ _ hlower, ih _ _ hupper⟩

/-- Checker-level soundness for any concrete tangent subdivision. -/
theorem subdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox} {certificate : Tree}
    (hcheck : certificate.check
      (LRHighShapeTangentCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateTTarget point := by
  exact subdivisionCertificate_nonnegative_checked
    (LRHighShapeTangentCertificate.checkedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

/-- A successful generated tree proves the exact tangent target throughout
the relevant part of its root box. -/
theorem target_nonnegative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateTTarget point := by
  exact subdivisionCertificate_nonnegative terms
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRHighShapeTangentAutoTree

/-- Coordinate-level tangent statement supplied by a complete collection
of generated roots and analytic tails. -/
def LRHighShapeTangentCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateTTarget point

/-- Transport a complete cancellation-coordinate tangent proof back to the
flow theorem used by the final positive-chart assembly. -/
theorem lrHighShapeTangentTheorem_of_coordinateTheorem
    (hcoordinate : LRHighShapeTangentCoordinateTheorem) :
    LRHighShapeTangentTheorem := by
  intro R v t hR hv ht htHigh hvHigh hJ
  let point := lrFlowCertificatePoint R v t
  have hinterior : LRHighShapeInterior point := by
    simpa [point] using lrFlowCertificatePoint_highShapeInterior hR hv ht
  have hrelevant : LRHighShapeVRelevant point := by
    simpa [point] using lrFlowCertificatePoint_highShapeVRelevant
      hR hv ht htHigh hvHigh hJ
  have htarget := hcoordinate point hinterior hrelevant
  rw [lrCertificateTTarget_eq_highShapeTarget hinterior.1
    hinterior.2.1 ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩] at htarget
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  rw [show point = lrFlowCertificatePoint R v t by rfl,
    lrHighShapeTCertificateTarget_flow hRNe hePos.ne' hv.1 ht.1] at htarget
  exact htarget

end CourtadeKumar
