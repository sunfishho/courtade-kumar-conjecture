import InformationTheory.CourtadeKumar.IntervalCertificateAssembly

/-!
# Verified physical-domain discards for the LR cancellation chart

The cancellation coordinates are `e = s k`, `x = 1 - χ e`, and
`v² = (1-e)/x`.  The third physical inequality can be cleared, when
`x > 0`, to `0 ≤ 8 - e(9-χ)`.  A discard is accepted only when an outward
interval proves that every point in the box violates one of these necessary
conditions.
-/

namespace CourtadeKumar

/-- Algebraic part of the retained high-shape physical domain.  The separate
positive-`J` condition is added by the determinant-specific checker. -/
def LRHighShapePhysical (point : CertificatePoint) : Prop :=
  point.s * point.k < 1 ∧
  point.chi * (point.s * point.k) ≤ 3 / 20 ∧
  0 ≤ 8 - point.s * point.k * (9 - point.chi)

def lrEInterval (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mul box.sInterval box.kInterval

def lrChiEInterval (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mul box.chiInterval (lrEInterval box)

def lrSmallVNumeratorInterval (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 8)
    (RationalEnclosure.mul (lrEInterval box)
      (RationalEnclosure.sub (RationalEnclosure.point 9) box.chiInterval))

theorem lrEInterval_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrEInterval box).Contains (point.s * point.k) :=
  RationalEnclosure.contains_mul
    ⟨hpoint.1, hpoint.2.1⟩ ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩

theorem lrChiEInterval_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrChiEInterval box).Contains
      (point.chi * (point.s * point.k)) :=
  RationalEnclosure.contains_mul
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
    (lrEInterval_sound hpoint)

theorem lrSmallVNumeratorInterval_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrSmallVNumeratorInterval box).Contains
      (8 - point.s * point.k * (9 - point.chi)) := by
  exact RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 8)
    (RationalEnclosure.contains_mul (lrEInterval_sound hpoint)
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_point 9)
        ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩))

/-- The three one-sided algebraic discard reasons. -/
inductive LRPhysicalDiscardData where
  | eAtLeastOne
  | xBelowHighShape
  | vBelowThird
  deriving DecidableEq, Repr

def lrPhysicalDiscardCheck
    (box : CertificateBox) (reason : LRPhysicalDiscardData) : Bool :=
  match reason with
  | .eAtLeastOne => decide (1 ≤ (lrEInterval box).lower)
  | .xBelowHighShape => decide (3 / 20 < (lrChiEInterval box).lower)
  | .vBelowThird => decide ((lrSmallVNumeratorInterval box).upper < 0)

theorem lrPhysicalDiscardCheck_sound
    (box : CertificateBox) (reason : LRPhysicalDiscardData)
    (hcheck : lrPhysicalDiscardCheck box reason = true) :
    ∀ point, box.Contains point → ¬ LRHighShapePhysical point := by
  intro point hpoint hphysical
  rcases hphysical with ⟨he, hx, hv⟩
  cases reason with
  | eAtLeastOne =>
      have hrat : (1 : ℚ) ≤ (lrEInterval box).lower := by
        simpa [lrPhysicalDiscardCheck] using hcheck
      have hlower : (1 : ℝ) ≤ ((lrEInterval box).lower : ℝ) := by
        exact_mod_cast hrat
      have henclose := (lrEInterval_sound hpoint).1
      linarith
  | xBelowHighShape =>
      have hrat : (3 / 20 : ℚ) < (lrChiEInterval box).lower := by
        simpa [lrPhysicalDiscardCheck] using hcheck
      have hlower : (3 / 20 : ℝ) <
          ((lrChiEInterval box).lower : ℝ) := by
        have hcast : (((3 / 20 : ℚ) : ℝ)) <
            ((lrChiEInterval box).lower : ℝ) := by
          exact_mod_cast hrat
        norm_num at hcast ⊢
        exact hcast
      have henclose := (lrChiEInterval_sound hpoint).1
      linarith
  | vBelowThird =>
      have hrat : (lrSmallVNumeratorInterval box).upper < (0 : ℚ) := by
        simpa [lrPhysicalDiscardCheck] using hcheck
      have hupper : ((lrSmallVNumeratorInterval box).upper : ℝ) < 0 := by
        exact_mod_cast hrat
      have henclose := (lrSmallVNumeratorInterval_sound hpoint).2
      linarith

end CourtadeKumar
