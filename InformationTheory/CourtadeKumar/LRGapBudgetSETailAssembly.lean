import InformationTheory.CourtadeKumar.LRGapBudgetSECertificate

/-!
# Finite subdivision interface for the bounded gap-budget tail

The generic `CertificatePoint.k` and `CertificateBox.k*` fields are
interpreted in this file as the bounded physical defect `e`, not as the
unbounded ratio `e / s`.  The retained region is the near-endpoint
high-shape tail

`0 < s < 1/10`, `0 < e < 1`, `0 < chi < 1`, `4s <= e`,

together with the two algebraic high-shape constraints.  Every accepted
leaf is checked by `LRGapBudgetSECertificate`; discarded leaves use only
one-sided rational interval comparisons.
-/

open Set

namespace CourtadeKumar

/-- A bounded-coordinate point associated to an ordinary cancellation
point.  Its `k` field stores `e = s*k`. -/
def lrGapBudgetSEPoint (point : CertificatePoint) : CertificatePoint where
  s := point.s
  k := lrCertificateE point
  chi := point.chi

/-- The exact bounded tail region on which the `e` derivative is needed. -/
def LRGapBudgetSETailRelevant (point : CertificatePoint) : Prop :=
  point.s ∈ Ioo (0 : ℝ) (1 / 10) ∧
  point.k ∈ Ioo (0 : ℝ) 1 ∧
  point.chi ∈ Ioo (0 : ℝ) 1 ∧
  4 * point.s ≤ point.k ∧
  point.chi * point.k ≤ 3 / 20 ∧
  0 ≤ 8 - point.k * (9 - point.chi)

def lrGapBudgetSEChiEInterval (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mul box.chiInterval box.kInterval

def lrGapBudgetSESmallVNumeratorInterval
    (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 8)
    (RationalEnclosure.mul box.kInterval
      (RationalEnclosure.sub (RationalEnclosure.point 9) box.chiInterval))

theorem lrGapBudgetSEChiEInterval_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrGapBudgetSEChiEInterval box).Contains (point.chi * point.k) := by
  exact RationalEnclosure.contains_mul
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩

theorem lrGapBudgetSESmallVNumeratorInterval_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    (lrGapBudgetSESmallVNumeratorInterval box).Contains
      (8 - point.k * (9 - point.chi)) := by
  exact RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 8)
    (RationalEnclosure.contains_mul
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_point 9)
        ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩))

/-- One-sided reasons a whole box can miss the bounded tail. -/
inductive LRGapBudgetSEDiscardData where
  | eBelowFourS
  | eAtLeastOne
  | xBelowHighShape
  | vBelowThird
  deriving DecidableEq, Repr

def lrGapBudgetSEDiscardCheck (box : CertificateBox) :
    LRGapBudgetSEDiscardData → Bool
  | .eBelowFourS => decide (box.kHi < 4 * box.sLo)
  | .eAtLeastOne => decide (1 ≤ box.kLo)
  | .xBelowHighShape =>
      decide (3 / 20 < (lrGapBudgetSEChiEInterval box).lower)
  | .vBelowThird =>
      decide ((lrGapBudgetSESmallVNumeratorInterval box).upper < 0)

theorem lrGapBudgetSEDiscardCheck_sound
    (box : CertificateBox) (reason : LRGapBudgetSEDiscardData)
    (hcheck : lrGapBudgetSEDiscardCheck box reason = true) :
    ∀ point, box.Contains point → ¬ LRGapBudgetSETailRelevant point := by
  intro point hpoint hrelevant
  rcases hrelevant with ⟨hs, he, hchi, htail, hx, hv⟩
  cases reason with
  | eBelowFourS =>
      have hrat : box.kHi < 4 * box.sLo := by
        simpa [lrGapBudgetSEDiscardCheck] using hcheck
      have hreal : (box.kHi : ℝ) < 4 * (box.sLo : ℝ) := by
        exact_mod_cast hrat
      linarith [hpoint.1, hpoint.2.2.2.1]
  | eAtLeastOne =>
      have hrat : (1 : ℚ) ≤ box.kLo := by
        simpa [lrGapBudgetSEDiscardCheck] using hcheck
      have hreal : (1 : ℝ) ≤ (box.kLo : ℝ) := by
        exact_mod_cast hrat
      linarith [hpoint.2.2.1, he.2]
  | xBelowHighShape =>
      have hrat : (3 / 20 : ℚ) <
          (lrGapBudgetSEChiEInterval box).lower := by
        simpa [lrGapBudgetSEDiscardCheck] using hcheck
      have hreal : (3 / 20 : ℝ) <
          ((lrGapBudgetSEChiEInterval box).lower : ℝ) := by
        have hcast : (((3 / 20 : ℚ) : ℝ)) <
            ((lrGapBudgetSEChiEInterval box).lower : ℝ) := by
          exact_mod_cast hrat
        norm_num at hcast ⊢
        exact hcast
      linarith [(lrGapBudgetSEChiEInterval_sound hpoint).1]
  | vBelowThird =>
      have hrat : (lrGapBudgetSESmallVNumeratorInterval box).upper <
          (0 : ℚ) := by
        simpa [lrGapBudgetSEDiscardCheck] using hcheck
      have hreal :
          ((lrGapBudgetSESmallVNumeratorInterval box).upper : ℝ) < 0 := by
        exact_mod_cast hrat
      linarith [(lrGapBudgetSESmallVNumeratorInterval_sound hpoint).2]

namespace LRGapBudgetSECertificate

def derivativeAccepts (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  check box payload && derivENonnegative terms box payload

def budgetAccepts (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  check box payload && budgetNonnegative terms box payload

theorem derivativeAccepts_sound (terms : ℕ) (box : CertificateBox)
    (payload : Payload) (haccept : derivativeAccepts terms box payload = true) :
    ∀ point, box.Contains point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  intro point hpoint
  have hparts : check box payload = true ∧
      derivENonnegative terms box payload = true := by
    simpa [derivativeAccepts] using haccept
  exact derivENonnegative_sound terms
    ⟨hpoint.1, hpoint.2.1⟩
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
    hparts.1 hparts.2

theorem budgetAccepts_sound (terms : ℕ) (box : CertificateBox)
    (payload : Payload) (haccept : budgetAccepts terms box payload = true) :
    ∀ point, box.Contains point →
      0 ≤ lrGapBudgetSEChi point.s point.k point.chi := by
  intro point hpoint
  have hparts : check box payload = true ∧
      budgetNonnegative terms box payload = true := by
    simpa [budgetAccepts] using haccept
  exact budgetNonnegative_sound terms
    ⟨hpoint.1, hpoint.2.1⟩
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
    hparts.1 hparts.2

def autoDerivativeAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  derivativeAccepts terms box (auto sqrtFuel logFuel box)

def autoBudgetAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  budgetAccepts terms box (auto sqrtFuel logFuel box)

theorem autoDerivativeAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : Unit)
    (haccept : autoDerivativeAccepts terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  exact derivativeAccepts_sound terms box (auto sqrtFuel logFuel box)
    (by simpa [autoDerivativeAccepts] using haccept)

theorem autoBudgetAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : Unit)
    (haccept : autoBudgetAccepts terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point →
      0 ≤ lrGapBudgetSEChi point.s point.k point.chi := by
  exact budgetAccepts_sound terms box (auto sqrtFuel logFuel box)
    (by simpa [autoBudgetAccepts] using haccept)

end LRGapBudgetSECertificate

/-- End-to-end derivative soundness for a finite bounded-tail subdivision. -/
theorem lrGapBudgetSEDerivativeSubdivision_sound
    (terms sqrtFuel logFuel : ℕ) {box : CertificateBox}
    {tree : SubdivisionCertificate Unit LRGapBudgetSEDiscardData}
    (hcheck : tree.check
      (LRGapBudgetSECertificate.autoDerivativeAccepts
        terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck box = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  exact subdivisionCertificate_sound
    (LRGapBudgetSECertificate.autoDerivativeAccepts_sound
      terms sqrtFuel logFuel)
    lrGapBudgetSEDiscardCheck_sound hcheck

/-- End-to-end value soundness for a finite bounded-tail subdivision. -/
theorem lrGapBudgetSEBudgetSubdivision_sound
    (terms sqrtFuel logFuel : ℕ) {box : CertificateBox}
    {tree : SubdivisionCertificate Unit LRGapBudgetSEDiscardData}
    (hcheck : tree.check
      (LRGapBudgetSECertificate.autoBudgetAccepts terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck box = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChi point.s point.k point.chi := by
  exact subdivisionCertificate_sound
    (LRGapBudgetSECertificate.autoBudgetAccepts_sound
      terms sqrtFuel logFuel)
    lrGapBudgetSEDiscardCheck_sound hcheck

/-- One closed rational root contains every bounded-coordinate tail point;
strict analytic endpoint conditions are carried by `Relevant`, not hidden in
the geometry of the root. -/
def lrGapBudgetSETailRoot : CertificateBox where
  sLo := 0
  sHi := 1 / 10
  kLo := 0
  kHi := 1
  chiLo := 0
  chiHi := 1

theorem lrGapBudgetSEPoint_mem_root {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) (hs : point.s < 1 / 10) :
    lrGapBudgetSETailRoot.Contains (lrGapBudgetSEPoint point) := by
  have h : (0 : ℝ) ≤ point.s ∧ point.s ≤ 1 / 10 ∧
      0 ≤ lrCertificateE point ∧ lrCertificateE point ≤ 1 ∧
      0 ≤ point.chi ∧ point.chi ≤ 1 :=
    ⟨hinterior.1.1.le, hs.le, hinterior.2.1.1.le,
    hinterior.2.1.2.le, hinterior.2.2.1.le,
    hinterior.2.2.2.le⟩
  simpa [CertificateBox.Contains, lrGapBudgetSETailRoot,
    lrGapBudgetSEPoint] using h

theorem lrGapBudgetSEPoint_tailRelevant {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    LRGapBudgetSETailRelevant (lrGapBudgetSEPoint point) := by
  refine ⟨⟨hinterior.1.1, hs⟩, hinterior.2.1,
    hinterior.2.2, ?_, ?_, ?_⟩
  · change 4 * point.s ≤ point.s * point.k
    nlinarith [mul_nonneg hinterior.1.1.le (sub_nonneg.mpr hk)]
  · simpa [lrGapBudgetSEPoint, lrCertificateE] using hphysical.2.1
  · simpa [lrGapBudgetSEPoint, lrCertificateE] using hphysical.2.2

theorem lrCertificateX_pos_of_highShapeInterior
    {point : CertificatePoint} (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateX point := by
  change 0 < 1 - point.chi * lrCertificateE point
  have hprod : point.chi * lrCertificateE point < 1 := calc
    point.chi * lrCertificateE point < 1 * lrCertificateE point :=
      mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
    _ = lrCertificateE point := one_mul _
    _ < 1 := hinterior.2.1.2
  exact sub_pos.mpr hprod

theorem lrCertificateV_pos_of_highShapeInterior
    {point : CertificatePoint} (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateV point := by
  unfold lrCertificateV
  exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hinterior.2.1.2)
    (lrCertificateX_pos_of_highShapeInterior hinterior))

/-- A checked subdivision of the single bounded root supplies precisely the
`k`-derivative hypothesis used by the monotonic noncompact-tail argument. -/
theorem lrCertificateGapBudgetDerivK_nonnegative_of_SETailSubdivision
    (terms sqrtFuel logFuel : ℕ)
    {tree : SubdivisionCertificate Unit LRGapBudgetSEDiscardData}
    (hcheck : tree.check
      (LRGapBudgetSECertificate.autoDerivativeAccepts
        terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck lrGapBudgetSETailRoot = true)
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudgetDerivK point := by
  apply lrCertificateGapBudgetDerivK_nonneg_of_derivE
    hinterior.1.1.le
    (lrCertificateV_pos_of_highShapeInterior hinterior)
    (lrCertificateX_pos_of_highShapeInterior hinterior)
  exact lrGapBudgetSEDerivativeSubdivision_sound
    terms sqrtFuel logFuel hcheck
    (lrGapBudgetSEPoint point)
    (lrGapBudgetSEPoint_mem_root hinterior hs)
    (lrGapBudgetSEPoint_tailRelevant hinterior hphysical hs hk)

end CourtadeKumar
