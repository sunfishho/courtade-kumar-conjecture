import InformationTheory.CourtadeKumar.IntervalMidpointCertificate

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

/-!
## Direct endpoint checker

On the nonnegative cancellation boxes used by the generated certificates,
the relevant products are monotone in their endpoints.  Checking the endpoint
products directly avoids midpoint/radius multiplication and is both tighter
and substantially cheaper to reduce.  The legacy checker above remains
available for existing generated trees.
-/

def lrPhysicalDiscardFastCheck
    (box : CertificateBox) (reason : LRPhysicalDiscardData) : Bool :=
  match reason with
  | .eAtLeastOne => decide
      (0 ≤ box.sLo ∧ 0 ≤ box.kLo ∧ 1 ≤ box.sLo * box.kLo)
  | .xBelowHighShape => decide
      (0 ≤ box.sLo ∧ 0 ≤ box.kLo ∧ 0 ≤ box.chiLo ∧
        3 / 20 < box.chiLo * (box.sLo * box.kLo))
  | .vBelowThird => decide
      (0 ≤ box.sLo ∧ 0 ≤ box.kLo ∧ box.chiHi ≤ 9 ∧
        8 < (box.sLo * box.kLo) * (9 - box.chiHi))

theorem lrPhysicalDiscardFastCheck_sound
    (box : CertificateBox) (reason : LRPhysicalDiscardData)
    (hcheck : lrPhysicalDiscardFastCheck box reason = true) :
    ∀ point, box.Contains point → ¬ LRHighShapePhysical point := by
  intro point hpoint hphysical
  rcases hpoint with ⟨hsLo, _hsHi, hkLo, _hkHi, hchiLo, hchiHi⟩
  rcases hphysical with ⟨hePhysical, hxPhysical, hvPhysical⟩
  cases reason with
  | eAtLeastOne =>
      have hrat : (0 : ℚ) ≤ box.sLo ∧ (0 : ℚ) ≤ box.kLo ∧
          (1 : ℚ) ≤ box.sLo * box.kLo := by
        simpa [lrPhysicalDiscardFastCheck] using hcheck
      have hsLoNonnegative : (0 : ℝ) ≤ (box.sLo : ℝ) := by
        exact_mod_cast hrat.1
      have hkLoNonnegative : (0 : ℝ) ≤ (box.kLo : ℝ) := by
        exact_mod_cast hrat.2.1
      have hsNonnegative : 0 ≤ point.s := hsLoNonnegative.trans hsLo
      have heLower : (box.sLo : ℝ) * box.kLo ≤ point.s * point.k :=
        mul_le_mul hsLo hkLo hkLoNonnegative hsNonnegative
      have hone : (1 : ℝ) ≤ (box.sLo : ℝ) * box.kLo := by
        exact_mod_cast hrat.2.2
      exact (not_lt_of_ge (hone.trans heLower)) hePhysical
  | xBelowHighShape =>
      have hrat : (0 : ℚ) ≤ box.sLo ∧ (0 : ℚ) ≤ box.kLo ∧
          (0 : ℚ) ≤ box.chiLo ∧
          (3 / 20 : ℚ) < box.chiLo * (box.sLo * box.kLo) := by
        simpa [lrPhysicalDiscardFastCheck] using hcheck
      have hsLoNonnegative : (0 : ℝ) ≤ (box.sLo : ℝ) := by
        exact_mod_cast hrat.1
      have hkLoNonnegative : (0 : ℝ) ≤ (box.kLo : ℝ) := by
        exact_mod_cast hrat.2.1
      have hchiLoNonnegative : (0 : ℝ) ≤ (box.chiLo : ℝ) := by
        exact_mod_cast hrat.2.2.1
      have hsNonnegative : 0 ≤ point.s := hsLoNonnegative.trans hsLo
      have hchiNonnegative : 0 ≤ point.chi :=
        hchiLoNonnegative.trans hchiLo
      have heLower : (box.sLo : ℝ) * box.kLo ≤ point.s * point.k :=
        mul_le_mul hsLo hkLo hkLoNonnegative hsNonnegative
      have heLowerNonnegative :
          (0 : ℝ) ≤ (box.sLo : ℝ) * box.kLo :=
        mul_nonneg hsLoNonnegative hkLoNonnegative
      have hchiELower :
          (box.chiLo : ℝ) * ((box.sLo : ℝ) * box.kLo) ≤
            point.chi * (point.s * point.k) :=
        mul_le_mul hchiLo heLower heLowerNonnegative hchiNonnegative
      have hstrict : (3 / 20 : ℝ) <
          (box.chiLo : ℝ) * ((box.sLo : ℝ) * box.kLo) := by
        have hcast : (((3 / 20 : ℚ) : ℝ)) <
            ((box.chiLo * (box.sLo * box.kLo) : ℚ) : ℝ) := by
          exact_mod_cast hrat.2.2.2
        norm_num at hcast ⊢
        exact hcast
      exact (not_le_of_gt (hstrict.trans_le hchiELower)) hxPhysical
  | vBelowThird =>
      have hrat : (0 : ℚ) ≤ box.sLo ∧ (0 : ℚ) ≤ box.kLo ∧
          box.chiHi ≤ (9 : ℚ) ∧
          (8 : ℚ) < (box.sLo * box.kLo) * (9 - box.chiHi) := by
        simpa [lrPhysicalDiscardFastCheck] using hcheck
      have hsLoNonnegative : (0 : ℝ) ≤ (box.sLo : ℝ) := by
        exact_mod_cast hrat.1
      have hkLoNonnegative : (0 : ℝ) ≤ (box.kLo : ℝ) := by
        exact_mod_cast hrat.2.1
      have hsNonnegative : 0 ≤ point.s := hsLoNonnegative.trans hsLo
      have heLower : (box.sLo : ℝ) * box.kLo ≤ point.s * point.k :=
        mul_le_mul hsLo hkLo hkLoNonnegative hsNonnegative
      have heLowerNonnegative :
          (0 : ℝ) ≤ (box.sLo : ℝ) * box.kLo :=
        mul_nonneg hsLoNonnegative hkLoNonnegative
      have heNonnegative : 0 ≤ point.s * point.k :=
        heLowerNonnegative.trans heLower
      have hgapNonnegative : (0 : ℝ) ≤ 9 - (box.chiHi : ℝ) := by
        exact_mod_cast sub_nonneg.mpr hrat.2.2.1
      have hgapLower : (9 : ℝ) - box.chiHi ≤ 9 - point.chi := by
        linarith
      have hproductLower :
          (box.sLo : ℝ) * box.kLo * (9 - (box.chiHi : ℝ)) ≤
            point.s * point.k * (9 - point.chi) :=
        mul_le_mul heLower hgapLower hgapNonnegative heNonnegative
      have hstrict : (8 : ℝ) <
          (box.sLo : ℝ) * box.kLo * (9 - (box.chiHi : ℝ)) := by
        exact_mod_cast hrat.2.2.2
      linarith

/-!
## Cached first-match selection

The consumers below only need the first applicable physical reason.  Selecting
it by calling the reason-indexed checker three times would rebuild the common
endpoint product `sLo * kLo` three times.  This selector binds that product
once and preserves the historical reason order.
-/

/-- Cheap endpoint-only selection of the first applicable physical reason.
The common nonnegativity facts and lower endpoint product are evaluated once. -/
def lrPhysicalDiscardFastFirst (box : CertificateBox) :
    Option LRPhysicalDiscardData :=
  let eLo := box.sLo * box.kLo
  if 0 ≤ box.sLo ∧ 0 ≤ box.kLo then
    if 1 ≤ eLo then
      some .eAtLeastOne
    else if 0 ≤ box.chiLo ∧ 3 / 20 < box.chiLo * eLo then
      some .xBelowHighShape
    else if box.chiHi ≤ 9 ∧ 8 < eLo * (9 - box.chiHi) then
      some .vBelowThird
    else
      none
  else
    none

/-- A reason returned by the cached endpoint selector passes the ordinary
kernel-reducible fast checker. -/
theorem lrPhysicalDiscardFastFirst_check_of_eq
    (box : CertificateBox) (reason : LRPhysicalDiscardData)
    (hfirst : lrPhysicalDiscardFastFirst box = some reason) :
    lrPhysicalDiscardFastCheck box reason = true := by
  unfold lrPhysicalDiscardFastFirst at hfirst
  dsimp only at hfirst
  split at hfirst <;> rename_i hbase
  · split at hfirst <;> rename_i he
    · cases hfirst
      simp [lrPhysicalDiscardFastCheck, hbase.1, hbase.2, he]
    · split at hfirst <;> rename_i hx
      · cases hfirst
        simp [lrPhysicalDiscardFastCheck, hbase.1, hbase.2,
          hx.1, hx.2]
      · split at hfirst <;> rename_i hv
        · cases hfirst
          simp [lrPhysicalDiscardFastCheck, hbase.1, hbase.2,
            hv.1, hv.2]
        · simp at hfirst
  · simp at hfirst

/-- Historical first-match selection, factored out so the optimized selector
can retain it as an exact compatibility fallback.  The shared `e` enclosure
is built once even when no physical reason applies. -/
def lrPhysicalDiscardLegacyFirst (box : CertificateBox) :
    Option LRPhysicalDiscardData :=
  let eI := lrEInterval box
  if 1 ≤ eI.lower then
    some .eAtLeastOne
  else
    let chiEI := RationalEnclosure.mul box.chiInterval eI
    if 3 / 20 < chiEI.lower then
      some .xBelowHighShape
    else
      let smallVI := RationalEnclosure.sub (RationalEnclosure.point 8)
        (RationalEnclosure.mul eI
          (RationalEnclosure.sub (RationalEnclosure.point 9)
            box.chiInterval))
      if smallVI.upper < 0 then
        some .vBelowThird
      else
        none

theorem lrPhysicalDiscardLegacyFirst_check_of_eq
    (box : CertificateBox) (reason : LRPhysicalDiscardData)
    (hfirst : lrPhysicalDiscardLegacyFirst box = some reason) :
    lrPhysicalDiscardCheck box reason = true := by
  unfold lrPhysicalDiscardLegacyFirst at hfirst
  dsimp only at hfirst
  split at hfirst <;> rename_i he
  · cases hfirst
    simpa only [lrPhysicalDiscardCheck, decide_eq_true_eq] using he
  split at hfirst <;> rename_i hx
  · cases hfirst
    simpa only [lrPhysicalDiscardCheck, lrChiEInterval,
      decide_eq_true_eq] using hx
  split at hfirst <;> rename_i hv
  · cases hfirst
    simpa only [lrPhysicalDiscardCheck, lrSmallVNumeratorInterval,
      decide_eq_true_eq] using hv
  · simp at hfirst

/-- Fast reason selection with an exact legacy-check confirmation.  Existing
checker APIs and generated discard payloads therefore remain unchanged.  If
the endpoint-selected reason is not accepted by the legacy enclosure checker,
the complete historical first-match search is used as a fallback. -/
def lrPhysicalDiscardFirst (box : CertificateBox) :
    Option LRPhysicalDiscardData :=
  match lrPhysicalDiscardFastFirst box with
  | some reason =>
      if lrPhysicalDiscardCheck box reason then
        some reason
      else
        lrPhysicalDiscardLegacyFirst box
  | none => lrPhysicalDiscardLegacyFirst box

theorem lrPhysicalDiscardFirst_check_of_eq
    (box : CertificateBox) (reason : LRPhysicalDiscardData)
    (hfirst : lrPhysicalDiscardFirst box = some reason) :
    lrPhysicalDiscardCheck box reason = true := by
  unfold lrPhysicalDiscardFirst at hfirst
  cases hfast : lrPhysicalDiscardFastFirst box with
  | none =>
      rw [hfast] at hfirst
      exact lrPhysicalDiscardLegacyFirst_check_of_eq box reason hfirst
  | some fastReason =>
      rw [hfast] at hfirst
      by_cases hlegacy :
          lrPhysicalDiscardCheck box fastReason = true
      · simp [hlegacy] at hfirst
        subst reason
        exact hlegacy
      · simp [hlegacy] at hfirst
        exact lrPhysicalDiscardLegacyFirst_check_of_eq box reason hfirst

end CourtadeKumar
