import InformationTheory.CourtadeKumar.LRSmallVZeroClosure

/-! Complete kernel-checked closure of the small-odds `V` chart. -/

open Set

namespace CourtadeKumar

theorem lrSmallVCoefficientTheorem : LRSmallVCoefficientTheorem := by
  intro v t hv ht hvSmall
  exact lrLowVConvolutionCoeff_nonneg_smallV hv hvSmall ht

theorem lrHighShapeSmallVNumeratorTheorem :
    LRHighShapeSmallVNumeratorTheorem :=
  lrHighShapeSmallVNumerator_of_coefficients lrSmallVCoefficientTheorem

end CourtadeKumar
