import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import InformationTheory.CourtadeKumar.LRDeterminantUpperKEnclosureCovers
import Mathlib.Data.Rat.Floor

/-!
# Lightweight verified dyadic outward rounding

This module contains only rational and `RationalEnclosure` operations.  The
interval-AD and midpoint-evaluator adapters live in
`LRDeterminantUpperKDyadicOuterRounding`.
-/

namespace CourtadeKumar
namespace LRUpperKDyadicOuterRounding

def scale (bits : ℕ) : ℚ := (2 : ℚ) ^ bits

theorem scale_pos (bits : ℕ) : 0 < scale bits := by
  unfold scale
  exact pow_pos (by norm_num) bits

def roundDown (bits : ℕ) (value : ℚ) : ℚ :=
  (Int.floor (value * scale bits) : ℚ) / scale bits

def roundUp (bits : ℕ) (value : ℚ) : ℚ :=
  (Int.ceil (value * scale bits) : ℚ) / scale bits

theorem roundDown_le (bits : ℕ) (value : ℚ) :
    roundDown bits value ≤ value := by
  apply (div_le_iff₀ (scale_pos bits)).2
  simpa [roundDown] using (Int.floor_le (value * scale bits))

theorem le_roundUp (bits : ℕ) (value : ℚ) :
    value ≤ roundUp bits value := by
  apply (le_div_iff₀ (scale_pos bits)).2
  simpa [roundUp] using (Int.le_ceil (value * scale bits))

def outerEnclosure (bits : ℕ)
    (value : RationalEnclosure) : RationalEnclosure :=
  { lower := roundDown bits value.lower
    upper := roundUp bits value.upper }

theorem outerEnclosure_lower_le (bits : ℕ) (value : RationalEnclosure) :
    (outerEnclosure bits value).lower ≤ value.lower :=
  roundDown_le bits value.lower

theorem outerEnclosure_le_upper (bits : ℕ) (value : RationalEnclosure) :
    value.upper ≤ (outerEnclosure bits value).upper :=
  le_roundUp bits value.upper

/-- Dyadic outward rounding covers the original enclosure. -/
theorem outerEnclosure_covers (bits : ℕ) (value : RationalEnclosure) :
    LRUpperKMidpointCoarsening.Covers (outerEnclosure bits value) value := by
  exact ⟨roundDown_le bits value.lower, le_roundUp bits value.upper⟩

end LRUpperKDyadicOuterRounding
end CourtadeKumar
