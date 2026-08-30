import InformationTheory.CourtadeKumar.LRDeterminantUpperKMidpointCoarsening
import Mathlib.Data.Rat.Floor

/-!
# Verified dyadic outward rounding

Rounding after every interval operation keeps numerators and denominators
small.  The generator may compute the rounded data, but these lemmas prove
once and for all that the operation can only enlarge an enclosure.
-/

namespace CourtadeKumar
namespace LRUpperKDyadicOuterRounding

open LRUpperKMidpointCoarsening

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

theorem outerEnclosure_covers (bits : ℕ) (value : RationalEnclosure) :
    Covers (outerEnclosure bits value) value := by
  exact ⟨roundDown_le bits value.lower, le_roundUp bits value.upper⟩

def outerIntervalAD (bits : ℕ) (value : IntervalAD) : IntervalAD :=
  { value := outerEnclosure bits value.value
    derivS := outerEnclosure bits value.derivS
    derivK := outerEnclosure bits value.derivK
    derivChi := outerEnclosure bits value.derivChi }

theorem outerIntervalAD_covers (bits : ℕ) (value : IntervalAD) :
    ADCovers (outerIntervalAD bits value) value := by
  exact
    ⟨outerEnclosure_covers bits value.value,
      outerEnclosure_covers bits value.derivS,
      outerEnclosure_covers bits value.derivK,
      outerEnclosure_covers bits value.derivChi⟩

end LRUpperKDyadicOuterRounding
end CourtadeKumar
