import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKMidpointCoarsening

/-!
# Verified dyadic outward rounding

Rounding after every interval operation keeps numerators and denominators
small.  The generator may compute the rounded data, but these lemmas prove
once and for all that the operation can only enlarge an enclosure.
-/

namespace CourtadeKumar
namespace LRUpperKDyadicOuterRounding

open LRUpperKMidpointCoarsening

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
