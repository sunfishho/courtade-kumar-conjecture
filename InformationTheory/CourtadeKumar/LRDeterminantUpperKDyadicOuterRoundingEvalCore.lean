import InformationTheory.CourtadeKumar.RationalEnclosureCore
import Mathlib.Data.Rat.Floor

/-!
# Executable dyadic outward rounding

The order proofs for these endpoint computations live in
`LRDeterminantUpperKDyadicOuterRoundingCore`.
-/

namespace CourtadeKumar
namespace LRUpperKDyadicOuterRounding

def scale (bits : ℕ) : ℚ := (2 : ℚ) ^ bits

def roundDown (bits : ℕ) (value : ℚ) : ℚ :=
  (Int.floor (value * scale bits) : ℚ) / scale bits

def roundUp (bits : ℕ) (value : ℚ) : ℚ :=
  (Int.ceil (value * scale bits) : ℚ) / scale bits

def outerEnclosure (bits : ℕ)
    (value : RationalEnclosure) : RationalEnclosure :=
  { lower := roundDown bits value.lower
    upper := roundUp bits value.upper }

end LRUpperKDyadicOuterRounding
end CourtadeKumar
