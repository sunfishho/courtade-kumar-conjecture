import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf004Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((497 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf004Check
  (leaf004Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLRLL)

def leaf004Checked : CheckedTree box_rLLRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf004Data leaf004Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
