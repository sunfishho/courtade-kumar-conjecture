import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf005Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((497 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf005Check
  (leaf005Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLRLR)

def leaf005Checked : CheckedTree box_rLLRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf005Data leaf005Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
