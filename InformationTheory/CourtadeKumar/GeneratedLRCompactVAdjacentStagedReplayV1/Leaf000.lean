import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf000Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((497 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf000Check
  (leaf000Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLLLL)

def leaf000Checked : CheckedTree box_rLLLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf000Data leaf000Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
