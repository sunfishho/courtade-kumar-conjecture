import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf027Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1001 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf027Check
  (leaf027Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRLLL)

def leaf027Checked : CheckedTree box_rRLRLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf027Data leaf027Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
