import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf008Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((997 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf008Check
  (leaf008Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLLLL)

def leaf008Checked : CheckedTree box_rLRLLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf008Data leaf008Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
