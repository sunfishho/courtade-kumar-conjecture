import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf034Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1005 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf034Check
  (leaf034Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLLLL)

def leaf034Checked : CheckedTree box_rRRLLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf034Data leaf034Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
