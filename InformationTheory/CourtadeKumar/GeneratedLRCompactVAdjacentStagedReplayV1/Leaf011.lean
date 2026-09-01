import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf011Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((999 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf011Check
  (leaf011Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLRLL)

def leaf011Checked : CheckedTree box_rLRLRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf011Data leaf011Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
