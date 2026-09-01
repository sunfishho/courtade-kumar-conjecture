import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf023Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1003 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf023Check
  (leaf023Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLRLL)

def leaf023Checked : CheckedTree box_rRLLRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf023Data leaf023Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
