import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf041Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((63 : ℚ) / 32) }
      headChoice := .n128 }

#kernel_checked_bool leaf041Check
  (leaf041Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRRLR)

def leaf041Checked : CheckedTree box_rRRLRRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf041Data leaf041Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
