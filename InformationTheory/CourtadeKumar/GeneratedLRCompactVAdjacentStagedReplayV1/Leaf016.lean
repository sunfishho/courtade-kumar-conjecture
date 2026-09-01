import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf016Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((499 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf016Check
  (leaf016Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRRLR)

def leaf016Checked : CheckedTree box_rLRRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf016Data leaf016Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
