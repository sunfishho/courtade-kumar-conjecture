import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf010Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((499 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf010Check
  (leaf010Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLLR)

def leaf010Checked : CheckedTree box_rLRLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf010Data leaf010Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
