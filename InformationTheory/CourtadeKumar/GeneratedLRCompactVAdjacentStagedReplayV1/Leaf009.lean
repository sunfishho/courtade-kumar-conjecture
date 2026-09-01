import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf009Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((499 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf009Check
  (leaf009Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLLLR)

def leaf009Checked : CheckedTree box_rLRLLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf009Data leaf009Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
