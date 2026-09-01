import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf022Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((501 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf022Check
  (leaf022Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLLRR)

def leaf022Checked : CheckedTree box_rRLLLRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf022Data leaf022Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
