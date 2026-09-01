import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf020Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((501 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf020Check
  (leaf020Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLLLR)

def leaf020Checked : CheckedTree box_rRLLLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf020Data leaf020Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
