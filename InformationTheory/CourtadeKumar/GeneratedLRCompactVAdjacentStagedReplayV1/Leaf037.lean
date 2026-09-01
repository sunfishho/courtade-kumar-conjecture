import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf037Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((503 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf037Check
  (leaf037Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLLRR)

def leaf037Checked : CheckedTree box_rRRLLRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf037Data leaf037Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
