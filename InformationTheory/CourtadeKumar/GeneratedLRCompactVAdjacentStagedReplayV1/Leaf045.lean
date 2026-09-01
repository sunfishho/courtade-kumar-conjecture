import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf045Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((503 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf045Check
  (leaf045Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRLLR)

def leaf045Checked : CheckedTree box_rRRRLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf045Data leaf045Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
