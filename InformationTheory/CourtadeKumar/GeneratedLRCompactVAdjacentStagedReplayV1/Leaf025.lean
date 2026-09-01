import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf025Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1003 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf025Check
  (leaf025Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLRRL)

def leaf025Checked : CheckedTree box_rRLLRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf025Data leaf025Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
