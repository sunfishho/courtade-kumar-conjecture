import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf029Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((501 : ℚ) / 256) }
      headChoice := .n192 }

#kernel_checked_bool leaf029Check
  (leaf029Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRLR)

def leaf029Checked : CheckedTree box_rRLRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf029Data leaf029Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
