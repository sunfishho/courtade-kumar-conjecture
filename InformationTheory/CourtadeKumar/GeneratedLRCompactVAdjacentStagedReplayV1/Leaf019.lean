import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf019Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1001 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf019Check
  (leaf019Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLLLL)

def leaf019Checked : CheckedTree box_rRLLLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf019Data leaf019Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
