import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf021Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1001 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf021Check
  (leaf021Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLLRL)

def leaf021Checked : CheckedTree box_rRLLLRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf021Data leaf021Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
