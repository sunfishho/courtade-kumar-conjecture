import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf001Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((497 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf001Check
  (leaf001Data.check logTerms pZeroTerms wTerms dTerms directN box_rLLLLR)

def leaf001Checked : CheckedTree box_rLLLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf001Data leaf001Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
