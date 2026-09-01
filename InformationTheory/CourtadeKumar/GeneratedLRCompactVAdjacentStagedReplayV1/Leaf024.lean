import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf024Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((251 : ℚ) / 128) }
      headChoice := .n128 }

#kernel_checked_bool leaf024Check
  (leaf024Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLLRLR)

def leaf024Checked : CheckedTree box_rRLLRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf024Data leaf024Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
