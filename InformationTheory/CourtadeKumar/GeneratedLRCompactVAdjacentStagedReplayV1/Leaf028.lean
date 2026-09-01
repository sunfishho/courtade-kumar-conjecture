import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf028Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((501 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf028Check
  (leaf028Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRLLR)

def leaf028Checked : CheckedTree box_rRLRLLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf028Data leaf028Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
