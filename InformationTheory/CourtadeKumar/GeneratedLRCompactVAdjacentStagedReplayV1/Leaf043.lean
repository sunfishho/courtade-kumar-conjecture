import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf043Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((63 : ℚ) / 32) }
      headChoice := .n128 }

#kernel_checked_bool leaf043Check
  (leaf043Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRRRR)

def leaf043Checked : CheckedTree box_rRRLRRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf043Data leaf043Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
