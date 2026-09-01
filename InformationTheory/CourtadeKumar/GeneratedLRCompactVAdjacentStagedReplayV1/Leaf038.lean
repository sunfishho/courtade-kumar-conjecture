import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf038Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1007 : ℚ) / 512) }
      headChoice := .n192 }

#kernel_checked_bool leaf038Check
  (leaf038Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRLL)

def leaf038Checked : CheckedTree box_rRRLRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf038Data leaf038Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
