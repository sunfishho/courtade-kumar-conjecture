import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf048Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1007 : ℚ) / 512) }
      headChoice := .n192 }

#kernel_checked_bool leaf048Check
  (leaf048Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRRLL)

def leaf048Checked : CheckedTree box_rRRRRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf048Data leaf048Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
