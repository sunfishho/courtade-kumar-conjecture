import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf051Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1007 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf051Check
  (leaf051Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRRRL)

def leaf051Checked : CheckedTree box_rRRRRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf051Data leaf051Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
