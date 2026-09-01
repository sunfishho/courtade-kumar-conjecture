import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf046Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1005 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf046Check
  (leaf046Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRLRL)

def leaf046Checked : CheckedTree box_rRRRLRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf046Data leaf046Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
