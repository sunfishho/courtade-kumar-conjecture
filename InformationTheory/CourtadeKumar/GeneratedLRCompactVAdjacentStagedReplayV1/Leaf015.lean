import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf015Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((499 : ℚ) / 256) }
      headChoice := .n128 }

#kernel_checked_bool leaf015Check
  (leaf015Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRRLL)

def leaf015Checked : CheckedTree box_rLRRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf015Data leaf015Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
