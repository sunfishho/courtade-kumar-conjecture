import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf040Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((2015 : ℚ) / 1024) }
      headChoice := .n128 }

#kernel_checked_bool leaf040Check
  (leaf040Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRRLL)

def leaf040Checked : CheckedTree box_rRRLRRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf040Data leaf040Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
