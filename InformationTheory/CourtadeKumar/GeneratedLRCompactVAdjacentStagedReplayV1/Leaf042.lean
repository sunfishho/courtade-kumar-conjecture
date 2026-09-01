import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf042Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((2015 : ℚ) / 1024) }
      headChoice := .n128 }

#kernel_checked_bool leaf042Check
  (leaf042Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRLRRRL)

def leaf042Checked : CheckedTree box_rRRLRRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf042Data leaf042Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
