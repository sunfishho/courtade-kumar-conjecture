import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf044Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1005 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf044Check
  (leaf044Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRLLL)

def leaf044Checked : CheckedTree box_rRRRLLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf044Data leaf044Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
