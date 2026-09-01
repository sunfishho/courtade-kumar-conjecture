import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf032Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1003 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf032Check
  (leaf032Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRRRL)

def leaf032Checked : CheckedTree box_rRLRRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf032Data leaf032Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
