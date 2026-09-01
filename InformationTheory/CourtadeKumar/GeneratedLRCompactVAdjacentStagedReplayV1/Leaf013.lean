import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf013Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((999 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf013Check
  (leaf013Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLRRL)

def leaf013Checked : CheckedTree box_rLRLRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf013Data leaf013Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
