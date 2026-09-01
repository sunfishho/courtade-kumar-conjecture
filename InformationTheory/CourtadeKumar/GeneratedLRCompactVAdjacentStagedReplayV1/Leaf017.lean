import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf017Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((125 : ℚ) / 64) }
      headChoice := .n192 }

#kernel_checked_bool leaf017Check
  (leaf017Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRRRL)

def leaf017Checked : CheckedTree box_rLRRRL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf017Data leaf017Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
