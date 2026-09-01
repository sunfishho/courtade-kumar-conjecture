import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf018Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((125 : ℚ) / 64) }
      headChoice := .n128 }

#kernel_checked_bool leaf018Check
  (leaf018Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRRRR)

def leaf018Checked : CheckedTree box_rLRRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf018Data leaf018Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
