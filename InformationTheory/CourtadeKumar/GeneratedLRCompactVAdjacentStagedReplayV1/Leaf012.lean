import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf012Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((125 : ℚ) / 64) }
      headChoice := .n128 }

#kernel_checked_bool leaf012Check
  (leaf012Data.check logTerms pZeroTerms wTerms dTerms directN box_rLRLRLR)

def leaf012Checked : CheckedTree box_rLRLRLR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf012Data leaf012Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
