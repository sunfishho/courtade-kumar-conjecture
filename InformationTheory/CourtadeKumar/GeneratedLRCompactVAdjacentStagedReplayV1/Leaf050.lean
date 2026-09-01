import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf050Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((63 : ℚ) / 32) }
      headChoice := .n128 }

#kernel_checked_bool leaf050Check
  (leaf050Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRRLRR)

def leaf050Checked : CheckedTree box_rRRRRLRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf050Data leaf050Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
